{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeFamilies #-}

-- | This module implements an optimization that tries to statically reuse
-- kernel-level allocations. The goal is to lower the static memory usage, which
-- might allow more programs to run using intra-group parallelism.
module Futhark.Optimise.ReuseAllocations (optimise) where

import Control.Exception
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Function ((&))
import Data.Map (Map, (!))
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import qualified Futhark.Analysis.Interference as Interference
import qualified Futhark.Analysis.LastUse as LastUse
import Futhark.Binder.Class
import Futhark.Construct
import Futhark.IR.KernelsMem
import qualified Futhark.Optimise.ReuseAllocations.GreedyColoring as GreedyColoring
import Futhark.Pass (Pass (..), PassM)
import qualified Futhark.Pass as Pass
import Futhark.Util (invertMap)

-- | A mapping from allocation names to their size and space.
type Allocs = Map VName (SubExp, Space)

getAllocsStm :: Stm KernelsMem -> Allocs
getAllocsStm (Let (Pattern [] [PatElem name _]) _ (Op (Alloc se sp))) =
  M.singleton name (se, sp)
getAllocsStm (Let _ _ (Op (Alloc _ _))) = error "impossible"
getAllocsStm (Let _ _ (If _ then_body else_body _)) =
  foldMap getAllocsStm (bodyStms then_body)
    <> foldMap getAllocsStm (bodyStms else_body)
getAllocsStm (Let _ _ (DoLoop _ _ _ body)) =
  foldMap getAllocsStm (bodyStms body)
getAllocsStm _ = mempty

getAllocsSegOp :: SegOp lvl KernelsMem -> Allocs
getAllocsSegOp (SegMap _ _ _ body) =
  foldMap getAllocsStm (kernelBodyStms body)
getAllocsSegOp (SegRed _ _ _ _ body) =
  foldMap getAllocsStm (kernelBodyStms body)
getAllocsSegOp (SegScan _ _ _ _ body) =
  foldMap getAllocsStm (kernelBodyStms body)
getAllocsSegOp (SegHist _ _ _ _ body) =
  foldMap getAllocsStm (kernelBodyStms body)

setAllocsStm :: Map VName SubExp -> Stm KernelsMem -> Stm KernelsMem
setAllocsStm m stm@(Let (Pattern [] [PatElem name _]) _ (Op (Alloc _ _)))
  | Just s <- M.lookup name m =
    stm {stmExp = BasicOp $ SubExp s}
setAllocsStm _ stm@(Let _ _ (Op (Alloc _ _))) = stm
setAllocsStm m stm@(Let _ _ (Op (Inner (SegOp segop)))) =
  stm {stmExp = Op $ Inner $ SegOp $ setAllocsSegOp m segop}
setAllocsStm m stm@(Let _ _ (If cse then_body else_body dec)) =
  stm
    { stmExp =
        If
          cse
          (then_body {bodyStms = setAllocsStm m <$> bodyStms then_body})
          (else_body {bodyStms = setAllocsStm m <$> bodyStms else_body})
          dec
    }
setAllocsStm m stm@(Let _ _ (DoLoop ctx vals form body)) =
  stm
    { stmExp =
        DoLoop
          ctx
          vals
          form
          (body {bodyStms = setAllocsStm m <$> bodyStms body})
    }
setAllocsStm _ stm = stm

setAllocsSegOp ::
  Map VName SubExp ->
  SegOp lvl KernelsMem ->
  SegOp lvl KernelsMem
setAllocsSegOp m (SegMap lvl sp tps body) =
  SegMap lvl sp tps $
    body {kernelBodyStms = setAllocsStm m <$> kernelBodyStms body}
setAllocsSegOp m (SegRed lvl sp segbinops tps body) =
  SegRed lvl sp segbinops tps $
    body {kernelBodyStms = setAllocsStm m <$> kernelBodyStms body}
setAllocsSegOp m (SegScan lvl sp segbinops tps body) =
  SegScan lvl sp segbinops tps $
    body {kernelBodyStms = setAllocsStm m <$> kernelBodyStms body}
setAllocsSegOp m (SegHist lvl sp segbinops tps body) =
  SegHist lvl sp segbinops tps $
    body {kernelBodyStms = setAllocsStm m <$> kernelBodyStms body}

maxSubExp :: MonadBinder m => Set SubExp -> m SubExp
maxSubExp = helper . S.toList
  where
    helper (s1 : s2 : sexps) = do
      z <- letSubExp "maxSubHelper" $ BasicOp $ BinOp (UMax Int64) s1 s2
      helper (z : sexps)
    helper [s] =
      return s
    helper [] = error "impossible"

definedInExp :: Exp KernelsMem -> Set VName
definedInExp (Op (Inner (SegOp segop))) =
  definedInSegOp segop
definedInExp (If _ then_body else_body _) =
  foldMap definedInStm (bodyStms then_body)
    <> foldMap definedInStm (bodyStms else_body)
definedInExp (DoLoop _ _ _ body) =
  foldMap definedInStm $ bodyStms body
definedInExp _ = mempty

definedInStm :: Stm KernelsMem -> Set VName
definedInStm Let {stmPattern = Pattern ctx vals, stmExp} =
  let definedInside =
        ctx <> vals
          & fmap patElemName
          & S.fromList
   in definedInExp stmExp <> definedInside

definedInSegOp :: SegOp lvl KernelsMem -> Set VName
definedInSegOp (SegMap _ _ _ body) =
  foldMap definedInStm $ kernelBodyStms body
definedInSegOp (SegRed _ _ _ _ body) =
  foldMap definedInStm $ kernelBodyStms body
definedInSegOp (SegScan _ _ _ _ body) =
  foldMap definedInStm $ kernelBodyStms body
definedInSegOp (SegHist _ _ _ _ body) =
  foldMap definedInStm $ kernelBodyStms body

isKernelInvariant :: SegOp lvl KernelsMem -> (SubExp, space) -> Bool
isKernelInvariant segop (Var vname, _) =
  not $ vname `S.member` definedInSegOp segop
isKernelInvariant _ _ = True

onKernelBodyStms ::
  MonadBinder m =>
  SegOp lvl KernelsMem ->
  (Stms KernelsMem -> m (Stms KernelsMem)) ->
  m (SegOp lvl KernelsMem)
onKernelBodyStms (SegMap lvl space ts body) f = do
  stms <- f $ kernelBodyStms body
  return $ SegMap lvl space ts $ body {kernelBodyStms = stms}
onKernelBodyStms (SegRed lvl space binops ts body) f = do
  stms <- f $ kernelBodyStms body
  return $ SegRed lvl space binops ts $ body {kernelBodyStms = stms}
onKernelBodyStms (SegScan lvl space binops ts body) f = do
  stms <- f $ kernelBodyStms body
  return $ SegScan lvl space binops ts $ body {kernelBodyStms = stms}
onKernelBodyStms (SegHist lvl space binops ts body) f = do
  stms <- f $ kernelBodyStms body
  return $ SegHist lvl space binops ts $ body {kernelBodyStms = stms}

-- | This is the actual optimiser. Given an interference graph and a `SegOp`,
-- replace allocations and references to memory blocks inside with a (hopefully)
-- reduced number of allocations.
optimiseKernel ::
  (MonadBinder m, Lore m ~ KernelsMem) =>
  Interference.Graph VName ->
  SegOp lvl KernelsMem ->
  m (SegOp lvl KernelsMem)
optimiseKernel graph segop0 = do
  segop <- onKernelBodyStms segop0 $ onKernels $ optimiseKernel graph
  let allocs = M.filter (isKernelInvariant segop) $ getAllocsSegOp segop
      (colorspaces, coloring) =
        GreedyColoring.colorGraph
          (fmap snd allocs)
          graph
  (maxes, maxstms) <-
    invertMap coloring
      & M.elems
      & mapM (maxSubExp . S.map (fst . (allocs !)))
      & collectStms
  (colors, stms) <-
    assert (length maxes == M.size colorspaces) maxes
      & zip [0 ..]
      & mapM (\(i, x) -> letSubExp "color" $ Op $ Alloc x $ colorspaces ! i)
      & collectStms
  let segop' = setAllocsSegOp (fmap (colors !!) coloring) segop
  return $ case segop' of
    SegMap lvl sp tps body ->
      SegMap lvl sp tps $
        body {kernelBodyStms = maxstms <> stms <> kernelBodyStms body}
    SegRed lvl sp binops tps body ->
      SegRed lvl sp binops tps $
        body {kernelBodyStms = maxstms <> stms <> kernelBodyStms body}
    SegScan lvl sp binops tps body ->
      SegScan lvl sp binops tps $
        body {kernelBodyStms = maxstms <> stms <> kernelBodyStms body}
    SegHist lvl sp binops tps body ->
      SegHist lvl sp binops tps $
        body {kernelBodyStms = maxstms <> stms <> kernelBodyStms body}

-- | Helper function that modifies kernels found inside some statements.
onKernels ::
  LocalScope KernelsMem m =>
  (SegOp SegLevel KernelsMem -> m (SegOp SegLevel KernelsMem)) ->
  Stms KernelsMem ->
  m (Stms KernelsMem)
onKernels f =
  mapM helper
  where
    helper stm@Let {stmExp = Op (Inner (SegOp segop))} =
      inScopeOf stm $ do
        exp' <- f segop
        return $ stm {stmExp = Op $ Inner $ SegOp exp'}
    helper stm@Let {stmExp = If c then_body else_body dec} =
      inScopeOf stm $ do
        then_body_stms <- f `onKernels` bodyStms then_body
        else_body_stms <- f `onKernels` bodyStms else_body
        return $
          stm
            { stmExp =
                If
                  c
                  (then_body {bodyStms = then_body_stms})
                  (else_body {bodyStms = else_body_stms})
                  dec
            }
    helper stm@Let {stmExp = DoLoop ctx vals form body} =
      inScopeOf stm $ do
        stms <- f `onKernels` bodyStms body
        return $ stm {stmExp = DoLoop ctx vals form (body {bodyStms = stms})}
    helper stm =
      inScopeOf stm $ return stm

-- | Perform the reuse-allocations optimization.
optimise :: Pass KernelsMem KernelsMem
optimise =
  Pass "reuse allocations" "reuse allocations" $ \prog ->
    let (lumap, _) = LastUse.analyseProg prog
        graph =
          foldMap
            ( \f ->
                runReader
                  ( Interference.analyseKernels lumap $
                      bodyStms $ funDefBody f
                  )
                  $ scopeOf f
            )
            $ progFuns prog
     in Pass.intraproceduralTransformation (onStms graph) prog
  where
    onStms ::
      Interference.Graph VName ->
      Scope KernelsMem ->
      Stms KernelsMem ->
      PassM (Stms KernelsMem)
    onStms graph scope stms = do
      let m = localScope scope $ optimiseKernel graph `onKernels` stms
      fmap fst $ modifyNameSource $ runState (runBinderT m mempty)