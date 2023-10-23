module Futhark.Optimise.IntraSeq (intraSeq) where

import Language.Futhark.Core
import Futhark.Pass
import Futhark.IR.GPU
import Futhark.Builder.Class
import Futhark.Construct

import Control.Monad.Reader
import Control.Monad.State
import Futhark.Transform.Rename
import Debug.Pretty.Simple
import Data.Map.Lazy as M




type SeqM a = ReaderT (Scope GPU) (State VNameSource) a


data Env = Env {
  grpId      :: SubExp,    -- The group id
  grpSize    :: SubExp,    -- The group size after seq
  grpsizeOld :: SubExp,    -- The group size before seq
  seqFactor  :: SubExp
}

nameOf :: SubExp -> VName
nameOf (Var name) = name
nameOf _ = error "Tried to get name of constant"

-- seqFactor :: SubExp
-- seqFactor = intConst Int64 4


-- NOTE uncomment this for pretty printing AST
-- intraSeq :: Pass GPU GPU
  -- intraSeq = Pass "test" "desc" printAst
  -- printAst :: Prog GPU -> PassM (Prog GPU)
-- printAst prog = pTrace (show prog) (pure prog)

intraSeq :: Pass GPU GPU
intraSeq =
    Pass {
      passName = "Sequentialisation",
      passDescription = "Performs intra group sequentialisation",
      passFunction = intraproceduralTransformation onStms
    }
    where
      onStms scope stms =
        modifyNameSource $
          runState $
            runReaderT (seqStms stms) scope



-- | This function is expected to match statements of the "group" level. That is
-- SegOps at group level and potentially intermediate statements between
-- multiple SegOps
seqStms ::
  Stms GPU ->
  SeqM (Stms GPU)
seqStms stms = do
  foldM (\ss s -> do
    ss' <- runBuilder_ $ localScope (scopeOf s) $ seqStm s
    pure $ ss <> ss'
    ) mempty (stmsToList stms)


-- | Expected to match at group level
seqStm ::
  Stm GPU ->
  Builder GPU ()

seqStm (Let pat aux (Op (SegOp (SegMap lvl@(SegGroup {}) space ts kbody)))) = do
  -- TODO: determine what the seqFactor should be
  let e = intConst Int64 4
  let grpId = fst $ head $ unSegSpace space

  -- Compute the new group size
  let sizeOld = snd $ head $ unSegSpace space
  sizeNew <- letSubExp "group_size" =<< eBinOp (SDivUp Int64 Unsafe) 
                                            (eSubExp sizeOld) 
                                            (eSubExp e)

  let env = Env (Var grpId) sizeNew sizeOld e

  -- At this point all arrays in scope must be global. Create a tile for each
  -- and let later optimisation passes clean up the mess
  tiles <- mkTiles env
  
  kernelRes <- seqKernelBody tiles kbody

  -- Remember not to lose the original pattern and result
  exp' <- eSubExp kernelRes
  addStm $ Let pat aux exp'
  
  pure ()

-- The catch all
seqStm stm = addStm stm





seqKernelBody ::
  [(VName, VName)] ->
  KernelBody GPU ->
  Builder GPU SubExp
seqKernelBody tiles (KernelBody dex stms result) = do undefined









-- | Creates a tile for each array in scope at the time of caling it.
-- That is if called at the correct time it will create a tile for each
-- global array
mkTiles ::
  Env -> 
  Builder GPU [(VName, VName)]
mkTiles env = do
  scope <- askScope
  let arraysInScope = M.toList $  M.filter isArray scope

  forM arraysInScope $ \ (arrName, arrInfo) -> do

    let tp = elemType $ typeOf arrInfo 
    -- Read coalesced
    tile <- buildSegMap_ "tile" $ do
      tid <- newVName "tid"
      phys <- newVName "phys_tid"
      es <- letSubExp "elems" $ BasicOp $ Index arrName
                  (Slice [DimFix $ grpId env, 
                         DimSlice (Var tid) (seqFactor env) (grpSize env)])
      let lvl = SegThread SegNoVirt Nothing
      let space = SegSpace phys [(tid, grpSize env)] 
      let types = [Array tp (Shape [seqFactor env]) NoUniqueness]
      pure ([Returns ResultMaySimplify mempty es], lvl, space, types)
    
    -- transpose and flatten
    tileT <- letExp "tileT" $ BasicOp $ Rearrange [1,0] tile 
    tileFlat <- letExp "tile_flat" $ BasicOp $ Reshape 
                ReshapeArbitrary (Shape [grpsizeOld env]) tileT

    -- Read the pr. thread chunk into registers
    tile' <- buildSegMap_ "tile" $ do
      tid <- newVName "tid"
      phys <- newVName "phys_tid"
      start <- letSubExp "start" =<< eBinOp (Mul Int64 OverflowUndef)
                                            (eSubExp $ Var tid)
                                            (eSubExp $ seqFactor env)
      es <- letSubExp "chunk" $ BasicOp $ Index tileFlat
            (Slice [DimFix $ grpId env,
                    DimSlice start (seqFactor env) (intConst Int64 1)])
      let lvl = SegThread SegNoVirt Nothing
      let space = SegSpace phys [(tid, grpSize env)]
      let types = [Array tp (Shape [seqFactor env]) NoUniqueness]
      pure ([Returns ResultPrivate mempty es], lvl, space, types)

    -- return the original arr name with the name of its local tile
    pure (arrName, tile') 
    
  where
    isArray :: NameInfo GPU -> Bool
    isArray info = arrayRank (typeOf info) > 0



-- Monad stuff below here


buildSegMap ::
  String ->
  Builder GPU ([KernelResult], SegLevel, SegSpace, [Type]) ->
  Builder GPU SubExp
buildSegMap name m = do
  ((results, lvl, space, ts), stms) <- collectStms m
  let kbody = KernelBody mempty stms results
  letSubExp name $ Op $ SegOp $ SegMap lvl space ts kbody

buildSegMap_ ::
  String ->
  Builder GPU ([KernelResult], SegLevel, SegSpace, [Type]) ->
  Builder GPU VName
buildSegMap_ name m = do
  res <- buildSegMap name m
  let (Var vname) = res
  pure vname