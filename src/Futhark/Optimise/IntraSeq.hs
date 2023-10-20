{-=# OPTIONS_GHC -Wno-unused-local-binds #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use join" #-}
{-# HLINT ignore "Use list comprehension" #-}
{-# HLINT ignore "Use null" #-}
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
import Data.List ( elemIndex )

type SeqM = ReaderT (Scope GPU) (State VNameSource)
-- Name, type of array, num of dimensions
data ArrInfo = ArrInfo { name :: VName, pType :: PrimType, dim :: Int }
-- from: original array name, to: tile name
data TileNameMappings = TileNameMappings { fromNames :: [VName], tileNames :: [VName] }
seqFactor :: SubExp
seqFactor = intConst Int64 4
-- we divide kernelbody stms of a soac into 3 categories:
-- read statements that should be read into a tile
-- statements used in the given SOAC binops
-- statements not used in the SOAC lambda body, but have been fused into the kernel body
-- data KBodyStms = KBodyStms { toTile :: [Stm GPU], usedInBinops :: [Stm GPU], fused :: [Stm GPU]}

-- NOTE uncomment this for pretty printing AST
-- intraSeq :: Pass GPU GPU
  -- intraSeq = Pass "test" "desc" printAst
  -- printAst :: Prog GPU -> PassM (Prog GPU)
-- printAst prog = pTrace (show prog) (pure prog)

intraSeq :: Pass GPU GPU
intraSeq =
    Pass "name" "description" $
      intraproceduralTransformation onStms
    where
      onStms scope stms =
        modifyNameSource $
          runState $
            runReaderT (seqStms stms) scope




-- SeqStms is only to be used for top level statements. To sequentialize
-- statements within a body use seqStms'
seqStms :: Stms GPU -> SeqM (Stms GPU)
seqStms stms =
  localScope (scopeOf stms) $
    mconcat <$> mapM seqStm (stmsToList stms)





-- Like seqStms, segStm is only for top level statements
seqStm :: Stm GPU -> SeqM (Stms GPU)
seqStm (Let pat aux (Op (SegOp (
            SegMap lvl@(SegGroup virt (Just grid)) space ts kbody)))) = do
  -- Create the new group size
  let grpSizeOld = unCount $ gridGroupSize grid
  (groupSize, groupStms) <- runBuilder $ bindNewGroupSize grpSizeOld
  let grid' = Just $  KernelGrid (gridNumGroups grid) (Count groupSize)

  -- Get the group id (gtid)
  -- TODO: Assumes only a single space
  let [(gtid, _)] = unSegSpace space

  kbody' <- seqBody (Var gtid) (grpSizeOld, groupSize) kbody
  pure $ groupStms <>
     oneStm (Let pat aux (Op (SegOp (SegMap (SegGroup virt grid') space ts kbody'))))

seqStm stm = error $ "Expected a SegMap at Group level but got " ++ show stm




-- First SubExp is the group id (gtid)
-- Second SubExp is the gruup size
seqBody ::
  SubExp ->                 -- Group ID
  (SubExp, SubExp) ->       -- (old size, new size)
  KernelBody GPU ->
  SeqM (KernelBody GPU)
seqBody grpId sizes (KernelBody dec stms result) = do
  stms' <- localScope (scopeOf stms) $ runBuilder_ $ seqStms' grpId sizes stms
  pure $ KernelBody dec stms' result




-- Much the same as seqStms but takes the group size to pass along
seqStms' ::
  SubExp ->             -- Group id
  (SubExp, SubExp)->    -- (old size, new size)
  Stms GPU ->
  Builder GPU ()
seqStms' grpId sizes stms = do
  mapM_ (seqStm' grpId sizes) $ stmsToList stms

-- seqStm' is assumed to only match on statements encountered within some
-- SegOp at group level
seqStm' ::
  SubExp ->             -- Group id
  (SubExp, SubExp) ->   -- (old size, new size)
  Stm GPU ->
  Builder GPU ()
seqStm' gid sizes stm@(Let pat aux (Op (SegOp
          (SegRed lvl@(SegThread {}) space binops ts kbody)))) = do
  -- Get the thread id
  let [(tid, _)] = unSegSpace space

  -- creates tiles for the arrays read. Parnames : names to set parameters to in screma
  (nameMappings, kbodyNotTiled, parNames) <- tileSegKernelBody kbody sizes gid (Var tid)

  -- For each BinOp extract the lambda and create a SegMap performing thread local reduction
  -- TODO: have to update the arguments from the kernelBody to the specific binOp (can you put the binops in the same screma and avoid this??)
  -- TODO: THIS IS IMPORTANT ELSE MULTIPLE BINOPS WON'T WORK, head is temporary fix
  redNames <- mapM (mkSegMapRed nameMappings sizes kbodyNotTiled parNames) binops

  -- -- Update the kbody to use the tile
  let phys = segFlat space
  let [(gtid, _)] = unSegSpace space
  let space' = SegSpace phys [(gtid, snd sizes)]

  -- -- Each VName in fparams should be paired with the corresponding tile
  -- -- created for the array of that VName
  -- TODO: Head in redNames is temp fix until multiple binops are supported
  let kbody' = substituteIndexes kbody $ zip (fromNames nameMappings) $ head redNames
  addStm $ Let pat aux (Op (SegOp (SegRed lvl space' binops ts kbody')))

seqStm' _ _ _ = undefined


substituteIndexes :: KernelBody GPU -> [(VName, VName)] -> KernelBody GPU
substituteIndexes (KernelBody dec stms results) names =
  let stms' = stmsFromList $ map (substituteIndex names) $ stmsToList stms
  in KernelBody dec stms' results

substituteIndex :: [(VName, VName)] -> Stm GPU -> Stm GPU
substituteIndex names stm@(Let pat aux (BasicOp (Index name slice))) =
  let (fromNames, toNames) = unzip names
      index = elemIndex name fromNames
      in case index of
        Just i ->
          -- after tiling we only need the last index
          let slice' = last $ unSlice slice
          in Let pat aux (BasicOp (Index (toNames !! i) $ Slice [slice']))
        Nothing -> stm
substituteIndex _ stm = stm

bindNewGroupSize :: SubExp -> Builder GPU SubExp
bindNewGroupSize group_size = do
  name <- newVName "group_size"
  letBindNames [name] $ BasicOp $ BinOp (SDivUp Int64 Unsafe) group_size seqFactor
  pure $ Var name

mkSegMapRed ::
  TileNameMappings ->                  -- The arrays to reduce over
  (SubExp, SubExp) ->                 -- (old size, new size)
  Maybe (Body GPU) ->
  [VName] ->
  SegBinOp GPU ->
  Builder GPU [VName]
mkSegMapRed names grpSizes body parNames binop = do
  let comm = segBinOpComm binop
  lambda <- renameLambda $ segBinOpLambda binop
  let neutral = segBinOpNeutral binop

  let reduce = Reduce comm lambda neutral

  buildSegMapThread_ "red_intermediate" $ do
      tid <- newVName "tid"
      phys <- newVName "phys_tid"
      currentSize <- mkChunkSize tid $ fst grpSizes
      es <- mapM (letChunkExp currentSize tid) (tileNames names)
      screma <- case body of
        Just k -> buildRedoMapFromKBody [reduce] k
        Nothing -> reduceSOAC [reduce]
      tmp <- letTupExp' "tmp" $ Op $ OtherOp $ Screma currentSize es screma
      let lvl = SegThread SegNoVirt Nothing
      let space = SegSpace phys [(tid, snd grpSizes)]
      let types = scremaType seqFactor screma
      -- make list map over and create kernelBodyResult
      let kRes = map (Returns ResultMaySimplify mempty) tmp
      pure (kRes, lvl, space, types)
  where
    -- build the screma form the redomap
    -- needs the reduce SOACs, kernelbody to transform to lambda body
    -- and the VNames of the chunk(s) the redomap iterates over
    buildRedoMapFromKBody ::  [Reduce GPU] -> Body GPU -> Builder GPU (ScremaForm GPU)
    buildRedoMapFromKBody reds body' = do
      let pars = zip parNames ts
      let params = map (\(n, t) -> Param mempty n t) pars
      let lamb = Lambda
                { lambdaParams = params,
                  lambdaBody = body',
                  lambdaReturnType = ts
                }
      pTrace (show $ lamb) (pure $ redomapSOAC reds lamb)
      where
        ts = concatMap (lambdaReturnType . redLambda) reds

    letChunkExp :: SubExp -> VName -> VName -> Builder GPU VName
    letChunkExp size tid arrName = do
      letExp "chunk" $ BasicOp $
        Index arrName (Slice [DimFix (Var tid),
        DimSlice (intConst Int64 0) size (intConst Int64 1)])

bodyFromKBody :: KernelBody GPU -> Body GPU
bodyFromKBody (KernelBody dec stms res) =
  let res' = map (subExpRes . kernelResultSubExp) res
  in Body
    { bodyDec = dec,
      bodyStms = stms,
      bodyResult = res'
    }
-- | The making of a tile consists of a SegMap to load elements into local
-- memory in a coalesced manner. Some intermediate instructions to modify
-- the tile. Lastly another SegMap to load the correct values into registers
-- 
-- The first SubExp is the group id 
-- The second SubExp is Var containing the groupsize
-- Returns a SubExp that is the chunks variable
mkTile :: SubExp -> (SubExp, SubExp) -> ArrInfo -> Builder GPU SubExp
mkTile gid (oldSize, newSize) arrInfo = do
  segMap <- buildSegMapThread_ "tile" $ do
      tid <- newVName "tid"
      phys <- newVName "phys_tid"
      let innerDim = if dim arrInfo == 2 then [DimFix gid] else []
      let slice' = innerDim ++ [DimSlice (Var tid) seqFactor newSize]
      e <- letSubExp "slice" $ BasicOp $
                Index (name arrInfo) (Slice slice')
      let lvl = SegThread SegNoVirt Nothing
      let space = SegSpace phys [(tid, newSize)]
      let types = [Array (pType arrInfo) (Shape [seqFactor]) NoUniqueness]
      pure ([Returns ResultMaySimplify mempty e], lvl, space, types)

  -- TODO: refactor head statement below
  -- tile segmaps should always produce a single vName result
  -- make function like buildSegMapThread but produces a single result?
  tileTrans <- letExp "tile_T" $ BasicOp $ Rearrange [1,0] $ head segMap
  tileFlat <- letExp "tile_flat" $ BasicOp $
                Reshape ReshapeArbitrary (Shape [oldSize]) tileTrans

  -- SegMap to read the actual chunks the threads need
  -- TODO: HEAD SAME AS ABOVE
  res <- buildSegMapThread "chunks" $ do
    tid <- newVName "tid"
    phys <- newVName "phys_tid"
    start <- letSubExp "start" $ BasicOp $
              BinOp (Mul Int64 OverflowUndef) (Var tid) seqFactor
    chunk <- letSubExp "chunk" $ BasicOp $
              Index tileFlat (Slice [DimSlice start seqFactor (intConst Int64 1)])
    let lvl = SegThread SegNoVirt Nothing
    let space = SegSpace phys [(tid, newSize)]
    let types = [Array (pType arrInfo) (Shape [seqFactor]) NoUniqueness]
    pure ([Returns ResultPrivate mempty chunk], lvl, space, types)
  pure $ head res

-- Generates statements that compute the pr. thread chunk size. This is needed
-- as the last thread in a block might not have seqFactor amount of elements
-- to read. 
mkChunkSize ::
  VName ->               -- The thread id
  SubExp ->              -- old size 
  Builder GPU SubExp     -- Returns the SubExp in which the size is
mkChunkSize tid sOld = do
  offset <- letSubExp "offset" $ BasicOp $
              BinOp (Mul Int64 OverflowUndef) (Var tid) seqFactor
  tmp <- letSubExp "tmp" $ BasicOp $
              BinOp (Sub Int64 OverflowUndef) sOld offset
  letSubExp "size" $ BasicOp $
              BinOp (SMin Int64) tmp seqFactor


-- Builds a SegMap at thread level containing all bindings created in m
-- and returns the subExp which is the variable containing the result
buildSegMapThread ::
  String ->
  Builder GPU ([KernelResult], SegLevel, SegSpace, [Type]) ->
  Builder GPU [SubExp]
buildSegMapThread name m = do
  ((res, lvl, space, ts), stms) <- collectStms m
  let kbody = KernelBody () stms res
  letTupExp' name $ Op $ SegOp $ SegMap lvl space ts kbody

-- Like buildSegMapThread but returns the VName instead of the actual 
-- SubExp. Just for convenience
buildSegMapThread_ ::
  String ->
  Builder GPU ([KernelResult], SegLevel, SegSpace, [Type]) ->
  Builder GPU [VName]
buildSegMapThread_ name m = do
  subExps <- buildSegMapThread name m
  pure $ map varFromExp subExps
  where
    varFromExp :: SubExp -> VName
    varFromExp (Var nm) = nm
    varFromExp e = error $ "Expected SubExp of type Var, but got:\n" ++ show e

-- create tiles for the arrays used in the segop kernelbody
-- returns a list of tuples of the name of the array and its tiled replacement
-- and if any stms were not tiled, the kernelbody with those 
tileSegKernelBody :: KernelBody GPU -> (SubExp, SubExp) -> SubExp -> SubExp
                      -> Builder GPU (TileNameMappings, Maybe (Body GPU), [VName])
tileSegKernelBody kb@(KernelBody dec stms res) grpSizes gid tid = do
  -- let stmsToTile = filter shouldTele $ stmsToList stms
  -- TODO refactor so not use shouldTile here
  let (stmsToTile, _) = foldr shouldTile ([],[]) $ stmsToList stms
  let stmsInfos = map getTileStmInfo stmsToTile
  tiles <- mapM (mkTile gid grpSizes) stmsInfos
  let names = map name stmsInfos
  let tileNames = map (\(Var t) -> t) tiles

  -- we need to rename the stms for when we put the body inside of the screma
  -- return list of the stmsToTile names of the renamed
  -- we must then use those names as the arguments in the redomap
  (Body dec' stms' res') <- renameBody $ bodyFromKBody kb
  let (tiledStms, stmsNotTiled) = foldr shouldTile ([], []) $ stmsToList stms'
  let tiledStmsNames = map getStmSingleName tiledStms
  let body = if length stmsNotTiled /= 0
              then Just $ Body dec' (stmsFromList stmsNotTiled) res'
              else Nothing
  pure (TileNameMappings names tileNames, body, tiledStmsNames)
  where
    -- divides stms into those that should be tiled and those that should not
    -- arrays to tile use the thread id and haven't been tiled in same kernelbody
    shouldTile :: Stm GPU -> ([Stm GPU], [Stm GPU]) -> ([Stm GPU], [Stm GPU])
    shouldTile stm@(Let _ _ (BasicOp (Index _ slice))) (toTile, dontTile) =
      let tidIndex = DimFix tid
      in case unSlice slice of
        (_:tid':_) -> updateAcc $ tid' == tidIndex && notTiled
        (tid':_) -> updateAcc $ tid' == tidIndex && notTiled
        _ -> updateAcc False
      where
        notTiled = stm `notElem` toTile
        updateAcc :: Bool -> ([Stm GPU], [Stm GPU])
        updateAcc b = if b then (stm:toTile, dontTile) else (toTile, stm:dontTile)
    shouldTile stm (toTile, dontTile) = (toTile, stm:dontTile)
      
    getStmSingleName :: Stm GPU -> VName
    getStmSingleName stm@(Let pat _ _) = 
      case patElems pat of 
      [pe] -> patElemName pe
      _ -> error $ "Expected a let binding for a single VName:\n" ++ show stm 

    getTileStmInfo :: Stm GPU -> ArrInfo
    getTileStmInfo stm@(Let pat _ (BasicOp (Index name slice))) =
      let dim = length $ unSlice slice
          pes = patElems pat
      in case pes of
        [PatElem _ dec'] -> ArrInfo name (elemType dec') dim
        _ -> error
              $ "Statements used for tiling should only contain a single VName:\n"
                ++ show stm
    getTileStmInfo stm =
      error
        $ "Invalid statement for tiling in IntraSeq " ++ show stm

-- analyseSoacKBodyStms :: KernelBody GPU -> [SegBinOp GPU] -> KBodyStms
-- analyseSoacKBodyStms kbody binops = 
--   let arity = foldl (+) $ map getArity binops

--   in undefined
--   -- length segBinOpNeutral, segbinoplambda -> length lambdaParams
--   where
--     getArity :: SegBinOp GPU -> Int
--     getArity (SegBinOp _ lamb neut _) = 
--       length lamb + length (lambdaParams lamb)

