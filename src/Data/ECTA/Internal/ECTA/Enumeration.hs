{-# LANGUAGE OverloadedStrings #-}

{- | Nondeterministic enumeration for ECTAs.

Enumeration builds 'TermFragment's before expanding them to concrete @Term@s.
Equality constraints are represented by suspended path-trie obligations that
point at UVars. When enumeration descends through an edge, those obligations
descend with it; when an obligation reaches the current node, the corresponding
UVars are merged so future choices stay consistent.

Most callers should use 'getAllTerms' or 'getAllTermsPrune'. The lower-level
state operations are exposed for pruning oracles and downstream tools that need
to inspect or steer enumeration.
-}
module Data.ECTA.Internal.ECTA.Enumeration (
    TermFragment (..),
    termFragToTruncatedTerm,
    SuspendedConstraint (..),
    scGetPathTrie,
    scGetUVar,
    descendScs,
    UVarValue (..),
    EnumerationState (..),
    uvarCounter,
    uvarRepresentative,
    uvarValues,
    pruneDeps,
    initEnumerationState,
    EnumerateM,
    TermSearch,
    TermSearchStep (..),
    TermBranch,
    BranchInfo (..),
    startTermSearch,
    stepTermSearch,
    termBranchInfo,
    followTermBranch,
    SampleLimits (..),
    defaultSampleLimits,
    SampleError (..),
    sampleTermSearch,
    sampleTermSearchByCount,
    sampleTerm,
    getUVarRepresentative,
    assimilateUvarVal,
    mergeNodeIntoUVarVal,
    getUVarValue,
    getTermFragForUVar,
    runEnumerateM,
    getPruneDepsOf,
    getPruneDeps,
    addPruneDep,
    deletePruneDep,
    fragRepresents,
    enumerateNode,
    enumerateEdge,
    ExpandableUVarResult (..),
    firstExpandableUVar,
    enumerateOutUVar,
    enumerateOutFirstExpandableUVar,
    enumerateFully,
    expandTermFrag,
    expandPartialTermFrag,
    expandUVar,
    getAllTruncatedTerms,
    getAllTerms,
    getAllTermsPrune,
    enumPrune,
) where

import Control.Applicative (Alternative (..))
import Control.Monad (MonadPlus (..), ap, filterM, forM_, guard, void, zipWithM)
import Control.Monad.State.Strict (StateT (..), gets, modify')
import qualified Control.Monad.State.Strict as State
import Control.Monad.Trans.Class (lift)
import qualified Data.IntMap as IntMap
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe (fromMaybe)
import Data.Semigroup (Max (..))
import Data.Sequence (Seq ((:<|), (:|>)))
import qualified Data.Sequence as Sequence

import Data.ECTA.Internal.ECTA.Operations
import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Paths
import Data.ECTA.Term
import qualified Data.IntSet as IntSet
import Data.Persistent.UnionFind (UVar, UVarGen, UnionFind, intToUVar, uvarToInt)
import qualified Data.Persistent.UnionFind as UnionFind
import Data.Text.Extended.Pretty

-------------------------------------------------------------------------------

---------------------------------------------------------------------------
------------------------------- Term fragments ----------------------------
---------------------------------------------------------------------------

-- | Partially enumerated term with holes for nodes that still need expansion.
data TermFragment
    = -- | Concrete symbol with already-created child fragments.
      TermFragmentNode !Symbol ![TermFragment]
    | -- | Hole whose value is tracked in the enumeration state.
      TermFragmentUVar UVar
    deriving (Eq, Ord, Show)

-- | Convert a fragment to a term, rendering holes as variable-like leaves.
termFragToTruncatedTerm :: TermFragment -> Term
termFragToTruncatedTerm (TermFragmentNode s ts) = Term s (map termFragToTruncatedTerm ts)
termFragToTruncatedTerm (TermFragmentUVar uv) = Term (Symbol $ "v" <> pretty (uvarToInt uv)) []

---------------------------------------------------------------------------
------------------------------ Search tree -------------------------------
---------------------------------------------------------------------------

-- | Lazy nondeterministic computation with explicit local choices.
data SearchTree a
    = SearchTreeDead
    | SearchTreeDone a
    | SearchTreeChoice (NonEmpty (SearchTreeBranch a))

-- | One labeled continuation in a search-tree choice.
data SearchTreeBranch a = SearchTreeBranch !(Maybe Symbol) !(SearchTree a)

instance Functor SearchTree where
    fmap _ SearchTreeDead = SearchTreeDead
    fmap f (SearchTreeDone x) = SearchTreeDone (f x)
    fmap f (SearchTreeChoice branches) = SearchTreeChoice (fmap mapBranch branches)
      where
        mapBranch (SearchTreeBranch label search) = SearchTreeBranch label (fmap f search)

instance Applicative SearchTree where
    pure = SearchTreeDone
    (<*>) = ap

instance Monad SearchTree where
    SearchTreeDead >>= _ = SearchTreeDead
    SearchTreeDone x >>= f = f x
    SearchTreeChoice branches >>= f = SearchTreeChoice (fmap bindBranch branches)
      where
        bindBranch (SearchTreeBranch label search) = SearchTreeBranch label (search >>= f)

instance MonadFail SearchTree where
    fail _ = SearchTreeDead

instance Alternative SearchTree where
    empty = SearchTreeDead
    SearchTreeDead <|> right = right
    left <|> SearchTreeDead = left
    left <|> right =
        SearchTreeChoice
            (SearchTreeBranch Nothing left :| [SearchTreeBranch Nothing right])

instance MonadPlus SearchTree where
    mzero = empty
    mplus = (<|>)

-- | Collect all search results in depth-first order.
searchTreeResults :: SearchTree a -> [a]
searchTreeResults SearchTreeDead = []
searchTreeResults (SearchTreeDone x) = [x]
searchTreeResults (SearchTreeChoice branches) =
    concatMap (\(SearchTreeBranch _ search) -> searchTreeResults search) branches

-- | Create an explicit search choice for multiple ECTA edges.
chooseEdges :: [Edge] -> EnumerateM Edge
chooseEdges [] = mzero
chooseEdges [edge] = pure edge
chooseEdges (edge : edges) = lift $ SearchTreeChoice (toBranch edge :| map toBranch edges)
  where
    toBranch e = SearchTreeBranch (Just (edgeSymbol e)) (SearchTreeDone e)

---------------------------------------------------------------------------
------------------------------ Enumeration state --------------------------
---------------------------------------------------------------------------

lens :: (Functor f) => (s -> a) -> (s -> a -> s) -> (a -> f a) -> s -> f s
lens getter setter f s = setter s <$> f (getter s)

-----------------------
------- Suspended constraints
-----------------------

-- | Equality obligation that has not yet reached the node it constrains.
data SuspendedConstraint = SuspendedConstraint !PathTrie !UVar
    deriving (Eq, Ord, Show)

-- | Remaining paths for a suspended equality obligation.
scGetPathTrie :: SuspendedConstraint -> PathTrie
scGetPathTrie (SuspendedConstraint pt _) = pt

-- | UVar that must be merged when the suspended obligation is reached.
scGetUVar :: SuspendedConstraint -> UVar
scGetUVar (SuspendedConstraint _ uv) = uv

-- | Push suspended obligations through child index @i@ and drop empty paths.
descendScs :: Int -> Seq SuspendedConstraint -> Seq SuspendedConstraint
descendScs i scs =
    Sequence.filter (not . isEmptyPathTrie . scGetPathTrie) $
        fmap
            (\(SuspendedConstraint pt uv) -> SuspendedConstraint (pathTrieDescend pt i) uv)
            scs

-----------------------
------- UVarValue
-----------------------

-- | Enumeration status for one UVar.
data UVarValue
    = UVarUnenumerated
        { contents :: !(Maybe Node)
        -- ^ ECTA node still to enumerate, or 'Nothing' for pure constraint variables.
        , constraints :: !(Seq SuspendedConstraint)
        -- ^ Constraints that should be carried while enumerating this value.
        }
    | -- | UVar has been expanded to a fragment.
      UVarEnumerated {termFragment :: !TermFragment}
    | -- | UVar was merged into another representative and should no longer be used.
      UVarEliminated
    deriving (Eq, Ord, Show)

intersectUVarValue :: UVarValue -> UVarValue -> UVarValue
intersectUVarValue (UVarUnenumerated mn1 scs1) (UVarUnenumerated mn2 scs2) =
    let newContents = case (mn1, mn2) of
            (Nothing, x) -> x
            (x, Nothing) -> x
            (Just n1, Just n2) -> Just (intersect n1 n2)
        newConstraints = scs1 <> scs2
     in UVarUnenumerated newContents newConstraints
intersectUVarValue UVarEliminated _ = error "intersectUVarValue: Unexpected UVarEliminated"
intersectUVarValue _ UVarEliminated = error "intersectUVarValue: Unexpected UVarEliminated"
intersectUVarValue _ _ = error "intersectUVarValue: Intersecting with enumerated value not implemented"

-----------------------
------- Top-level state
-----------------------

-- | Mutable state threaded through nondeterministic enumeration branches.
data EnumerationState = EnumerationState
    { _uvarCounter :: UVarGen
    -- ^ Fresh UVar supply.
    , _uvarRepresentative :: UnionFind
    -- ^ Persistent union-find for equality-constrained UVars.
    , _uvarValues :: Seq UVarValue
    -- ^ Per-UVar contents indexed by 'uvarToInt'.
    , _pruneDeps :: !(IntMap.IntMap [Term])
    {- ^ Pending prune checks keyed by suspended UVar id.

    A pruning oracle can use this to remember rewrite/template terms that
    could not be checked until a particular UVar is expanded. The pruned
    enumerator prioritizes expandable UVars that have entries here and
    rechecks the stored terms when that UVar is enumerated.
    -}
    }
    deriving (Eq, Ord, Show)

-- | Lens-compatible accessor for the fresh UVar supply.
uvarCounter :: (Functor f) => (UVarGen -> f UVarGen) -> EnumerationState -> f EnumerationState
uvarCounter = lens _uvarCounter (\s c -> s{_uvarCounter = c})

-- | Lens-compatible accessor for representative UVar tracking.
uvarRepresentative :: (Functor f) => (UnionFind -> f UnionFind) -> EnumerationState -> f EnumerationState
uvarRepresentative = lens _uvarRepresentative (\s uf -> s{_uvarRepresentative = uf})

-- | Lens-compatible accessor for per-UVar enumeration values.
uvarValues :: (Functor f) => (Seq UVarValue -> f (Seq UVarValue)) -> EnumerationState -> f EnumerationState
uvarValues = lens _uvarValues (\s vals -> s{_uvarValues = vals})

{- | Lens for the oracle's pending prune checks.

Pruning code uses this through helpers like 'getPruneDeps', 'addPruneDep', and
'deletePruneDep'. It is exported for lower-level oracles that need direct
access to the dependency map while composing their own enumeration actions.
-}
pruneDeps :: (Functor f) => (IntMap.IntMap [Term] -> f (IntMap.IntMap [Term])) -> EnumerationState -> f EnumerationState
pruneDeps = lens _pruneDeps (\s pds -> s{_pruneDeps = pds})

-- | Initial state whose root UVar contains the node being enumerated.
initEnumerationState :: Node -> EnumerationState
initEnumerationState n =
    let (uvg, uv) = UnionFind.nextUVar UnionFind.initUVarGen
     in EnumerationState
            uvg
            (UnionFind.withInitialValues [uv])
            (Sequence.singleton (UVarUnenumerated (Just n) Sequence.Empty))
            IntMap.empty

---------------------------------------------------------------------------
---------------------------- Enumeration monad ----------------------------
---------------------------------------------------------------------------

---------------------
-------- Monad
---------------------

-- | Nondeterministic enumeration state monad.
type EnumerateM = StateT EnumerationState SearchTree

-- | Run a lower-level enumeration action from an explicit state.
runEnumerateM :: EnumerateM a -> EnumerationState -> [(a, EnumerationState)]
runEnumerateM action = searchTreeResults . runStateT action

-- Prune deps --

{- | Return all pending prune checks.

This is mainly useful inside a pruning oracle. A caller can inspect the map
to decide whether it is currently resuming a suspended check or starting a
fresh one from the root fragment.
-}
getPruneDeps :: EnumerateM (IntMap.IntMap [Term])
getPruneDeps = gets _pruneDeps

{- | Return pending prune checks for a particular UVar id.

The ids are the integer form of 'UVar's, via 'uvarToInt'. The enumerator uses
this after expanding a UVar to decide whether any previously suspended terms
should be checked against the new fragment.
-}
getPruneDepsOf :: Int -> EnumerateM (Maybe [Term])
getPruneDepsOf uv = do
    pd <- gets _pruneDeps
    return (pd IntMap.!? uv)

{- | Remember one term to check when the given UVar is expanded.

Oracles use this when a prune test reaches an unexpanded 'TermFragmentUVar':
store the term that needs checking, return "not pruned" for now, and let the
pruned enumerator revisit the check after that UVar becomes concrete.
-}
addPruneDep :: Int -> Term -> EnumerateM ()
addPruneDep uv rw = addPruneDeps uv [rw]

addPruneDeps :: Int -> [Term] -> EnumerateM ()
addPruneDeps uv rws =
    modify' $ \s -> s{_pruneDeps = IntMap.insertWith (++) uv rws (_pruneDeps s)}

{- | Clear pending prune checks for a UVar.

The enumerator calls this when it resumes checks for an expanded UVar. Oracles
that consume entries from 'getPruneDeps' should delete them for the same
reason: each dependency is a one-shot request to recheck after expansion.
-}
deletePruneDep :: Int -> EnumerateM ()
deletePruneDep uv =
    modify' $ \s -> s{_pruneDeps = IntMap.delete uv (_pruneDeps s)}

---------------------
-------- UVar accessors
---------------------

nextUVar :: EnumerateM UVar
nextUVar = do
    c <- gets _uvarCounter
    let (c', uv) = UnionFind.nextUVar c
    modify' $ \s -> s{_uvarCounter = c'}
    return uv

addUVarValue :: Maybe Node -> EnumerateM UVar
addUVarValue x = do
    uv <- nextUVar
    modify' $ \s -> s{_uvarValues = _uvarValues s :|> UVarUnenumerated x Sequence.Empty}
    return uv

-- | Return the current representative for a UVar, updating union-find state.
getUVarRepresentative :: UVar -> EnumerateM UVar
getUVarRepresentative uv = do
    uf <- gets _uvarRepresentative
    let (uv', uf') = UnionFind.find uv uf
    modify' $ \s -> s{_uvarRepresentative = uf'}
    return uv'

-- | Look up the value for a UVar after path-compressing its representative.
getUVarValue :: UVar -> EnumerateM UVarValue
getUVarValue uv = do
    uv' <- getUVarRepresentative uv
    let idx = uvarToInt uv'
    values <- gets _uvarValues
    return $ Sequence.index values idx

-- | Look up the fragment for an already-enumerated UVar.
getTermFragForUVar :: UVar -> EnumerateM TermFragment
getTermFragForUVar uv = termFragment <$> getUVarValue uv

setUVarValue :: Int -> UVarValue -> EnumerateM ()
setUVarValue idx val =
    modify' $ \s -> s{_uvarValues = Sequence.update idx val (_uvarValues s)}

modifyUVarValue :: Int -> (UVarValue -> UVarValue) -> EnumerateM ()
modifyUVarValue idx f = do
    values <- gets _uvarValues
    setUVarValue idx (f (Sequence.index values idx))

---------------------
-------- Creating UVar's
---------------------

pecToSuspendedConstraint :: PathEClass -> EnumerateM SuspendedConstraint
pecToSuspendedConstraint pec = do
    uv <- addUVarValue Nothing
    return $ SuspendedConstraint (getPathTrie pec) uv

---------------------
-------- Merging UVar's / nodes
---------------------

-- | Merge the source UVar into the target UVar, intersecting their constraints.
assimilateUvarVal :: UVar -> UVar -> EnumerateM ()
assimilateUvarVal uvTarg uvSrc
    | uvTarg == uvSrc = return ()
    | otherwise = do
        values <- gets _uvarValues
        let srcVal = Sequence.index values (uvarToInt uvSrc)
        let targVal = Sequence.index values (uvarToInt uvTarg)
        case srcVal of
            UVarEliminated -> return () -- Happens from duplicate constraints
            _ -> do
                let v = intersectUVarValue srcVal targVal
                guard (contents v /= Just EmptyNode)
                setUVarValue (uvarToInt uvTarg) v
                setUVarValue (uvarToInt uvSrc) UVarEliminated

-- | Intersect a node and inherited constraints into the value for a UVar.
mergeNodeIntoUVarVal :: UVar -> Node -> Seq SuspendedConstraint -> EnumerateM ()
mergeNodeIntoUVarVal uv n scs = do
    uv' <- getUVarRepresentative uv
    let idx = uvarToInt uv'
    modifyUVarValue idx (intersectUVarValue (UVarUnenumerated (Just n) scs))
    newValues <- gets _uvarValues
    guard (contents (Sequence.index newValues idx) /= Just EmptyNode)

---------------------
-------- Variant maintainer
---------------------

-- This thing here might be a performance issue. UPDATE: Yes it is; clocked at 1/3 the time and 1/2 the
-- allocations of enumerateFully
--
-- It exists because it was easier to code / might actually be faster
-- to update referenced uvars here than inline in firstExpandableUVar.
-- There is no Sequence.foldMapWithIndexM.
refreshReferencedUVars :: EnumerateM ()
refreshReferencedUVars = do
    values <- gets _uvarValues

    updated <-
        traverse
            ( \case
                UVarUnenumerated n scs ->
                    UVarUnenumerated n
                        <$> mapM
                            ( \sc ->
                                SuspendedConstraint (scGetPathTrie sc)
                                    <$> getUVarRepresentative (scGetUVar sc)
                            )
                            scs
                x -> return x
            )
            values

    modify' $ \s -> s{_uvarValues = updated}

---------------------
-------- Core enumeration algorithm
---------------------
--

-- | Enumerate one node under the suspended constraints currently in scope.
enumerateNode :: Seq SuspendedConstraint -> Node -> EnumerateM TermFragment
enumerateNode _ EmptyNode = mzero
enumerateNode scs n =
    let (hereConstraints, descendantConstraints) = Sequence.partition (\(SuspendedConstraint pt _) -> isTerminalPathTrie pt) scs
     in case hereConstraints of
            Sequence.Empty -> case n of
                Mu _ -> TermFragmentUVar <$> addUVarValue (Just n)
                Node es -> enumerateEdge scs =<< chooseEdges es
                _ -> error $ "enumerateNode: unexpected node " <> show n
            (x :<| xs) -> do
                reps <- mapM (getUVarRepresentative . scGetUVar) hereConstraints
                forM_ xs $ \sc ->
                    modify' $ \s ->
                        s{_uvarRepresentative = UnionFind.union (scGetUVar x) (scGetUVar sc) (_uvarRepresentative s)}
                uv <- getUVarRepresentative (scGetUVar x)
                mapM_ (assimilateUvarVal uv) reps

                mergeNodeIntoUVarVal uv n descendantConstraints
                return $ TermFragmentUVar uv

-- | Enumerate one edge, introducing UVars for its equality classes.
enumerateEdge :: Seq SuspendedConstraint -> Edge -> EnumerateM TermFragment
enumerateEdge scs e = do
    let highestConstraintIndex = getMax $ foldMap (\sc -> Max $ fromMaybe (-1) $ getMaxNonemptyIndex $ scGetPathTrie sc) scs
    guard $ highestConstraintIndex < length (edgeChildren e)

    newScs <- Sequence.fromList <$> mapM pecToSuspendedConstraint (unsafeGetEclasses $ edgeEcs e)
    let scs' = scs <> newScs
    TermFragmentNode (edgeSymbol e) <$> zipWithM (\i n -> enumerateNode (descendScs i scs') n) [0 ..] (edgeChildren e)

---------------------
-------- Enumeration-loop control
---------------------

-- | Result of looking for the next UVar that can be expanded.
data ExpandableUVarResult
    = -- | Candidates exist, but all are blocked by suspended dependencies.
      ExpansionStuck
    | -- | Enumeration has no more UVar work to do.
      ExpansionDone
    | -- | The next unconstrained UVar to expand.
      ExpansionNext !UVar
    deriving (Show)

-- Can speed this up with bitvectors

findExpandableUVars :: EnumerateM (Maybe (IntMap.IntMap Bool))
findExpandableUVars = do
    values <- gets _uvarValues
    -- check representative uvars because only representatives are updated
    candidateMaps <-
        mapM
            ( \i -> do
                rep <- getUVarRepresentative (intToUVar i)
                v <- getUVarValue rep
                case v of
                    (UVarUnenumerated (Just (Mu _)) Sequence.Empty) -> return IntMap.empty
                    (UVarUnenumerated (Just (Mu _)) _) -> return $ IntMap.singleton (uvarToInt rep) False
                    (UVarUnenumerated (Just _) _) -> return $ IntMap.singleton (uvarToInt rep) False
                    _ -> return IntMap.empty
            )
            [0 .. (Sequence.length values - 1)]
    let candidates = IntMap.unions candidateMaps

    if IntMap.null candidates
        then
            return Nothing
        else do
            let ruledOut =
                    foldMap
                        ( \case
                            (UVarUnenumerated _ scs) ->
                                foldMap
                                    (\sc -> IntMap.singleton (uvarToInt $ scGetUVar sc) True)
                                    scs
                            _ -> IntMap.empty
                        )
                        values

            let unconstrainedCandidateMap = IntMap.filter not (ruledOut <> candidates)
            return (Just unconstrainedCandidateMap)

-- | Find the next UVar that can be expanded without violating dependencies.
firstExpandableUVar :: EnumerateM ExpandableUVarResult
firstExpandableUVar = do
    mb_unconstrainedCandidateMap <- findExpandableUVars
    case mb_unconstrainedCandidateMap of
        Nothing -> return ExpansionDone
        Just unconstrainedCandidateMap ->
            case IntMap.lookupMin unconstrainedCandidateMap of
                Nothing -> return ExpansionStuck
                Just (i, _) -> return $ ExpansionNext $ intToUVar i

ruleMatches :: Bool -> TermFragment -> Term -> EnumerateM Bool
-- TODO: this should match types
ruleMatches _ _ (Term (Symbol "<v>") _) = return True
ruleMatches
    pruneSuspended
    (TermFragmentNode "app" [_, _, tf_f, tf_v])
    (Term "app" [_, _, rw_f, rw_v]) = do
        rw_f_m <- ruleMatches pruneSuspended tf_f rw_f
        if not rw_f_m
            then return False
            else ruleMatches pruneSuspended tf_v rw_v
ruleMatches
    _
    (TermFragmentNode ts [_])
    (Term rws [_]) = return (ts == rws)
ruleMatches pruneSuspended (TermFragmentUVar uv) rw =
    do
        val <- getUVarValue uv
        case val of
            UVarEnumerated t -> ruleMatches pruneSuspended t rw
            _ -> return False
ruleMatches _ _ _ = return False

{- | Test whether a partially enumerated fragment represents any given term.

This is the helper a pruning oracle uses after receiving a @Left
TermFragment@ callback from 'getAllTermsPrune'. It understands the
Spectacular template shape used by the pruning code: @filter@ unwraps to its
body, @app@ compares the function and value positions, unary symbols compare
by symbol, and the term symbol @"<v>"@ is treated as a wildcard.

The Boolean argument marks checks that are allowed to suspend on unexpanded
UVars. The current matcher only follows already-enumerated UVars; callers that
need explicit suspension can pair this with 'addPruneDep'.
-}
fragRepresents :: Bool -> TermFragment -> [Term] -> EnumerateM Bool
fragRepresents pruneSuspended (TermFragmentNode "filter" [_, t]) rwrs = fragRepresents pruneSuspended t rwrs
fragRepresents pruneSuspended tf@(TermFragmentNode "app" [_, _, f, v]) rwrs = do
    tfMatches <- filterM (ruleMatches pruneSuspended tf) rwrs
    if not (null tfMatches)
        then return True
        else do
            r <- or <$> mapM (flip (fragRepresents False) rwrs) [f, v]
            return r
fragRepresents pruneSuspended tf@(TermFragmentNode _ [_]) rwrs =
    not . null <$> filterM (ruleMatches pruneSuspended tf) rwrs
fragRepresents pruneSuspended tf@(TermFragmentUVar uv) rwrs =
    do
        uvMatches <- filterM (ruleMatches pruneSuspended tf) rwrs
        if not (null uvMatches)
            then return True
            else do
                val <- getUVarValue uv
                case val of
                    UVarEnumerated t -> fragRepresents pruneSuspended t rwrs
                    _ -> return False
fragRepresents _ tf _ = error $ "unrecognized frag! " ++ show tf

-- | Expand one UVar, then update prune dependencies and referenced UVars.
enumerateOutUVar :: UVar -> EnumerateM TermFragment
enumerateOutUVar uv =
    do
        UVarUnenumerated (Just n) scs <- getUVarValue uv
        uv' <- getUVarRepresentative uv

        t <- case n of
            Mu _ -> enumerateNode scs (unfoldOuterRec n)
            _ -> enumerateNode scs n

        setUVarValue (uvarToInt uv') (UVarEnumerated t)
        pd <- getPruneDepsOf (uvarToInt uv)
        case pd of
            Just rws -> do
                deletePruneDep (uvarToInt uv)
                res <- fragRepresents True t rws
                if res
                    then mzero
                    else return t
            _ -> refreshReferencedUVars >> return t

-- | Expand the next available UVar, failing when enumeration is done or stuck.
enumerateOutFirstExpandableUVar :: EnumerateM ()
enumerateOutFirstExpandableUVar = do
    muv <- firstExpandableUVar
    case muv of
        ExpansionNext uv -> void $ enumerateOutUVar uv
        ExpansionDone -> mzero
        ExpansionStuck -> mzero

-- | Expand the root UVar until it represents a complete term.
enumerateFully :: EnumerateM ()
enumerateFully = const () <$> enumerateFully' () False (\x _ _ -> return (False, x))

{- | Enumerate until the root term is complete, with optional oracle pruning.

The oracle is called twice around each expandable UVar:

* @Right node@ is passed before expanding the node, so callers can drop a
  whole branch early when the current ECTA already represents a forbidden
  template.
* @Left fragment@ is passed after expansion, so callers can reject the
  concrete fragment or update their oracle state before enumeration
  continues.

The threaded state parameter belongs to the caller. Returning @True@ prunes
the current nondeterministic branch; returning @False@ keeps it. When
@usePruneHints@ is enabled, UVar ids in 'pruneDeps' are expanded first so
suspended checks resume promptly.
-}
enumerateFully' ::
    forall a.
    a ->
    Bool ->
    (a -> UVar -> Either TermFragment Node -> EnumerateM (Bool, a)) ->
    EnumerateM Bool
enumerateFully' ost usePruneHints oracle = do
    muv <-
        if usePruneHints
            then do
                hints <- IntMap.keysSet <$> getPruneDeps
                if IntSet.null hints
                    -- if we aren't targeting any terms, just expand the first one
                    then {-# SCC "no-hints" #-} firstExpandableUVar
                    else do
                        expandable <- findExpandableUVars
                        case expandable of
                            Nothing -> return ExpansionDone
                            Just ucm | IntMap.null ucm -> return ExpansionStuck
                            Just ucm ->
                                let expSet = IntMap.keysSet ucm
                                    inters = IntSet.intersection expSet hints
                                 in if not (IntSet.null inters)
                                        then
                                            return $
                                                ExpansionNext $
                                                    intToUVar (IntSet.findMax inters)
                                        else firstExpandableUVar
            else firstExpandableUVar
    case muv of
        ExpansionStuck -> mzero
        ExpansionDone -> return True
        ExpansionNext uv ->
            let continue ost' = do
                    tf <- enumerateOutUVar uv
                    (should_prune, ost'') <- oracle ost' uv (Left tf)
                    if should_prune
                        then mzero
                        else enumerateFully' ost'' usePruneHints oracle
             in do
                    UVarUnenumerated (Just n) scs <- getUVarValue uv
                    case n of
                        Mu _ | scs == Sequence.empty -> return True
                        _ -> do
                            (should_prune, ost') <- oracle ost uv (Right n)
                            if should_prune then mzero else continue ost'

---------------------
-------- Expanding an enumerated term fragment into a term
---------------------

{- | Expand a fragment even if it still contains unenumerated UVars.

Unlike 'expandTermFrag', this is safe for diagnostics and oracle logging while
enumeration is still in progress. Unexpanded non-recursive UVars become
placeholders named @<vN>@, where @N@ is the UVar id; recursive holes become
@Mu@.
-}
expandPartialTermFrag :: TermFragment -> EnumerateM Term
expandPartialTermFrag (TermFragmentNode s ts) = Term s <$> mapM expandPartialTermFrag ts
expandPartialTermFrag (TermFragmentUVar uv) =
    do
        val <- getUVarValue uv
        case val of
            UVarEnumerated t -> expandPartialTermFrag t
            UVarUnenumerated (Just (Mu _)) _ -> return $ Term "Mu" []
            _ -> return $ Term (Symbol $ "<v" <> pretty (uvarToInt uv) <> ">") []

-- | Expand a complete term fragment into a concrete term.
expandTermFrag :: TermFragment -> EnumerateM Term
expandTermFrag (TermFragmentNode s ts) = Term s <$> mapM expandTermFrag ts
expandTermFrag (TermFragmentUVar uv) =
    do
        val <- getUVarValue uv
        case val of
            UVarEnumerated t -> expandTermFrag t
            UVarUnenumerated (Just (Mu _)) _ -> return $ Term "Mu" []
            _ ->
                error "expandTermFrag: Non-recursive, unenumerated node encountered"

-- | Expand an already-enumerated UVar into a concrete term.
expandUVar :: UVar -> EnumerateM Term
expandUVar uv = do
    values <- gets _uvarValues
    representatives <- gets _uvarRepresentative
    return $
        State.evalState
            (expandUVarMemo representatives values uv)
            IntMap.empty

-- | Expand a UVar once and share equal subterms in the result.
expandUVarMemo ::
    UnionFind ->
    Seq UVarValue ->
    UVar ->
    State.State (IntMap.IntMap Term) Term
expandUVarMemo representatives values = expandUVar'
  where
    expandFragment (TermFragmentNode symbol children) =
        Term symbol <$> mapM expandFragment children
    expandFragment (TermFragmentUVar child) = expandUVar' child

    expandUVar' child = do
        let (representative, _) = UnionFind.find child representatives
            index = uvarToInt representative
        cached <- State.gets (IntMap.lookup index)
        case cached of
            Just term -> return term
            Nothing -> case Sequence.index values index of
                UVarEnumerated fragment -> do
                    term <- expandFragment fragment
                    State.modify' (IntMap.insert index term)
                    return term
                UVarUnenumerated (Just (Mu _)) _ -> return $ Term "Mu" []
                _ -> error "expandUVarMemo: Non-recursive, unenumerated node encountered"

---------------------
-------- Full enumeration
---------------------

-- | Enumerate terms, replacing recursive holes with a truncation marker.
getAllTruncatedTerms :: Node -> [Term]
getAllTruncatedTerms n = map (termFragToTruncatedTerm . fst) $
    flip runEnumerateM (initEnumerationState n) $ do
        enumerateFully
        getTermFragForUVar (intToUVar 0)

{- | Enumerate terms while letting an oracle prune branches.

This is the public entry point for pruning-aware enumeration. The oracle has
type:

@
state -> UVar -> Either TermFragment Node -> EnumerateM (Bool, state)
@

It receives the caller state, the UVar being considered, and either the node
about to be expanded (@Right@) or the fragment just produced (@Left@). Return
@True@ to discard that branch, or @False@ with updated state to keep
enumerating. A typical Spectacular-style oracle uses @Right node@ with
'nodeRepresentsTemplate' to reject whole ECTA branches, and @Left fragment@
with 'fragRepresents' to reject terms that match known rewrites/templates.
-}
getAllTermsPrune ::
    forall a.
    a ->
    (a -> UVar -> Either TermFragment Node -> EnumerateM (Bool, a)) ->
    Node ->
    [Term]
getAllTermsPrune ost oracle n =
    map fst $ flip runEnumerateM (initEnumerationState n) $ enumPrune ost oracle

{- | Monadic form of 'getAllTermsPrune'.

Use this when the caller is already composing lower-level enumeration actions
in 'EnumerateM'. Most callers should prefer 'getAllTermsPrune'.
-}
enumPrune :: forall a. a -> (a -> UVar -> Either TermFragment Node -> EnumerateM (Bool, a)) -> EnumerateM Term
enumPrune a oracle = do
    finished <- enumerateFully' a True oracle
    if finished then expandUVar (intToUVar 0) else mzero

{- | Resumable search for complete terms represented by an ECTA.

Use 'stepTermSearch' to inspect one edge choice at a time. The search value is
persistent, so callers can retain unselected branches for backtracking.
-}
newtype TermSearch = TermSearch (SearchTree Term)

-- | One observable step in a term search.
data TermSearchStep
    = TermSearchDead
    | TermSearchDone !Term
    | TermSearchChoice !(NonEmpty TermBranch)

-- | One alternative from an ECTA edge choice.
data TermBranch = TermBranch !BranchInfo !TermSearch

-- | Information that a branch-selection policy can inspect.
newtype BranchInfo = BranchInfo
    { branchSymbol :: Maybe Symbol
    }
    deriving (Eq, Ord, Show)

-- | Limits for one sampling attempt.
data SampleLimits = SampleLimits
    { sampleChoiceLimit :: !Int
    , sampleBacktrackLimit :: !Int
    }
    deriving (Eq, Ord, Show)

-- | Failures reported by bounded sampling.
data SampleError
    = SampleNoAcceptedTerm
    | SampleChoiceLimitExceeded
    | SampleBacktrackLimitExceeded
    | SampleInvalidChoiceIndex !Int !Int
    deriving (Eq, Ord, Show)

-- | Conservative limits suitable for finite testing automata.
defaultSampleLimits :: SampleLimits
defaultSampleLimits =
    SampleLimits
        { sampleChoiceLimit = 100000
        , sampleBacktrackLimit = 10000
        }

-- | Start a resumable search without a pruning oracle.
startTermSearch :: Node -> TermSearch
startTermSearch n =
    TermSearch $
        fmap fst $
            runStateT
                (enumPrune () (\_ _ _ -> return (False, ())))
                (initEnumerationState n)

-- | Inspect the next result or edge choice in a term search.
stepTermSearch :: TermSearch -> TermSearchStep
stepTermSearch (TermSearch SearchTreeDead) = TermSearchDead
stepTermSearch (TermSearch (SearchTreeDone term)) = TermSearchDone term
stepTermSearch (TermSearch (SearchTreeChoice branches)) =
    TermSearchChoice (fmap toTermBranch branches)
  where
    toTermBranch (SearchTreeBranch label search) =
        TermBranch (BranchInfo label) (TermSearch search)

-- | Return the metadata for one term-search branch.
termBranchInfo :: TermBranch -> BranchInfo
termBranchInfo (TermBranch info _) = info

-- | Continue a term search through one branch.
followTermBranch :: TermBranch -> TermSearch
followTermBranch (TermBranch _ search) = search

{- | Select one complete term without enumerating all complete terms.

The selector receives the available branch metadata and must return a zero-based
index plus its next state. Unselected alternatives remain available for bounded
depth-first backtracking.
-}
sampleTerm ::
    SampleLimits ->
    (NonEmpty BranchInfo -> g -> (Int, g)) ->
    g ->
    Node ->
    Either SampleError (Term, g)
sampleTerm limits select initialState = go 0 0 initialState [] . startTermSearch
  where
    go choices backtracks selectorState pending search =
        case stepTermSearch search of
            TermSearchDead ->
                case pending of
                    [] -> Left SampleNoAcceptedTerm
                    next : rest
                        | backtracks >= sampleBacktrackLimit limits ->
                            Left SampleBacktrackLimitExceeded
                        | otherwise ->
                            go choices (backtracks + 1) selectorState rest next
            TermSearchDone term -> Right (term, selectorState)
            TermSearchChoice branches
                | choices >= sampleChoiceLimit limits -> Left SampleChoiceLimitExceeded
                | otherwise ->
                    let infos = fmap termBranchInfo branches
                        (selectedIndex, selectorState') = select infos selectorState
                        branchCount = length (NonEmpty.toList branches)
                     in case removeAt selectedIndex (NonEmpty.toList branches) of
                            Nothing -> Left (SampleInvalidChoiceIndex selectedIndex branchCount)
                            Just (selected, remaining) ->
                                let pending' = maybe pending (: pending) (searchFor remaining)
                                 in go
                                        (choices + 1)
                                        backtracks
                                        selectorState'
                                        pending'
                                        (followTermBranch selected)

    removeAt i xs
        | i < 0 = Nothing
        | otherwise =
            case splitAt i xs of
                (before, selected : after) -> Just (selected, before <> after)
                _ -> Nothing

    searchFor [] = Nothing
    searchFor (branch : branches) =
        Just $
            TermSearch $
                SearchTreeChoice
                    (toSearchBranch branch :| map toSearchBranch branches)

    toSearchBranch (TermBranch (BranchInfo label) (TermSearch search)) =
        SearchTreeBranch label search

-- | Select a complete term and retain alternatives only for backtracking.
sampleTermBacktracking ::
    SampleLimits ->
    (NonEmpty BranchInfo -> g -> (Int, g)) ->
    g ->
    TermSearch ->
    Either SampleError (Term, g)
sampleTermBacktracking limits select initialState (TermSearch initialSearch) =
    go 0 0 initialState [] initialSearch
  where
    go choices backtracks selectorState pending search =
        case search of
            SearchTreeDead ->
                case pending of
                    [] -> Left SampleNoAcceptedTerm
                    next : rest
                        | backtracks >= sampleBacktrackLimit limits ->
                            Left SampleBacktrackLimitExceeded
                        | otherwise ->
                            go choices (backtracks + 1) selectorState rest next
            SearchTreeDone term -> Right (term, selectorState)
            SearchTreeChoice branches
                | choices >= sampleChoiceLimit limits -> Left SampleChoiceLimitExceeded
                | otherwise ->
                    let infos = fmap (BranchInfo . searchTreeBranchLabel) branches
                        (selectedIndex, selectorState') = select infos selectorState
                        branchCount = NonEmpty.length branches
                     in case removeSearchBranchAt selectedIndex branches of
                            Nothing -> Left (SampleInvalidChoiceIndex selectedIndex branchCount)
                            Just (selected, remaining) ->
                                go
                                    (choices + 1)
                                    backtracks
                                    selectorState'
                                    (maybe pending (: pending) remaining)
                                    (searchTreeBranchSearch selected)

{- | Select one term from a reusable search.

The search is persistent. Reusing it shares the evaluated search prefixes and
their enumeration states between samples. A successful branch does not retain
backtracking alternatives. If it reaches a dead end, the sampler restarts with
bounded backtracking.
-}
sampleTermSearch ::
    SampleLimits ->
    (NonEmpty BranchInfo -> g -> (Int, g)) ->
    g ->
    TermSearch ->
    Either SampleError (Term, g)
sampleTermSearch limits select initialState initialSearch =
    case goFast 0 initialState initialSearch of
        Left SampleNoAcceptedTerm ->
            sampleTermBacktracking limits select initialState initialSearch
        result -> result
  where
    goFast choices selectorState (TermSearch search) =
        case search of
            SearchTreeDead -> Left SampleNoAcceptedTerm
            SearchTreeDone term -> Right (term, selectorState)
            SearchTreeChoice branches
                | choices >= sampleChoiceLimit limits -> Left SampleChoiceLimitExceeded
                | otherwise ->
                    let infos = fmap (BranchInfo . searchTreeBranchLabel) branches
                        (selectedIndex, selectorState') = select infos selectorState
                        branchCount = NonEmpty.length branches
                     in case selectAt selectedIndex branches of
                            Nothing -> Left (SampleInvalidChoiceIndex selectedIndex branchCount)
                            Just selected ->
                                goFast
                                    (choices + 1)
                                    selectorState'
                                    (TermSearch $ searchTreeBranchSearch selected)

    selectAt i _ | i < 0 = Nothing
    selectAt 0 (branch :| _) = Just branch
    selectAt i (_ :| branches) = goTo (i - 1) branches
      where
        goTo _ [] = Nothing
        goTo 0 (branch : _) = Just branch
        goTo n (_ : rest) = goTo (n - 1) rest
{-# INLINE sampleTermSearch #-}

{- | Select one term when the policy needs only the branch count.

This variant does not allocate branch metadata. Use 'sampleTermSearch' when a
policy must inspect branch symbols.
-}
sampleTermSearchByCount ::
    SampleLimits ->
    (Int -> g -> (Int, g)) ->
    g ->
    TermSearch ->
    Either SampleError (Term, g)
sampleTermSearchByCount limits select initialState initialSearch =
    case goFast 0 initialState initialSearch of
        Left SampleNoAcceptedTerm -> go 0 0 initialState [] initialSearch
        result -> result
  where
    goFast choices selectorState (TermSearch search) =
        case search of
            SearchTreeDead -> Left SampleNoAcceptedTerm
            SearchTreeDone term -> Right (term, selectorState)
            SearchTreeChoice branches
                | choices >= sampleChoiceLimit limits -> Left SampleChoiceLimitExceeded
                | otherwise ->
                    let branchCount = NonEmpty.length branches
                        (selectedIndex, selectorState') = select branchCount selectorState
                     in case selectAt selectedIndex branches of
                            Nothing -> Left (SampleInvalidChoiceIndex selectedIndex branchCount)
                            Just selected ->
                                goFast
                                    (choices + 1)
                                    selectorState'
                                    (TermSearch $ searchTreeBranchSearch selected)

    go choices backtracks selectorState pending (TermSearch search) =
        case search of
            SearchTreeDead ->
                case pending of
                    [] -> Left SampleNoAcceptedTerm
                    next : rest
                        | backtracks >= sampleBacktrackLimit limits ->
                            Left SampleBacktrackLimitExceeded
                        | otherwise ->
                            go choices (backtracks + 1) selectorState rest (TermSearch next)
            SearchTreeDone term -> Right (term, selectorState)
            SearchTreeChoice branches
                | choices >= sampleChoiceLimit limits -> Left SampleChoiceLimitExceeded
                | otherwise ->
                    let branchCount = NonEmpty.length branches
                        (selectedIndex, selectorState') = select branchCount selectorState
                     in case removeSearchBranchAt selectedIndex branches of
                            Nothing -> Left (SampleInvalidChoiceIndex selectedIndex branchCount)
                            Just (selected, remaining) ->
                                go
                                    (choices + 1)
                                    backtracks
                                    selectorState'
                                    (maybe pending (: pending) remaining)
                                    (TermSearch $ searchTreeBranchSearch selected)

    selectAt i _ | i < 0 = Nothing
    selectAt 0 (branch :| _) = Just branch
    selectAt i (_ :| branches) = goTo (i - 1) branches
      where
        goTo _ [] = Nothing
        goTo 0 (branch : _) = Just branch
        goTo n (_ : rest) = goTo (n - 1) rest
{-# INLINE sampleTermSearchByCount #-}

-- | Select one branch and package the other branches as one search.
removeSearchBranchAt ::
    Int ->
    NonEmpty (SearchTreeBranch a) ->
    Maybe (SearchTreeBranch a, Maybe (SearchTree a))
removeSearchBranchAt index (first :| rest)
    | index < 0 = Nothing
    | otherwise = go [] index (first : rest)
  where
    go _ _ [] = Nothing
    go before 0 (selected : after) =
        Just (selected, searchChoice $ reverse before <> after)
    go before i (branch : branches) = go (branch : before) (i - 1) branches

    searchChoice [] = Nothing
    searchChoice (branch : branches) =
        Just $ SearchTreeChoice (branch :| branches)

-- | Return the label attached to a search branch.
searchTreeBranchLabel :: SearchTreeBranch a -> Maybe Symbol
searchTreeBranchLabel (SearchTreeBranch label _) = label

-- | Return the continuation attached to a search branch.
searchTreeBranchSearch :: SearchTreeBranch a -> SearchTree a
searchTreeBranchSearch (SearchTreeBranch _ search) = search

-- | Enumerate all complete terms represented by an ECTA in depth-first order.
getAllTerms :: Node -> [Term]
getAllTerms n = searchTreeResults search
  where
    TermSearch search = startTermSearch n
