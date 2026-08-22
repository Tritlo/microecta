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
    initEnumerationState,
    EnumerateM,
    getUVarRepresentative,
    assimilateUvarVal,
    mergeNodeIntoUVarVal,
    getUVarValue,
    getTermFragForUVar,
    runEnumerateM,
    enumerateNode,
    enumerateEdge,
    ExpandableUVarResult (..),
    ExpansionOrder,
    noExpansionPreference,
    firstExpandableUVar,
    nextExpandableUVar,
    enumerateOutUVar,
    enumerateOutFirstExpandableUVar,
    enumerateFully,
    expandTermFrag,
    expandPartialTermFrag,
    expandUVar,
    getAllTruncatedTerms,
    getAllTerms,
    getAllTermsPrune,
    getAllTermsPruneWith,
    enumPrune,
    enumPruneWith,
) where

import Control.Monad (forM_, guard, mzero, void, zipWithM)
import Control.Monad.State.Strict (StateT (..), gets, modify')
import Control.Monad.Trans.Class (lift)
import qualified Data.IntMap as IntMap
import Data.Maybe (fromMaybe)
import Data.Semigroup (Max (..))
import Data.Sequence (Seq ((:<|), (:|>)))
import qualified Data.Sequence as Sequence

import Data.ECTA.Internal.ECTA.Operations
import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Paths
import Data.ECTA.Term
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
    = -- | UVar still has an ECTA node to expand.
      UVarUnenumerated
        -- | ECTA node still to enumerate, or 'Nothing' for pure constraint variables.
        !(Maybe Node)
        -- | Constraints that should be carried while enumerating this value.
        !(Seq SuspendedConstraint)
    | -- | UVar has been expanded to a fragment.
      UVarEnumerated !TermFragment
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

-- | Initial state whose root UVar contains the node being enumerated.
initEnumerationState :: Node -> EnumerationState
initEnumerationState n =
    let (uvg, uv) = UnionFind.nextUVar UnionFind.initUVarGen
     in EnumerationState
            uvg
            (UnionFind.withInitialValues [uv])
            (Sequence.singleton (UVarUnenumerated (Just n) Sequence.Empty))

---------------------------------------------------------------------------
---------------------------- Enumeration monad ----------------------------
---------------------------------------------------------------------------

---------------------
-------- Monad
---------------------

-- | Nondeterministic enumeration state monad.
type EnumerateM = StateT EnumerationState []

-- | Run a lower-level enumeration action from an explicit state.
runEnumerateM :: EnumerateM a -> EnumerationState -> [(a, EnumerationState)]
runEnumerateM = runStateT

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
getTermFragForUVar uv = do
    value <- getUVarValue uv
    case value of
        UVarEnumerated fragment -> return fragment
        _ -> error "getTermFragForUVar: UVar has not been enumerated"

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
                guard $ not $ hasEmptyContents v
                setUVarValue (uvarToInt uvTarg) v
                setUVarValue (uvarToInt uvSrc) UVarEliminated

-- | Intersect a node and inherited constraints into the value for a UVar.
mergeNodeIntoUVarVal :: UVar -> Node -> Seq SuspendedConstraint -> EnumerateM ()
mergeNodeIntoUVarVal uv n scs = do
    uv' <- getUVarRepresentative uv
    let idx = uvarToInt uv'
    modifyUVarValue idx (intersectUVarValue (UVarUnenumerated (Just n) scs))
    newValues <- gets _uvarValues
    guard $ not $ hasEmptyContents $ Sequence.index newValues idx

-- | Whether an unenumerated variable has already reduced to the empty node.
hasEmptyContents :: UVarValue -> Bool
hasEmptyContents (UVarUnenumerated (Just EmptyNode) _) = True
hasEmptyContents _ = False

---------------------
-------- Variant maintainer
---------------------

{- | Rewrite every suspended constraint to name its UVar's representative.

'findExpandableUVars' matches candidate UVars against the UVars named by
suspended constraints, and only representatives are kept up to date, so the
two have to agree before that comparison is meaningful.

This is a whole-state sweep and it costs: roughly a third of the time and half
the allocation of 'enumerateFully'. Folding it into 'firstExpandableUVar'
would avoid the separate pass, but there is no @Sequence.foldMapWithIndexM@ to
do it in one traversal.
-}
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

-- | Enumerate one node under the suspended constraints currently in scope.
enumerateNode :: Seq SuspendedConstraint -> Node -> EnumerateM TermFragment
enumerateNode _ EmptyNode = mzero
enumerateNode scs n =
    let (hereConstraints, descendantConstraints) = Sequence.partition (\(SuspendedConstraint pt _) -> isTerminalPathTrie pt) scs
     in case hereConstraints of
            Sequence.Empty -> case n of
                Mu _ -> TermFragmentUVar <$> addUVarValue (Just n)
                Node es -> enumerateEdge scs =<< lift es
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
                    -- An unconstrained Mu is the recursive base case: expanding
                    -- it would unfold forever with nothing to stop it.
                    UVarUnenumerated (Just (Mu _)) Sequence.Empty -> return IntMap.empty
                    UVarUnenumerated (Just _) _ -> return $ IntMap.singleton (uvarToInt rep) False
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

{- | Which of the currently expandable UVars to expand next.

The list holds every UVar that can be expanded right now, in the order the
enumerator itself would consider them, so its head is what it would pick.

Returning 'Nothing' means "no preference". Returning a UVar that is not in the
list means the same thing: this steers the order and can never make a UVar
expandable before it is ready.

Steering is worth it when the caller is waiting on a particular hole - one
whose expansion settles a check parked in the oracle's own state - and would
rather resolve it than enumerate the rest of a branch the check will kill.
It cannot change which UVars are expandable, only which of them goes first.
-}
type ExpansionOrder state = state -> [UVar] -> Maybe UVar

-- | The 'ExpansionOrder' that always leaves the choice to the enumerator.
noExpansionPreference :: ExpansionOrder state
noExpansionPreference _ _ = Nothing

-- | Find the next UVar that can be expanded without violating dependencies.
firstExpandableUVar :: EnumerateM ExpandableUVarResult
firstExpandableUVar = nextExpandableUVar (const Nothing)

-- | 'firstExpandableUVar', letting the caller steer among the candidates.
nextExpandableUVar :: ([UVar] -> Maybe UVar) -> EnumerateM ExpandableUVarResult
nextExpandableUVar choose = do
    mb_unconstrainedCandidateMap <- findExpandableUVars
    return $ case mb_unconstrainedCandidateMap of
        Nothing -> ExpansionDone
        Just unconstrainedCandidateMap ->
            case IntMap.lookupMin unconstrainedCandidateMap of
                Nothing -> ExpansionStuck
                Just (lowest, _) ->
                    -- The candidate list is only forced if the caller looks at
                    -- it, so the default order pays nothing for this.
                    ExpansionNext $
                        case choose (map intToUVar $ IntMap.keys unconstrainedCandidateMap) of
                            Just preferred
                                | IntMap.member (uvarToInt preferred) unconstrainedCandidateMap ->
                                    preferred
                            _ -> intToUVar lowest

{- | Expand one UVar into a fragment.

The pattern bind is deliberately failable: 'EnumerateM' fails into the list
monad, so a UVar that is not an unexpanded node drops this branch instead of
raising. The branch is unreachable through 'enumerateFully'' and
'enumerateOutFirstExpandableUVar', which only offer expandable UVars.
-}
enumerateOutUVar :: UVar -> EnumerateM TermFragment
enumerateOutUVar uv =
    do
        UVarUnenumerated (Just n) scs <- getUVarValue uv
        uv' <- getUVarRepresentative uv

        t <- case n of
            Mu _ -> enumerateNode scs (unfoldOuterRec n)
            _ -> enumerateNode scs n

        setUVarValue (uvarToInt uv') (UVarEnumerated t)
        -- Expanding a UVar merges others into it, so suspended constraints
        -- recorded elsewhere may now name non-representatives.
        -- 'firstExpandableUVar' compares against representatives.
        refreshReferencedUVars
        return t

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
enumerateFully =
    void $ enumerateFully' () noExpansionPreference (\state _ _ -> return (False, state))

{- | Enumerate until the root term is complete, with optional oracle pruning.

The oracle is called twice around each expandable UVar:

* @Right node@ is passed before expanding the node, so callers can drop a
  whole branch early when the ECTA about to be expanded is already known to
  be uninteresting.
* @Left fragment@ is passed after expansion, together with the UVar it came
  from, so callers can reject the fragment or update their state before
  enumeration continues.

The threaded state parameter belongs entirely to the caller. Returning @True@
prunes the current nondeterministic branch; returning @False@ keeps it.

The 'ExpansionOrder' sees the same state and may steer which expandable UVar
goes next; 'noExpansionPreference' leaves that to the enumerator.
-}
enumerateFully' ::
    forall a.
    a ->
    ExpansionOrder a ->
    (a -> UVar -> Either TermFragment Node -> EnumerateM (Bool, a)) ->
    EnumerateM Bool
enumerateFully' ost order oracle = do
    muv <- nextExpandableUVar (order ost)
    case muv of
        ExpansionStuck -> mzero
        ExpansionDone -> return True
        ExpansionNext uv ->
            let continue ost' = do
                    tf <- enumerateOutUVar uv
                    (should_prune, ost'') <- oracle ost' uv (Left tf)
                    if should_prune
                        then mzero
                        else enumerateFully' ost'' order oracle
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
    UVarEnumerated t <- getUVarValue uv
    expandTermFrag t

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
enumerating. The state is threaded down each nondeterministic branch
separately, so what one branch records cannot leak into a sibling.

What counts as a term worth rejecting is the caller's to decide: this library
supplies the callbacks and the means to read a partial term
('expandPartialTermFrag') or test an ECTA node ('nodeRepresentsTemplate'), and
no notion of which shapes are interesting.

A check that cannot be settled because the fragment still holds an unexpanded
'TermFragmentUVar' does not need help from this module either. Park it in the
oracle's own state under that hole's representative
('getUVarRepresentative'), and settle it when the oracle is called with
@Left fragment@ for that UVar, which is guaranteed to happen before the branch
completes. 'getAllTermsPruneWith' can bring that moment forward.
-}
getAllTermsPrune ::
    forall a.
    a ->
    (a -> UVar -> Either TermFragment Node -> EnumerateM (Bool, a)) ->
    Node ->
    [Term]
getAllTermsPrune ost = getAllTermsPruneWith ost noExpansionPreference

{- | 'getAllTermsPrune' with a say in which UVar is expanded next.

An oracle that parks checks on unexpanded holes can use this to reach those
holes sooner: return the candidate the parked checks are waiting on, and a
branch that a check would kill dies before the rest of it is enumerated.

This is a hint about order, not about which terms are enumerated. It cannot
make a UVar expandable early, and for an oracle whose rejections are monotone
- once a branch can be rejected it stays rejectable - it changes only how much
work is done. An oracle that decides differently depending on the order it
sees UVars in will, of course, see the difference.
-}
getAllTermsPruneWith ::
    forall a.
    a ->
    ExpansionOrder a ->
    (a -> UVar -> Either TermFragment Node -> EnumerateM (Bool, a)) ->
    Node ->
    [Term]
getAllTermsPruneWith ost order oracle n =
    map fst $ flip runEnumerateM (initEnumerationState n) $ enumPruneWith ost order oracle

{- | Monadic form of 'getAllTermsPrune'.

Use this when the caller is already composing lower-level enumeration actions
in 'EnumerateM'. Most callers should prefer 'getAllTermsPrune'.
-}
enumPrune :: forall a. a -> (a -> UVar -> Either TermFragment Node -> EnumerateM (Bool, a)) -> EnumerateM Term
enumPrune a = enumPruneWith a noExpansionPreference

-- | Monadic form of 'getAllTermsPruneWith'.
enumPruneWith ::
    forall a.
    a ->
    ExpansionOrder a ->
    (a -> UVar -> Either TermFragment Node -> EnumerateM (Bool, a)) ->
    EnumerateM Term
enumPruneWith a order oracle = do
    finished <- enumerateFully' a order oracle
    if finished then expandUVar (intToUVar 0) else mzero

-- | Enumerate all complete terms represented by an ECTA.
getAllTerms :: Node -> [Term]
getAllTerms = getAllTermsPrune () (\_ _ _ -> return (False, ()))
