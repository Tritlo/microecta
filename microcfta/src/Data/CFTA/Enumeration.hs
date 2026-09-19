{-# LANGUAGE OverloadedStrings #-}

{- | Enumeration of constrained automata.

One enumerator serves every constraint theory. It builds 'TermFragment's
before expanding them to concrete @Tree.Tree@s. The path equalities of a
constraint ('equalities') are suspended obligations that point at UVars:
when enumeration descends through an edge, those obligations descend with
it, and when one reaches the node it names, the UVars are merged so future
choices stay consistent. A constraint with a 'residual' beyond its
equalities is recorded with the subterm it guards, and 'runs' hands those
pairs to the caller to decide. An automaton with no constraint at all is
listed level by level without the enumeration state, so a cyclic one gives an
infinite lazy list.

Most callers use 'terms' or 'runs'. The lower-level state operations are
exposed for pruning oracles and downstream tools that need to inspect or
steer enumeration.
-}
module Data.CFTA.Enumeration (
    -- * Terms and runs
    terms,
    termsWith,
    runs,
    truncatedTerms,
    plainTerms,
    unconstrained,

    -- * Pruning oracles
    termsPrune,
    termsPruneWith,
    ExpansionOrder,
    noExpansionPreference,
    expandPartialTermFrag,
    getUVarRepresentative,

    -- * Fragments
    TermFragment (..),
    PartialSymbol (..),
    termFragToTruncatedTerm,

    -- * Enumeration state
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
    runEnumerateM,
    assimilateUvarVal,
    mergeNodeIntoUVarVal,
    getUVarValue,
    rootTermFrag,
    enumerateNode,
    enumerateEdge,
    ExpandableUVarResult (..),
    firstExpandableUVar,
    nextExpandableUVar,
    enumerateOutUVar,
    enumerateOutFirstExpandableUVar,
    enumerateFully,
    expandTermFrag,
    expandTermFragWith,
    expandUVar,
) where

import Control.Monad (forM_, guard, mzero, void, when, zipWithM)
import Control.Monad.State.Strict (StateT (..), gets, modify')
import Control.Monad.Trans.Class (lift)
import qualified Data.Foldable as Foldable
import Data.Hashable (Hashable (..))
import qualified Data.IntSet as IntSet
import Data.List (compareLength)
import Data.Maybe (fromMaybe)
import Data.Monoid (All (..))
import Data.Semigroup (Max (..))
import Data.Sequence (Seq ((:<|), (:|>)))
import qualified Data.Sequence as Sequence
import Data.String (IsString (..))
import qualified Data.Tree as Tree
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (Typeable, typeRep)

import Data.CFTA.Constraint.Equality (
    EqConstraints (EmptyConstraints),
    PathEClass (getPathTrie),
    PathTrie,
    getMaxNonemptyIndex,
    isEmptyPathTrie,
    isTerminalPathTrie,
    pathTrieDescend,
    unsafeGetEclasses,
 )
import Data.CFTA.Internal.Tree (termsBy)
import Data.CFTA.Internal.UnionFind (UVar, UVarGen, UnionFind, intToUVar, uvarToInt)
import qualified Data.CFTA.Internal.UnionFind as UnionFind
import Data.CFTA.Interned
import Data.CFTA.Interned.Memo (TypeableMemoCache, memoTypeableWith, newTypeableMemoCache)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as Set

-------------------------------------------------------------------------------

---------------------------------------------------------------------------
------------------------------- Term fragments ----------------------------
---------------------------------------------------------------------------

-- | Partially enumerated term with holes for nodes that still need expansion.
data TermFragment symbol
    = -- | Concrete symbol with already-created child fragments.
      TermFragmentNode !symbol ![TermFragment symbol]
    | -- | Hole whose value is tracked in the enumeration state.
      TermFragmentUVar UVar
    deriving (Eq, Ord, Show)

{- | A label in a term that may still contain enumeration holes.

Keeping holes outside the caller's alphabet prevents a real symbol from being
mistaken for a rendered placeholder such as @v0@. 'TruncatedRecursion' records a
recursive node that enumeration has finished with: one carrying no suspended
constraints, which is where enumeration stops. A recursive node that still has
constraints pending is a 'UVarHole', because it may still be expanded.
-}
data PartialSymbol symbol
    = -- | A symbol from the ECTA's alphabet.
      ConcreteSymbol !symbol
    | -- | An unexpanded enumeration variable.
      UVarHole !UVar
    | -- | Enumeration stopped at an unconstrained recursive node.
      TruncatedRecursion
    deriving (Eq, Ord, Show)

instance (Hashable symbol) => Hashable (PartialSymbol symbol) where
    hashWithSalt salt (ConcreteSymbol symbol) =
        salt `hashWithSalt` (0 :: Int) `hashWithSalt` symbol
    hashWithSalt salt (UVarHole uv) =
        salt `hashWithSalt` (1 :: Int) `hashWithSalt` (uvarToInt uv)
    hashWithSalt salt TruncatedRecursion =
        salt `hashWithSalt` (2 :: Int)

-- | Convert a fragment to a term while retaining holes outside the alphabet.
termFragToTruncatedTerm :: TermFragment symbol -> Tree.Tree (PartialSymbol symbol)
termFragToTruncatedTerm (TermFragmentNode symbol children) =
    Tree.Node (ConcreteSymbol symbol) (map termFragToTruncatedTerm children)
termFragToTruncatedTerm (TermFragmentUVar uv) = Tree.Node (UVarHole uv) []

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
data UVarValue symbol constraint
    = -- | UVar still has an ECTA node to expand.
      UVarUnenumerated
        -- | ECTA node still to enumerate, or 'Nothing' for pure constraint variables.
        !(Maybe (Node symbol constraint))
        -- | Constraints that should be carried while enumerating this value.
        !(Seq SuspendedConstraint)
    | -- | UVar has been expanded to a fragment.
      UVarEnumerated !(TermFragment symbol)
    | -- | UVar was merged into another representative and should no longer be used.
      UVarEliminated
    deriving (Eq, Ord, Show)

intersectUVarValue ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    UVarValue symbol constraint -> UVarValue symbol constraint -> UVarValue symbol constraint
intersectUVarValue (UVarUnenumerated mn1 scs1) (UVarUnenumerated mn2 scs2) =
    let newContents = case (mn1, mn2) of
            (Nothing, x) -> x
            (x, Nothing) -> x
            (Just n1, Just n2) -> Just (n1 `intersect` n2)
        newConstraints = scs1 <> scs2
     in UVarUnenumerated newContents newConstraints
intersectUVarValue UVarEliminated _ = error "intersectUVarValue: Unexpected UVarEliminated"
intersectUVarValue _ UVarEliminated = error "intersectUVarValue: Unexpected UVarEliminated"
intersectUVarValue _ _ = error "intersectUVarValue: Intersecting with enumerated value not implemented"

-----------------------
------- Top-level state
-----------------------

-- | Mutable state threaded through nondeterministic enumeration branches.
data EnumerationState symbol constraint = EnumerationState
    { _uvarCounter :: UVarGen
    -- ^ Fresh UVar supply.
    , _uvarRepresentative :: UnionFind
    -- ^ Persistent union-find for equality-constrained UVars.
    , _uvarValues :: Seq (UVarValue symbol constraint)
    {- ^ Per-UVar contents indexed by 'uvarToInt'. A slot is
    'UVarEliminated' exactly when its UVar is not a representative;
    @findExpandableUVars@ relies on 'assimilateUvarVal' maintaining this.
    -}
    , _obligations :: [(constraint, TermFragment symbol)]
    -- ^ Constraints with a 'residual', each with the fragment it guards.
    }
    deriving (Eq, Ord, Show)

-- | Lens-compatible accessor for the fresh UVar supply.
uvarCounter ::
    (Functor f) => (UVarGen -> f UVarGen) -> EnumerationState symbol constraint -> f (EnumerationState symbol constraint)
uvarCounter = lens _uvarCounter (\s c -> s{_uvarCounter = c})

-- | Lens-compatible accessor for representative UVar tracking.
uvarRepresentative ::
    (Functor f) =>
    (UnionFind -> f UnionFind) -> EnumerationState symbol constraint -> f (EnumerationState symbol constraint)
uvarRepresentative = lens _uvarRepresentative (\s uf -> s{_uvarRepresentative = uf})

-- | Lens-compatible accessor for per-UVar enumeration values.
uvarValues ::
    (Functor f) =>
    (Seq (UVarValue symbol constraint) -> f (Seq (UVarValue symbol constraint))) ->
    EnumerationState symbol constraint ->
    f (EnumerationState symbol constraint)
uvarValues = lens _uvarValues (\s vals -> s{_uvarValues = vals})

-- | Initial state whose root UVar contains the node being enumerated.
initEnumerationState :: Node symbol constraint -> EnumerationState symbol constraint
initEnumerationState n =
    let (uvg, uv) = UnionFind.nextUVar UnionFind.initUVarGen
     in EnumerationState
            uvg
            (UnionFind.withInitialValues [uv])
            (Sequence.singleton (UVarUnenumerated (Just n) Sequence.Empty))
            []

---------------------------------------------------------------------------
---------------------------- Enumeration monad ----------------------------
---------------------------------------------------------------------------

---------------------
-------- Monad
---------------------

-- | Nondeterministic enumeration state monad.
type EnumerateM symbol constraint = StateT (EnumerationState symbol constraint) []

-- | Run a lower-level enumeration action from an explicit state.
runEnumerateM ::
    EnumerateM symbol constraint a -> EnumerationState symbol constraint -> [(a, EnumerationState symbol constraint)]
runEnumerateM = runStateT

---------------------
-------- UVar accessors
---------------------

nextUVar :: EnumerateM symbol constraint UVar
nextUVar = do
    c <- gets _uvarCounter
    let (c', uv) = UnionFind.nextUVar c
    modify' $ \s -> s{_uvarCounter = c'}
    return uv

addUVarValue :: Maybe (Node symbol constraint) -> EnumerateM symbol constraint UVar
addUVarValue x = do
    uv <- nextUVar
    modify' $ \s -> s{_uvarValues = _uvarValues s :|> UVarUnenumerated x Sequence.Empty}
    return uv

-- | Return the current representative for a UVar, updating union-find state.
getUVarRepresentative :: UVar -> EnumerateM symbol constraint UVar
getUVarRepresentative uv = do
    uf <- gets _uvarRepresentative
    let (uv', uf') = UnionFind.find uv uf
    modify' $ \s -> s{_uvarRepresentative = uf'}
    return uv'

-- | Look up the value for a UVar after path-compressing its representative.
getUVarValue :: UVar -> EnumerateM symbol constraint (UVarValue symbol constraint)
getUVarValue uv = do
    uv' <- getUVarRepresentative uv
    let idx = uvarToInt uv'
    values <- gets _uvarValues
    return $ Sequence.index values idx

{- | The fragment the root UVar holds, or the root hole itself.

An automaton that is a bare 'Mu' is never expanded - an unconstrained 'Mu' is
where enumeration stops - so its root stays a hole, exactly as a nested one
does.
-}
rootTermFrag :: EnumerateM symbol constraint (TermFragment symbol)
rootTermFrag = do
    value <- getUVarValue root
    return $ case value of
        UVarEnumerated fragment -> fragment
        _ -> TermFragmentUVar root
  where
    root = intToUVar 0

setUVarValue :: Int -> UVarValue symbol constraint -> EnumerateM symbol constraint ()
setUVarValue idx val =
    modify' $ \s -> s{_uvarValues = Sequence.update idx val (_uvarValues s)}

modifyUVarValue ::
    Int -> (UVarValue symbol constraint -> UVarValue symbol constraint) -> EnumerateM symbol constraint ()
modifyUVarValue idx f = do
    values <- gets _uvarValues
    setUVarValue idx (f (Sequence.index values idx))

---------------------
-------- Creating UVar's
---------------------

pecToSuspendedConstraint :: PathEClass -> EnumerateM symbol constraint SuspendedConstraint
pecToSuspendedConstraint pec = do
    uv <- addUVarValue Nothing
    return $ SuspendedConstraint (getPathTrie pec) uv

---------------------
-------- Merging UVar's / nodes
---------------------

-- | Merge the source UVar into the target UVar, intersecting their constraints.
assimilateUvarVal ::
    (Hashable symbol, Typeable symbol, Constraint constraint) => UVar -> UVar -> EnumerateM symbol constraint ()
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
mergeNodeIntoUVarVal ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    UVar -> Node symbol constraint -> Seq SuspendedConstraint -> EnumerateM symbol constraint ()
mergeNodeIntoUVarVal uv n scs = do
    uv' <- getUVarRepresentative uv
    let idx = uvarToInt uv'
    modifyUVarValue idx (intersectUVarValue (UVarUnenumerated (Just n) scs))
    newValues <- gets _uvarValues
    guard $ not $ hasEmptyContents $ Sequence.index newValues idx

-- | Whether an unenumerated variable has already reduced to the empty node.
hasEmptyContents :: UVarValue symbol constraint -> Bool
hasEmptyContents (UVarUnenumerated (Just EmptyNode) _) = True
hasEmptyContents _ = False

---------------------
-------- Core enumeration algorithm
---------------------

-- | Table for 'unconstrained'.
unconstrainedCache :: TypeableMemoCache
unconstrainedCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE unconstrainedCache #-}

{- | Whether no edge reachable from the node carries a constraint: no path
equality and no residual. Such an automaton is an ordinary tree automaton,
recursive or not.
-}
unconstrained :: (Typeable symbol, Constraint constraint) => Node symbol constraint -> Bool
unconstrained = memoTypeableWith unconstrainedCache $ getAll . crush free
  where
    free (Node es) = All (all (\e -> equalities (edgeConstraint e) == EmptyConstraints && not (residual (edgeConstraint e))) es)
    free _ = All True

-- | Enumerate one node under the suspended constraints currently in scope.
enumerateNode ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Seq SuspendedConstraint -> Node symbol constraint -> EnumerateM symbol constraint (TermFragment symbol)
enumerateNode _ EmptyNode = mzero
enumerateNode scs n =
    let (hereConstraints, descendantConstraints) = Sequence.partition (\(SuspendedConstraint pt _) -> isTerminalPathTrie pt) scs
     in case hereConstraints of
            Sequence.Empty -> case n of
                Mu _ -> TermFragmentUVar <$> addUVarValue (Just n)
                Node es -> enumerateEdge scs =<< lift es
                Rec recId ->
                    error $
                        "enumerateNode: unexpected unresolved recursive reference "
                            <> show recId
                            <> " for symbol type "
                            <> show (typeRep @symbol)
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
enumerateEdge ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Seq SuspendedConstraint -> Edge symbol constraint -> EnumerateM symbol constraint (TermFragment symbol)
enumerateEdge scs e = do
    -- With no constraints this is 'minBound', which passes the guard below,
    -- as it should: nothing constrains how many children the edge needs.
    let highestConstraintIndex = getMax $ foldMap (\sc -> Max $ fromMaybe (-1) $ getMaxNonemptyIndex $ scGetPathTrie sc) scs
    guard $ compareLength (edgeChildren e) highestConstraintIndex == GT

    newScs <- Sequence.fromList <$> mapM pecToSuspendedConstraint (unsafeGetEclasses $ equalities $ edgeConstraint e)
    let scs' = scs <> newScs
    fragment <-
        TermFragmentNode (edgeSymbol e) <$> zipWithM (\i n -> enumerateNode (descendScs i scs') n) [0 ..] (edgeChildren e)
    when (residual (edgeConstraint e)) $
        modify' $
            \s -> s{_obligations = (edgeConstraint e, fragment) : _obligations s}
    return fragment

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

{- | Find every expandable UVar in one pass over the value slots.

Slots merged into another UVar are marked 'UVarEliminated', so every live slot
is a representative and can be considered directly. Suspended constraints may
still name eliminated UVars; resolve only those references through the
union-find and write their path compression back once after the scan.

'Nothing' means no candidates remain. @Just empty@ means candidates exist, but
all of them are blocked by suspended constraints.
-}
findExpandableUVars :: EnumerateM symbol constraint (Maybe IntSet.IntSet)
findExpandableUVars = do
    values <- gets _uvarValues
    uf0 <- gets _uvarRepresentative
    let (candidates, ruledOut, uf) =
            Sequence.foldlWithIndex collect (IntSet.empty, IntSet.empty, uf0) values
    modify' $ \s -> s{_uvarRepresentative = uf}
    return $
        if IntSet.null candidates
            then Nothing
            else Just (candidates IntSet.\\ ruledOut)
  where
    collect (candidates, ruledOut, uf) i value = case value of
        UVarUnenumerated mbContents scs ->
            let (ruledOut', uf') = Foldable.foldl' resolve (ruledOut, uf) scs
                candidates' = case mbContents of
                    -- An unconstrained Mu is the recursive base case: expanding
                    -- it would unfold forever with nothing to stop it.
                    Just (InternedMu _)
                        | Sequence.null scs -> candidates
                    Just _ -> IntSet.insert i candidates
                    Nothing -> candidates
             in (candidates', ruledOut', uf')
        _ -> (candidates, ruledOut, uf)

    resolve (ruledOut, uf) sc =
        let (rep, uf') = UnionFind.find (scGetUVar sc) uf
         in (IntSet.insert (uvarToInt rep) ruledOut, uf')

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
firstExpandableUVar :: EnumerateM symbol constraint ExpandableUVarResult
firstExpandableUVar = nextExpandableUVar (const Nothing)

-- | 'firstExpandableUVar', letting the caller steer among the candidates.
nextExpandableUVar :: ([UVar] -> Maybe UVar) -> EnumerateM symbol constraint ExpandableUVarResult
nextExpandableUVar choose = do
    mbCandidates <- findExpandableUVars
    return $ case mbCandidates of
        Nothing -> ExpansionDone
        Just candidates
            | IntSet.null candidates -> ExpansionStuck
            | otherwise ->
                -- The candidate list is only forced if the caller looks at it,
                -- so the default order pays nothing for this.
                ExpansionNext $
                    case choose (map intToUVar $ IntSet.toAscList candidates) of
                        Just preferred
                            | IntSet.member (uvarToInt preferred) candidates ->
                                preferred
                        _ -> intToUVar (IntSet.findMin candidates)

{- | Expand one UVar into a fragment.

The pattern bind is deliberately failable: 'EnumerateM' fails into the list
monad, so a UVar that is not an unexpanded node drops this branch instead of
raising. The branch is unreachable through @enumerateFully'@ and
'enumerateOutFirstExpandableUVar', which only offer expandable UVars.
-}
enumerateOutUVar ::
    (Hashable symbol, Typeable symbol, Constraint constraint) => UVar -> EnumerateM symbol constraint (TermFragment symbol)
enumerateOutUVar uv =
    do
        UVarUnenumerated (Just n) scs <- getUVarValue uv
        uv' <- getUVarRepresentative uv

        t <- case n of
            Mu _ -> enumerateNode scs (unfoldOuterRec n)
            _ -> enumerateNode scs n

        setUVarValue (uvarToInt uv') (UVarEnumerated t)
        return t

-- | Expand the next available UVar, failing when enumeration is done or stuck.
enumerateOutFirstExpandableUVar ::
    (Hashable symbol, Typeable symbol, Constraint constraint) => EnumerateM symbol constraint ()
enumerateOutFirstExpandableUVar = do
    muv <- firstExpandableUVar
    case muv of
        ExpansionNext uv -> void $ enumerateOutUVar uv
        ExpansionDone -> mzero
        ExpansionStuck -> mzero

-- | Expand the root UVar until it represents a complete term.
enumerateFully :: (Hashable symbol, Typeable symbol, Constraint constraint) => EnumerateM symbol constraint ()
enumerateFully =
    void $ enumerateFully' () noExpansionPreference (\state _ _ -> return (False, state))

{- | Enumerate until the root term is complete, with optional oracle pruning.

The oracle is called twice around each UVar it expands:

* @Right node@ is passed before expanding the node, so callers can drop a
  whole branch early when the ECTA about to be expanded is already known to
  be uninteresting.
* @Left fragment@ is passed after expansion, together with the UVar it came
  from, so callers can reject the fragment or update their state before
  enumeration continues.

The threaded state parameter belongs entirely to the caller. Returning @True@
prunes the current nondeterministic branch; returning @False@ keeps it.

The 'ExpansionOrder' sees the same state and may steer which expandable UVar
goes next; 'noExpansionPreference' leaves that to the enumerator. A bare
unconstrained 'Mu' terminates enumeration without being expanded and produces
neither callback.
-}
enumerateFully' ::
    forall symbol constraint a.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    a ->
    ExpansionOrder a ->
    (a -> UVar -> Either (TermFragment symbol) (Node symbol constraint) -> EnumerateM symbol constraint (Bool, a)) ->
    EnumerateM symbol constraint Bool
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
enumeration is still in progress. Unexpanded UVars become 'UVarHole's, except a
recursive one with no suspended constraints, which is where enumeration stops
and which becomes 'TruncatedRecursion'.

A recursive node whose constraints have not been settled is still pending
expansion, so it is reported as a hole. An oracle that parks checks on holes
would otherwise read it as final and settle a check that has not been decided.
-}
expandPartialTermFrag :: TermFragment symbol -> EnumerateM symbol constraint (Tree.Tree (PartialSymbol symbol))
expandPartialTermFrag (TermFragmentNode symbol children) =
    Tree.Node (ConcreteSymbol symbol) <$> mapM expandPartialTermFrag children
expandPartialTermFrag (TermFragmentUVar uv) = do
    value <- getUVarValue uv
    case value of
        UVarEnumerated fragment -> expandPartialTermFrag fragment
        UVarUnenumerated (Just (InternedMu _)) Sequence.Empty -> return $ Tree.Node TruncatedRecursion []
        _ -> return $ Tree.Node (UVarHole uv) []

-- | Expand a complete term fragment into a concrete term.
expandTermFrag :: (IsString symbol) => TermFragment symbol -> EnumerateM symbol constraint (Tree.Tree symbol)
expandTermFrag = expandTermFragWith "Mu"

-- | 'expandTermFrag' with an explicit symbol for truncated recursion.
expandTermFragWith :: symbol -> TermFragment symbol -> EnumerateM symbol constraint (Tree.Tree symbol)
expandTermFragWith recursionSymbol = go
  where
    go (TermFragmentNode s ts) = Tree.Node s <$> mapM go ts
    go (TermFragmentUVar uv) = do
        val <- getUVarValue uv
        case val of
            UVarEnumerated t -> go t
            UVarUnenumerated (Just (InternedMu _)) _ -> return $ Tree.Node recursionSymbol []
            _ ->
                error "expandTermFrag: Non-recursive, unenumerated node encountered"

{- | Expand an enumerated UVar into a concrete term.

A UVar holding an unconstrained 'Mu' was never expanded, and truncates to the
same @Mu@ marker 'expandTermFrag' gives a nested one. Any other unenumerated
state is not reachable once enumeration reports itself finished, and drops the
branch rather than guessing.
-}
expandUVar :: (IsString symbol) => UVar -> EnumerateM symbol constraint (Tree.Tree symbol)
expandUVar = expandUVarWith "Mu"

expandUVarWith :: symbol -> UVar -> EnumerateM symbol constraint (Tree.Tree symbol)
expandUVarWith recursionSymbol uv = do
    value <- getUVarValue uv
    case value of
        UVarEnumerated fragment -> expandTermFragWith recursionSymbol fragment
        UVarUnenumerated (Just (InternedMu _)) _ -> return $ Tree.Node recursionSymbol []
        _ -> mzero

---------------------
-------- Full enumeration
---------------------

{- | Enumerate terms while retaining truncation explicitly.

Where 'terms' embeds a recursion marker into the caller's alphabet, this
uses 'TruncatedRecursion'. Any genuinely unresolved non-recursive variable remains
a 'UVarHole', as it does in 'expandPartialTermFrag'.
-}
truncatedTerms ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Node symbol constraint -> [Tree.Tree (PartialSymbol symbol)]
truncatedTerms n = map fst $
    flip runEnumerateM (initEnumerationState n) $ do
        enumerateFully
        rootTermFrag >>= expandPartialTermFrag

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
('expandPartialTermFrag'), and no notion of which shapes are interesting.

A check that cannot be settled because the fragment still holds an unexpanded
'TermFragmentUVar' does not need help from this module either. Park it in the
oracle's own state under that hole's representative
('getUVarRepresentative'), and settle it when the oracle is called with
@Left fragment@ for that UVar, which is guaranteed to happen before the branch
completes. 'termsPruneWith' can bring that moment forward.

Truncated recursion is reported as the @Mu@ marker in the caller's alphabet;
'termsPruneWith' takes that symbol explicitly, so an alphabet without an
'IsString' instance can prune too.
-}
termsPrune ::
    forall symbol constraint a.
    (Hashable symbol, Typeable symbol, Constraint constraint, IsString symbol) =>
    a ->
    (a -> UVar -> Either (TermFragment symbol) (Node symbol constraint) -> EnumerateM symbol constraint (Bool, a)) ->
    Node symbol constraint ->
    [Tree.Tree symbol]
termsPrune ost oracle = termsPruneWith "Mu" ost noExpansionPreference oracle

{- | 'termsPrune' with an explicit recursion symbol and a say in which
UVar is expanded next.

The first argument is the symbol standing for truncated recursion, as in
'termsWith'; taking it here rather than through 'IsString' is what lets
an ordinary datatype alphabet use the pruning API.

An oracle that parks checks on unexpanded holes can use the 'ExpansionOrder' to
reach those holes sooner: return the candidate the parked checks are waiting
on, and a branch that a check would kill dies before the rest of it is
enumerated.

This is a hint about order, not about which terms are enumerated. It cannot
make a UVar expandable early, and for an oracle whose rejections are monotone
- once a branch can be rejected it stays rejectable - it changes only how much
work is done. An oracle that decides differently depending on the order it
sees UVars in will, of course, see the difference.
-}
termsPruneWith ::
    forall symbol constraint a.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    symbol ->
    a ->
    ExpansionOrder a ->
    (a -> UVar -> Either (TermFragment symbol) (Node symbol constraint) -> EnumerateM symbol constraint (Bool, a)) ->
    Node symbol constraint ->
    [Tree.Tree symbol]
termsPruneWith recursionSymbol ost order oracle n =
    map fst $ flip runEnumerateM (initEnumerationState n) $ do
        finished <- enumerateFully' ost order oracle
        if finished then expandUVarWith recursionSymbol (intToUVar 0) else mzero

{- | The terms of the automaton's accepting runs, each once.

Path equalities are solved by unification. Enumeration stops at a recursive
binder and reports it as the marker term @Mu@ rather than unfolding it;
unfold first with 'unfoldBounded' to see past it, or use 'plainTerms' for
the lazy, depth-ordered listing of an automaton without constraints. An
acyclic automaton with no constraint anywhere is listed level by level
without the enumeration state. A constraint's residual beyond its equalities
is not decided here: use 'runs' to see it with the subterm it guards.

A constraint whose paths descend into a truncated recursive binder is dropped
rather than checked, so a result term containing the marker is not evidence
that the language below it is non-empty.
-}
terms ::
    (Hashable symbol, Ord symbol, Typeable symbol, Constraint constraint, IsString symbol) =>
    Node symbol constraint -> [Tree.Tree symbol]
terms = termsWith "Mu"

-- | 'terms' with an explicit symbol for truncated recursion.
termsWith ::
    (Hashable symbol, Ord symbol, Typeable symbol, Constraint constraint) =>
    symbol -> Node symbol constraint -> [Tree.Tree symbol]
termsWith recursionSymbol n
    | plain n = plainTerms n
    | otherwise = dedup $ map fst $ runsWith recursionSymbol n

{- | The term of every accepting run, with the residual constraints the run
must satisfy, each paired with the complete subterm it guards.

Runs are listed, not distinct terms: an ambiguous automaton yields a term
once per run, and a term is accepted when some run's obligations all hold.
An acyclic automaton with no constraint has no obligations and is listed
level by level as by 'terms'. The symbol stands for truncated recursion.
-}
runs ::
    (Hashable symbol, Ord symbol, Typeable symbol, Constraint constraint) =>
    symbol -> Node symbol constraint -> [(Tree.Tree symbol, [(constraint, Tree.Tree symbol)])]
runs recursionSymbol n
    | plain n = map (,[]) (plainTerms n)
    | otherwise = runsWith recursionSymbol n

-- | Whether the automaton is an acyclic ordinary tree automaton.
plain :: (Typeable symbol, Constraint constraint) => Node symbol constraint -> Bool
plain n = numNestedMu n == 0 && unconstrained n

runsWith ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    symbol -> Node symbol constraint -> [(Tree.Tree symbol, [(constraint, Tree.Tree symbol)])]
runsWith recursionSymbol n =
    map fst $ flip runEnumerateM (initEnumerationState n) $ do
        enumerateFully
        term <- expandUVarWith recursionSymbol (intToUVar 0)
        obligations <- gets _obligations
        pending <- mapM (\(constraint, fragment) -> (constraint,) <$> expandTermFragWith recursionSymbol fragment) obligations
        return (term, pending)

-- | Each term once, in the enumeration order of its first run.
dedup :: (Ord symbol) => [Tree.Tree symbol] -> [Tree.Tree symbol]
dedup = go Set.empty
  where
    go _ [] = []
    go seen (t : ts)
        | Set.member t seen = go seen ts
        | otherwise = t : go (Set.insert t seen) ts

{- | Every term of the underlying ordinary graph of a closed root, ordered by
depth, lazily. Constraints are not interpreted, each term appears once, and a
recursive graph gives an infinite list. See 'terms' for the constrained
listing.
-}
plainTerms ::
    (Hashable symbol, Ord symbol, Typeable symbol, Constraint constraint) => Node symbol constraint -> [Tree.Tree symbol]
plainTerms EmptyNode = []
plainTerms root =
    termsBy
        [ (ident, [(edgeSymbol edge, map nodeIdentity (edgeChildren edge)) | edge <- edges])
        | (ident, edges) <- IntMap.toList (reachable root)
        ]
        (nodeIdentity root)
