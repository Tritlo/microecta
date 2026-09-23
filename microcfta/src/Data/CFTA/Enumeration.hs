{-# LANGUAGE OverloadedStrings #-}

{- | Enumeration of constrained automata.

One enumerator serves every constraint theory. It builds 'TermFragment's
before expanding them to concrete @Tree.Tree@s. The path equalities of a
constraint ('equalities') are suspended obligations that point at UVars:
when enumeration descends through an edge, those obligations descend with
it, and when one reaches the node it names, the UVars are merged so future
choices stay consistent. A constraint with a 'residual' beyond its
equalities is recorded with the subterm it guards, and 'runs' hands those
pairs to the caller to decide. An automaton with no constraint and no
recursive binder is listed level by level without the enumeration state. A
cyclic one always uses the enumeration state, and enumeration stops at a
recursive binder. Only 'plainTerms' lists a cyclic graph without constraints,
as an infinite lazy list.

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
    plainTermsAtMost,
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
    EnumerateM,
) where

import Control.Monad (forM_, guard, mzero, unless, void, when, zipWithM)
import Control.Monad.State.Strict (StateT (..), gets, modify')
import Control.Monad.Trans.Class (lift)
import qualified Data.Foldable as Foldable
import Data.Hashable (Hashable (..))
import qualified Data.IntSet as IntSet
import Data.List (compareLength, genericTake)
import Data.Monoid (All (..))
import Data.Semigroup (Max (..))
import Data.Sequence (Seq ((:<|), (:|>)))
import qualified Data.Sequence as Sequence
import Data.String (IsString (..))
import qualified Data.Tree as Tree
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (Typeable, typeRep)

import Data.CFTA.Equality.Constraint (
    EqConstraints (EmptyConstraints),
    PathEClass (getPathTrie),
    PathTrie,
    getMaxNonemptyIndex,
    isEmptyPathTrie,
    isTerminalPathTrie,
    pathTrieDescend,
    unsafeGetEclasses,
 )
import Data.CFTA.Index (ChildIndex (..), Depth (..))
import Data.CFTA.Internal.Tree (termLevelsBy)
import Data.CFTA.Internal.UnionFind (UVar, UVarGen, UnionFind, intToUVar, uvarToInt)
import qualified Data.CFTA.Internal.UnionFind as UnionFind
import Data.CFTA.Interned
import Data.CFTA.Interned.Memo (TypeableMemoCache, memoTypeableWith, newTypeableMemoCache)
import qualified Data.HashSet as HashSet
import qualified Data.IntMap.Strict as IntMap

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
    = -- | A symbol from the automaton's alphabet.
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

---------------------------------------------------------------------------
------------------------------ Enumeration state --------------------------
---------------------------------------------------------------------------

-----------------------
------- Suspended constraints
-----------------------

-- | Equality obligation that has not yet reached the node it constrains.
data SuspendedConstraint = SuspendedConstraint !PathTrie !UVar
    deriving (Eq, Show)

-- | Remaining paths for a suspended equality obligation.
scGetPathTrie :: SuspendedConstraint -> PathTrie
scGetPathTrie (SuspendedConstraint pt _) = pt

-- | UVar that must be merged when the suspended obligation is reached.
scGetUVar :: SuspendedConstraint -> UVar
scGetUVar (SuspendedConstraint _ uv) = uv

-- | Push suspended obligations through child index @i@ and drop empty paths.
descendScs :: ChildIndex -> Seq SuspendedConstraint -> Seq SuspendedConstraint
descendScs i scs =
    Sequence.filter (not . isEmptyPathTrie . scGetPathTrie) $
        fmap
            (\(SuspendedConstraint pt uv) -> SuspendedConstraint (pathTrieDescend pt i) uv)
            scs

-----------------------
------- UVarValue
-----------------------

-- | Enumeration status for one UVar.
data UVarValue symbol
    = -- | UVar still has a node to expand.
      UVarUnenumerated
        -- | Node still to enumerate, or 'Nothing' for pure constraint variables.
        !(Maybe (Node symbol))
        -- | Constraints that should be carried while enumerating this value.
        !(Seq SuspendedConstraint)
    | -- | UVar has been expanded to a fragment.
      UVarEnumerated !(TermFragment symbol)
    | -- | UVar was merged into another representative and should no longer be used.
      UVarEliminated
    deriving (Eq, Show)

intersectUVarValue ::
    (Hashable symbol, Typeable symbol) =>
    UVarValue symbol -> UVarValue symbol -> UVarValue symbol
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
data EnumerationState symbol = EnumerationState
    { _uvarCounter :: UVarGen
    -- ^ Fresh UVar supply.
    , _uvarRepresentative :: UnionFind
    -- ^ Persistent union-find for equality-constrained UVars.
    , _uvarValues :: Seq (UVarValue symbol)
    {- ^ Per-UVar contents indexed by 'uvarToInt'. A slot is
    'UVarEliminated' exactly when its UVar is not a representative;
    @findExpandableUVars@ relies on 'assimilateUvarVal' maintaining this.
    -}
    , _obligations :: [(Constraint, TermFragment symbol)]
    -- ^ Constraints with a 'residual', each with the fragment it guards.
    , _recursionAncestry :: IntMap.IntMap RecursionAncestry
    {- ^ For each UVar that the expansion of a constrained recursive node
    reached, directly or through later expansions, the keys of those
    expansions.
    -}
    , _expansionAncestry :: RecursionAncestry
    -- ^ The ancestry that the current expansion gives the UVars it reaches.
    }
    deriving (Eq, Show)

{- | The expansions of constrained recursive nodes that a UVar descends from,
each as its 'recursionKey'.
-}
type RecursionAncestry = HashSet.HashSet (NodeId, HashSet.HashSet PathTrie)

{- | A recursive node with the paths suspended on it. Two expansions with one
key differ only in their UVars.
-}
recursionKey :: Node symbol -> Seq SuspendedConstraint -> (NodeId, HashSet.HashSet PathTrie)
recursionKey n scs = (nodeIdentity n, HashSet.fromList $ map scGetPathTrie $ Foldable.toList scs)

-- | Initial state whose root UVar contains the node being enumerated.
initEnumerationState :: Node symbol -> EnumerationState symbol
initEnumerationState n =
    let (uvg, uv) = UnionFind.nextUVar UnionFind.initUVarGen
     in EnumerationState
            uvg
            (UnionFind.withInitialValues [uv])
            (Sequence.singleton (UVarUnenumerated (Just n) Sequence.Empty))
            []
            IntMap.empty
            HashSet.empty

---------------------------------------------------------------------------
---------------------------- Enumeration monad ----------------------------
---------------------------------------------------------------------------

---------------------
-------- Monad
---------------------

-- | Nondeterministic enumeration state monad.
type EnumerateM symbol = StateT (EnumerationState symbol) []

-- | Run a lower-level enumeration action from an explicit state.
runEnumerateM ::
    EnumerateM symbol a -> EnumerationState symbol -> [(a, EnumerationState symbol)]
runEnumerateM = runStateT

---------------------
-------- UVar accessors
---------------------

nextUVar :: EnumerateM symbol UVar
nextUVar = do
    c <- gets _uvarCounter
    let (c', uv) = UnionFind.nextUVar c
    modify' $ \s -> s{_uvarCounter = c'}
    return uv

addUVarValue :: Maybe (Node symbol) -> EnumerateM symbol UVar
addUVarValue x = do
    uv <- nextUVar
    modify' $ \s -> s{_uvarValues = _uvarValues s :|> UVarUnenumerated x Sequence.Empty}
    inheritAncestry (uvarToInt uv)
    return uv

-- | Give one UVar the ancestry of the current expansion.
inheritAncestry :: Int -> EnumerateM symbol ()
inheritAncestry idx = do
    current <- gets _expansionAncestry
    unless (HashSet.null current) $
        modify' $
            \s -> s{_recursionAncestry = IntMap.insertWith HashSet.union idx current (_recursionAncestry s)}

-- | Return the current representative for a UVar, updating union-find state.
getUVarRepresentative :: UVar -> EnumerateM symbol UVar
getUVarRepresentative uv = do
    uf <- gets _uvarRepresentative
    let (uv', uf') = UnionFind.find uv uf
    modify' $ \s -> s{_uvarRepresentative = uf'}
    return uv'

-- | Look up the value for a UVar after path-compressing its representative.
getUVarValue :: UVar -> EnumerateM symbol (UVarValue symbol)
getUVarValue uv = do
    uv' <- getUVarRepresentative uv
    let idx = uvarToInt uv'
    values <- gets _uvarValues
    return $ Sequence.index values idx

{- | The fragment the root UVar holds, or the root hole itself.

An automaton that is a bare 'Mu' is never expanded, because an unconstrained
'Mu' is where enumeration stops. Its root stays a hole, exactly as a nested one
does.
-}
rootTermFrag :: EnumerateM symbol (TermFragment symbol)
rootTermFrag = do
    value <- getUVarValue root
    return $ case value of
        UVarEnumerated fragment -> fragment
        _ -> TermFragmentUVar root
  where
    root = intToUVar 0

setUVarValue :: Int -> UVarValue symbol -> EnumerateM symbol ()
setUVarValue idx val =
    modify' $ \s -> s{_uvarValues = Sequence.update idx val (_uvarValues s)}

modifyUVarValue ::
    Int -> (UVarValue symbol -> UVarValue symbol) -> EnumerateM symbol ()
modifyUVarValue idx f = do
    values <- gets _uvarValues
    setUVarValue idx (f (Sequence.index values idx))

---------------------
-------- Creating UVar's
---------------------

pecToSuspendedConstraint :: PathEClass -> EnumerateM symbol SuspendedConstraint
pecToSuspendedConstraint pec = do
    uv <- addUVarValue Nothing
    return $ SuspendedConstraint (getPathTrie pec) uv

---------------------
-------- Merging UVar's / nodes
---------------------

-- | Merge the source UVar into the target UVar, intersecting their constraints.
assimilateUvarVal ::
    (Hashable symbol, Typeable symbol) => UVar -> UVar -> EnumerateM symbol ()
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
                modify' $ \s -> case IntMap.lookup (uvarToInt uvSrc) (_recursionAncestry s) of
                    Nothing -> s
                    Just ancestry -> s{_recursionAncestry = IntMap.insertWith HashSet.union (uvarToInt uvTarg) ancestry (_recursionAncestry s)}

-- | Intersect a node and inherited constraints into the value for a UVar.
mergeNodeIntoUVarVal ::
    (Hashable symbol, Typeable symbol) =>
    UVar -> Node symbol -> Seq SuspendedConstraint -> EnumerateM symbol ()
mergeNodeIntoUVarVal uv n scs = do
    uv' <- getUVarRepresentative uv
    let idx = uvarToInt uv'
    modifyUVarValue idx (intersectUVarValue (UVarUnenumerated (Just n) scs))
    inheritAncestry idx
    newValues <- gets _uvarValues
    guard $ not $ hasEmptyContents $ Sequence.index newValues idx

-- | Whether an unenumerated variable has already reduced to the empty node.
hasEmptyContents :: UVarValue symbol -> Bool
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
unconstrained :: forall symbol. (Typeable symbol) => Node symbol -> Bool
unconstrained = memoTypeableWith @symbol unconstrainedCache $ getAll . crush free
  where
    free (Node es) = All (all (\e -> equalities (edgeConstraint e) == EmptyConstraints && not (residual (edgeConstraint e))) es)
    free _ = All True

-- | Enumerate one node under the suspended constraints currently in scope.
enumerateNode ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    Seq SuspendedConstraint -> Node symbol -> EnumerateM symbol (TermFragment symbol)
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
    (Hashable symbol, Typeable symbol) =>
    Seq SuspendedConstraint -> Edge symbol -> EnumerateM symbol (TermFragment symbol)
enumerateEdge scs e = do
    -- With no constraints this is 'minBound', which passes the guard below,
    -- as it should: nothing constrains how many children the edge needs.
    let highestConstraintIndex =
            getMax $ foldMap (\sc -> Max $ maybe (-1) (\(ChildIndex index) -> index) $ getMaxNonemptyIndex $ scGetPathTrie sc) scs
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
findExpandableUVars :: EnumerateM symbol (Maybe IntSet.IntSet)
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

Steering is worth it when the caller waits on a particular hole, one whose
expansion settles a check parked in the oracle's own state. The caller then
resolves that hole first, instead of enumerating the rest of a branch that the
check rejects.
At one step, it cannot change which UVars are expandable. It can only choose
which of them goes first.
-}
type ExpansionOrder state = state -> [UVar] -> Maybe UVar

-- | The 'ExpansionOrder' that always leaves the choice to the enumerator.
noExpansionPreference :: ExpansionOrder state
noExpansionPreference _ _ = Nothing

-- | Find the next UVar that can be expanded without violating dependencies.
nextExpandableUVar :: ([UVar] -> Maybe UVar) -> EnumerateM symbol ExpandableUVarResult
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
raising. The branch is unreachable through @enumerateFully'@, which takes its
UVar from 'nextExpandableUVar' and so only offers expandable UVars.
-}
enumerateOutUVar ::
    (Hashable symbol, Typeable symbol) => UVar -> EnumerateM symbol (TermFragment symbol)
enumerateOutUVar uv =
    do
        UVarUnenumerated (Just n) scs <- getUVarValue uv
        uv' <- getUVarRepresentative uv
        ancestry <- gets $ IntMap.findWithDefault HashSet.empty (uvarToInt uv') . _recursionAncestry
        modify' $ \s ->
            s
                { _expansionAncestry = case n of
                    Mu _ -> HashSet.insert (recursionKey n scs) ancestry
                    _ -> ancestry
                }

        t <- case n of
            Mu _ -> enumerateNode scs (unfoldOuterRec n)
            _ -> enumerateNode scs n

        modify' $ \s -> s{_expansionAncestry = HashSet.empty}
        setUVarValue (uvarToInt uv') (UVarEnumerated t)
        return t

-- | Expand the root UVar until it represents a complete term.
enumerateFully :: (Hashable symbol, Typeable symbol) => EnumerateM symbol ()
enumerateFully =
    void $ enumerateFully' () noExpansionPreference (\state _ _ -> return (False, state))

{- | Enumerate until the root term is complete, with optional oracle pruning.

The oracle is called twice around each UVar it expands:

* @Right node@ is passed before expanding the node, so callers can drop a
  whole branch early when the node about to be expanded is already known to
  be uninteresting.
* @Left fragment@ is passed after expansion, together with the UVar it came
  from, so callers can reject the fragment or update their state before
  enumeration continues.

The threaded state parameter belongs entirely to the caller. Returning @True@
prunes the current nondeterministic branch; returning @False@ keeps it.

The 'ExpansionOrder' sees the same state and may steer which expandable UVar
goes next; 'noExpansionPreference' leaves that to the enumerator. An
unconstrained 'Mu' is never offered for expansion, so it is not expanded and
produces neither callback. Enumeration ends when no other UVar can be expanded.
-}
enumerateFully' ::
    forall symbol a.
    (Hashable symbol, Typeable symbol) =>
    a ->
    ExpansionOrder a ->
    (a -> UVar -> Either (TermFragment symbol) (Node symbol) -> EnumerateM symbol (Bool, a)) ->
    EnumerateM symbol Bool
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
                expand n = do
                    (should_prune, ost') <- oracle ost uv (Right n)
                    if should_prune then mzero else continue ost'
             in do
                    UVarUnenumerated (Just n) scs <- getUVarValue uv
                    case n of
                        Mu _ | scs == Sequence.empty -> return True
                        Mu _ -> do
                            uv' <- getUVarRepresentative uv
                            ancestry <- gets $ IntMap.findWithDefault HashSet.empty (uvarToInt uv') . _recursionAncestry
                            if HashSet.member (recursionKey n scs) ancestry
                                then do
                                    -- The expansion of this node with these paths led to it
                                    -- again, so each further expansion repeats the last one.
                                    -- Enumeration stops here, as at an unconstrained 'Mu'.
                                    setUVarValue (uvarToInt uv') (UVarUnenumerated (Just n) Sequence.Empty)
                                    enumerateFully' ost order oracle
                                else expand n
                        _ -> expand n

---------------------
-------- Expanding an enumerated term fragment into a term
---------------------

{- | Expand a fragment even if it still contains unenumerated UVars.

Unlike 'expandTermFragWith', which fails on an unenumerated non-recursive node,
this is safe for diagnostics and oracle logging while enumeration is still in
progress. Unexpanded UVars become 'UVarHole's, except a recursive one with no
suspended constraints, which is where enumeration stops and which becomes
'TruncatedRecursion'. A recursive node whose constraints have not been settled
is still pending expansion, so it is reported as a hole. An oracle that parks
checks on holes would otherwise read it as final and settle a check that has not
been decided.
-}
expandPartialTermFrag :: TermFragment symbol -> EnumerateM symbol (Tree.Tree (PartialSymbol symbol))
expandPartialTermFrag (TermFragmentNode symbol children) =
    Tree.Node (ConcreteSymbol symbol) <$> mapM expandPartialTermFrag children
expandPartialTermFrag (TermFragmentUVar uv) = do
    value <- getUVarValue uv
    case value of
        UVarEnumerated fragment -> expandPartialTermFrag fragment
        UVarUnenumerated (Just (InternedMu _)) Sequence.Empty -> return $ Tree.Node TruncatedRecursion []
        _ -> return $ Tree.Node (UVarHole uv) []

-- | Expand a complete term fragment into a concrete term, with the symbol that stands for truncated recursion.
expandTermFragWith :: symbol -> TermFragment symbol -> EnumerateM symbol (Tree.Tree symbol)
expandTermFragWith recursionSymbol = go
  where
    go (TermFragmentNode s ts) = Tree.Node s <$> mapM go ts
    go (TermFragmentUVar uv) = do
        val <- getUVarValue uv
        case val of
            UVarEnumerated t -> go t
            UVarUnenumerated (Just (InternedMu _)) _ -> return $ Tree.Node recursionSymbol []
            _ ->
                error "expandTermFragWith: Non-recursive, unenumerated node encountered"

{- | Expand an enumerated UVar into a concrete term.

A UVar holding an unconstrained 'Mu' was never expanded, and truncates to the
same marker 'expandTermFragWith' gives a nested one. Any other unenumerated
state is not reachable once enumeration reports itself finished, and drops the
branch rather than guessing.
-}
expandUVarWith :: symbol -> UVar -> EnumerateM symbol (Tree.Tree symbol)
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
    (Hashable symbol, Typeable symbol) =>
    Node symbol -> [Tree.Tree (PartialSymbol symbol)]
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

The caller decides which terms to reject. This library supplies the callbacks
and the means to read a partial term ('expandPartialTermFrag'). It has no
notion of which shapes are interesting.

A check that cannot be settled because the fragment still holds an unexpanded
'TermFragmentUVar' does not need help from this module either. Park it in the
oracle's own state under that hole's UVar. The oracle is called with
@Left fragment@ for every UVar that enumeration expands, and that UVar is always
a current representative. Enumeration can merge a parked UVar into another one,
and then no call names the parked UVar. So at each call, look up the current
representative of each parked UVar with 'getUVarRepresentative', and settle the
checks whose representative is the UVar of the call. A UVar that holds an
unconstrained 'Mu' gets no call. 'termsPruneWith' can bring a call forward.

Truncated recursion is reported as the @Mu@ marker in the caller's alphabet;
'termsPruneWith' takes that symbol explicitly, so an alphabet without an
'IsString' instance can prune too.
-}
termsPrune ::
    forall symbol a.
    (Hashable symbol, Typeable symbol, IsString symbol) =>
    a ->
    (a -> UVar -> Either (TermFragment symbol) (Node symbol) -> EnumerateM symbol (Bool, a)) ->
    Node symbol ->
    [Tree.Tree symbol]
termsPrune ost oracle = termsPruneWith "Mu" ost noExpansionPreference oracle

{- | 'termsPrune' with an explicit recursion symbol and control over which
UVar is expanded next.

The first argument is the symbol standing for truncated recursion, as in
'termsWith'. The symbol is passed here, not through 'IsString', so an ordinary
datatype alphabet can use the pruning API.

An oracle that parks checks on unexpanded holes can use the 'ExpansionOrder' to
reach those holes sooner: return the candidate the parked checks are waiting
on, and a branch that a check rejects ends before the rest of it is
enumerated.

This is a hint about order, not about which terms are enumerated. It cannot
make a UVar expandable early. For an oracle whose rejections are monotone (a
branch that can be rejected stays rejectable), it changes only how much work is
done. An oracle that decides differently depending on the order in which it
sees UVars sees the difference.
-}
termsPruneWith ::
    forall symbol a.
    (Hashable symbol, Typeable symbol) =>
    symbol ->
    a ->
    ExpansionOrder a ->
    (a -> UVar -> Either (TermFragment symbol) (Node symbol) -> EnumerateM symbol (Bool, a)) ->
    Node symbol ->
    [Tree.Tree symbol]
termsPruneWith recursionSymbol ost order oracle n =
    map fst $ flip runEnumerateM (initEnumerationState n) $ do
        finished <- enumerateFully' ost order oracle
        if finished then expandUVarWith recursionSymbol (intToUVar 0) else mzero

{- | The terms of the automaton's accepting runs, each once.

Path equalities are solved by unification. Enumeration stops at a recursive
binder and reports it as the marker term @Mu@ rather than unfolding it;
bound the depth first with 'boundDepth' to see past it, or use 'plainTerms'
and 'plainTermsAtMost' for the depth-ordered listing of an automaton without
constraints. An acyclic automaton with no constraint anywhere is listed level
by level without the enumeration state. A constraint's residual beyond its equalities
is not decided here: use 'runs' to see it with the subterm it guards.

A constraint whose paths descend into a truncated recursive binder is dropped
rather than checked, so a result term containing the marker is not evidence
that the language below it is non-empty.
-}
terms ::
    (Hashable symbol, Ord symbol, Typeable symbol, IsString symbol) =>
    Node symbol -> [Tree.Tree symbol]
terms = termsWith "Mu"

-- | 'terms' with an explicit symbol for truncated recursion.
termsWith ::
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    symbol -> Node symbol -> [Tree.Tree symbol]
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
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    symbol -> Node symbol -> [(Tree.Tree symbol, [(Constraint, Tree.Tree symbol)])]
runs recursionSymbol n
    | plain n = map (,[]) (plainTerms n)
    | otherwise = runsWith recursionSymbol n

-- | Whether the automaton is an acyclic ordinary tree automaton.
plain :: (Typeable symbol) => Node symbol -> Bool
plain n = numNestedMu n == 0 && unconstrained n

runsWith ::
    (Hashable symbol, Typeable symbol) =>
    symbol -> Node symbol -> [(Tree.Tree symbol, [(Constraint, Tree.Tree symbol)])]
runsWith recursionSymbol n =
    map fst $ flip runEnumerateM (initEnumerationState n) $ do
        enumerateFully
        term <- expandUVarWith recursionSymbol (intToUVar 0)
        obligations <- gets _obligations
        pending <- mapM (\(constraint, fragment) -> (constraint,) <$> expandTermFragWith recursionSymbol fragment) obligations
        return (term, pending)

-- | Each term once, in the enumeration order of its first run. The order is kept, unlike a set.
dedup :: (Hashable symbol) => [Tree.Tree symbol] -> [Tree.Tree symbol]
dedup = go HashSet.empty
  where
    go _ [] = []
    go seen (t : ts)
        | HashSet.member t seen = go seen ts
        | otherwise = t : go (HashSet.insert t seen) ts

{- | Every term of the underlying ordinary graph of a closed root, ordered by
depth, lazily. Constraints are not interpreted, each term appears once, and a
recursive graph gives an infinite list. See 'terms' for the constrained
listing.
-}
plainTerms ::
    (Hashable symbol, Ord symbol, Typeable symbol) => Node symbol -> [Tree.Tree symbol]
plainTerms = concat . plainTermLevels

{- | The terms of 'plainTerms' whose leaves are at most the given depth from
the root. A leaf has depth zero, and a negative depth gives no terms. The
deeper terms are never built, so a recursive graph gives a finite list.
-}
plainTermsAtMost ::
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    Depth -> Node symbol -> [Tree.Tree symbol]
plainTermsAtMost (Depth depth) = concat . genericTake (toInteger depth + 1) . plainTermLevels

-- | The terms of the underlying ordinary graph, grouped by depth.
plainTermLevels ::
    (Hashable symbol, Ord symbol, Typeable symbol) => Node symbol -> [[Tree.Tree symbol]]
plainTermLevels EmptyNode = []
plainTermLevels root =
    termLevelsBy
        [ (NodeId ident, [(edgeSymbol edge, map nodeIdentity (edgeChildren edge)) | edge <- edges])
        | (ident, edges) <- IntMap.toList (reachable root)
        ]
        (nodeIdentity root)
