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
    PartialSymbol (..),
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
    rootTermFrag,
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
    expandTermFragWith,
    expandPartialTermFrag,
    expandUVar,
    getAllTruncatedTerms,
    getAllTerms,
    getAllTermsWith,
    getAllTermsPrune,
    getAllTermsPruneWith,
    enumPrune,
    enumPruneWith,
) where

import Control.Monad (forM_, guard, mzero, void, zipWithM)
import Control.Monad.State.Strict (StateT (..), gets, modify')
import Control.Monad.Trans.Class (lift)
import qualified Data.Foldable as Foldable
import Data.Hashable (Hashable (..))
import qualified Data.IntSet as IntSet
import Data.Maybe (fromMaybe)
import Data.Semigroup (Max (..))
import Data.Sequence (Seq ((:<|), (:|>)))
import qualified Data.Sequence as Sequence
import Data.String (IsString (..))
import Type.Reflection (Typeable, typeRep)

import Data.ECTA.Internal.ECTA.Operations
import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Paths
import Data.ECTA.Term
import Data.Persistent.UnionFind (UVar, UVarGen, UnionFind, intToUVar, uvarToInt)
import qualified Data.Persistent.UnionFind as UnionFind

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
mistaken for a rendered placeholder such as @v0@. 'TruncatedRecursion' records an
unconstrained recursive node when the enumeration state is available to
identify it.
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
termFragToTruncatedTerm :: TermFragment symbol -> Term (PartialSymbol symbol)
termFragToTruncatedTerm (TermFragmentNode symbol children) =
    Term (ConcreteSymbol symbol) (map termFragToTruncatedTerm children)
termFragToTruncatedTerm (TermFragmentUVar uv) = Term (UVarHole uv) []

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
data UVarValue symbol
    = -- | UVar still has an ECTA node to expand.
      UVarUnenumerated
        -- | ECTA node still to enumerate, or 'Nothing' for pure constraint variables.
        !(Maybe (Node symbol))
        -- | Constraints that should be carried while enumerating this value.
        !(Seq SuspendedConstraint)
    | -- | UVar has been expanded to a fragment.
      UVarEnumerated !(TermFragment symbol)
    | -- | UVar was merged into another representative and should no longer be used.
      UVarEliminated
    deriving (Eq, Ord, Show)

intersectUVarValue :: (Hashable symbol, Typeable symbol) => UVarValue symbol -> UVarValue symbol -> UVarValue symbol
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
data EnumerationState symbol = EnumerationState
    { _uvarCounter :: UVarGen
    -- ^ Fresh UVar supply.
    , _uvarRepresentative :: UnionFind
    -- ^ Persistent union-find for equality-constrained UVars.
    , _uvarValues :: Seq (UVarValue symbol)
    {- ^ Per-UVar contents indexed by 'uvarToInt'. A slot is
    'UVarEliminated' exactly when its UVar is not a representative;
    'findExpandableUVars' relies on 'assimilateUvarVal' maintaining this.
    -}
    }
    deriving (Eq, Ord, Show)

-- | Lens-compatible accessor for the fresh UVar supply.
uvarCounter :: (Functor f) => (UVarGen -> f UVarGen) -> EnumerationState symbol -> f (EnumerationState symbol)
uvarCounter = lens _uvarCounter (\s c -> s{_uvarCounter = c})

-- | Lens-compatible accessor for representative UVar tracking.
uvarRepresentative :: (Functor f) => (UnionFind -> f UnionFind) -> EnumerationState symbol -> f (EnumerationState symbol)
uvarRepresentative = lens _uvarRepresentative (\s uf -> s{_uvarRepresentative = uf})

-- | Lens-compatible accessor for per-UVar enumeration values.
uvarValues :: (Functor f) => (Seq (UVarValue symbol) -> f (Seq (UVarValue symbol))) -> EnumerationState symbol -> f (EnumerationState symbol)
uvarValues = lens _uvarValues (\s vals -> s{_uvarValues = vals})

-- | Initial state whose root UVar contains the node being enumerated.
initEnumerationState :: Node symbol -> EnumerationState symbol
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
type EnumerateM symbol = StateT (EnumerationState symbol) []

-- | Run a lower-level enumeration action from an explicit state.
runEnumerateM :: EnumerateM symbol a -> EnumerationState symbol -> [(a, EnumerationState symbol)]
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
    return uv

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

An automaton that is a bare 'Mu' is never expanded - an unconstrained 'Mu' is
where enumeration stops - so its root stays a hole, exactly as a nested one
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

modifyUVarValue :: Int -> (UVarValue symbol -> UVarValue symbol) -> EnumerateM symbol ()
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
assimilateUvarVal :: (Hashable symbol, Typeable symbol) => UVar -> UVar -> EnumerateM symbol ()
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
mergeNodeIntoUVarVal :: (Hashable symbol, Typeable symbol) => UVar -> Node symbol -> Seq SuspendedConstraint -> EnumerateM symbol ()
mergeNodeIntoUVarVal uv n scs = do
    uv' <- getUVarRepresentative uv
    let idx = uvarToInt uv'
    modifyUVarValue idx (intersectUVarValue (UVarUnenumerated (Just n) scs))
    newValues <- gets _uvarValues
    guard $ not $ hasEmptyContents $ Sequence.index newValues idx

-- | Whether an unenumerated variable has already reduced to the empty node.
hasEmptyContents :: UVarValue symbol -> Bool
hasEmptyContents (UVarUnenumerated (Just EmptyNode) _) = True
hasEmptyContents _ = False

---------------------
-------- Core enumeration algorithm
---------------------

-- | Enumerate one node under the suspended constraints currently in scope.
enumerateNode :: forall symbol. (Hashable symbol, Typeable symbol) => Seq SuspendedConstraint -> Node symbol -> EnumerateM symbol (TermFragment symbol)
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
enumerateEdge :: (Hashable symbol, Typeable symbol) => Seq SuspendedConstraint -> Edge symbol -> EnumerateM symbol (TermFragment symbol)
enumerateEdge scs e = do
    -- With no constraints this is 'minBound', which passes the guard below,
    -- as it should: nothing constrains how many children the edge needs.
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
firstExpandableUVar :: EnumerateM symbol ExpandableUVarResult
firstExpandableUVar = nextExpandableUVar (const Nothing)

-- | 'firstExpandableUVar', letting the caller steer among the candidates.
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
raising. The branch is unreachable through 'enumerateFully'' and
'enumerateOutFirstExpandableUVar', which only offer expandable UVars.
-}
enumerateOutUVar :: (Hashable symbol, Typeable symbol) => UVar -> EnumerateM symbol (TermFragment symbol)
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
enumerateOutFirstExpandableUVar :: (Hashable symbol, Typeable symbol) => EnumerateM symbol ()
enumerateOutFirstExpandableUVar = do
    muv <- firstExpandableUVar
    case muv of
        ExpansionNext uv -> void $ enumerateOutUVar uv
        ExpansionDone -> mzero
        ExpansionStuck -> mzero

-- | Expand the root UVar until it represents a complete term.
enumerateFully :: (Hashable symbol, Typeable symbol) => EnumerateM symbol ()
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
'UVarHole's, and recursive continuations become 'TruncatedRecursion'.
-}
expandPartialTermFrag :: TermFragment symbol -> EnumerateM symbol (Term (PartialSymbol symbol))
expandPartialTermFrag (TermFragmentNode symbol children) =
    Term (ConcreteSymbol symbol) <$> mapM expandPartialTermFrag children
expandPartialTermFrag (TermFragmentUVar uv) = do
    value <- getUVarValue uv
    case value of
        UVarEnumerated fragment -> expandPartialTermFrag fragment
        UVarUnenumerated (Just (InternedMu _)) _ -> return $ Term TruncatedRecursion []
        _ -> return $ Term (UVarHole uv) []

-- | Expand a complete term fragment into a concrete term.
expandTermFrag :: (IsString symbol) => TermFragment symbol -> EnumerateM symbol (Term symbol)
expandTermFrag = expandTermFragWith "Mu"

-- | 'expandTermFrag' with an explicit symbol for truncated recursion.
expandTermFragWith :: symbol -> TermFragment symbol -> EnumerateM symbol (Term symbol)
expandTermFragWith recursionSymbol = go
  where
    go (TermFragmentNode s ts) = Term s <$> mapM go ts
    go (TermFragmentUVar uv) = do
        val <- getUVarValue uv
        case val of
            UVarEnumerated t -> go t
            UVarUnenumerated (Just (InternedMu _)) _ -> return $ Term recursionSymbol []
            _ ->
                error "expandTermFrag: Non-recursive, unenumerated node encountered"

{- | Expand an enumerated UVar into a concrete term.

A UVar holding an unconstrained 'Mu' was never expanded, and truncates to the
same @Mu@ marker 'expandTermFrag' gives a nested one. Any other unenumerated
state is not reachable once enumeration reports itself finished, and drops the
branch rather than guessing.
-}
expandUVar :: (IsString symbol) => UVar -> EnumerateM symbol (Term symbol)
expandUVar = expandUVarWith "Mu"

expandUVarWith :: symbol -> UVar -> EnumerateM symbol (Term symbol)
expandUVarWith recursionSymbol uv = do
    value <- getUVarValue uv
    case value of
        UVarEnumerated fragment -> expandTermFragWith recursionSymbol fragment
        UVarUnenumerated (Just (InternedMu _)) _ -> return $ Term recursionSymbol []
        _ -> mzero

---------------------
-------- Full enumeration
---------------------

{- | Enumerate terms while retaining truncation explicitly.

Where 'getAllTerms' embeds a recursion marker into the caller's alphabet, this
uses 'TruncatedRecursion'. Any genuinely unresolved non-recursive variable remains
a 'UVarHole', as it does in 'expandPartialTermFrag'.
-}
getAllTruncatedTerms :: (Hashable symbol, Typeable symbol) => Node symbol -> [Term (PartialSymbol symbol)]
getAllTruncatedTerms n = map fst $
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
completes. 'getAllTermsPruneWith' can bring that moment forward.
-}
getAllTermsPrune ::
    forall symbol a.
    (Hashable symbol, Typeable symbol, IsString symbol) =>
    a ->
    (a -> UVar -> Either (TermFragment symbol) (Node symbol) -> EnumerateM symbol (Bool, a)) ->
    Node symbol ->
    [Term symbol]
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
    forall symbol a.
    (Hashable symbol, Typeable symbol, IsString symbol) =>
    a ->
    ExpansionOrder a ->
    (a -> UVar -> Either (TermFragment symbol) (Node symbol) -> EnumerateM symbol (Bool, a)) ->
    Node symbol ->
    [Term symbol]
getAllTermsPruneWith ost order oracle n =
    map fst $ flip runEnumerateM (initEnumerationState n) $ enumPruneWith ost order oracle

{- | Monadic form of 'getAllTermsPrune'.

Use this when the caller is already composing lower-level enumeration actions
in 'EnumerateM'. Most callers should prefer 'getAllTermsPrune'.
-}
enumPrune :: forall symbol a. (Hashable symbol, Typeable symbol, IsString symbol) => a -> (a -> UVar -> Either (TermFragment symbol) (Node symbol) -> EnumerateM symbol (Bool, a)) -> EnumerateM symbol (Term symbol)
enumPrune a = enumPruneWith a noExpansionPreference

-- | Monadic form of 'getAllTermsPruneWith'.
enumPruneWith ::
    forall symbol a.
    (Hashable symbol, Typeable symbol, IsString symbol) =>
    a ->
    ExpansionOrder a ->
    (a -> UVar -> Either (TermFragment symbol) (Node symbol) -> EnumerateM symbol (Bool, a)) ->
    EnumerateM symbol (Term symbol)
enumPruneWith a order oracle = do
    finished <- enumerateFully' a order oracle
    if finished then expandUVar (intToUVar 0) else mzero

{- | Enumerate the terms an ECTA accepts, truncating at recursion.

Enumeration stops at an unconstrained 'Mu', which appears in the result as the
marker term @Mu@ rather than being unfolded. Every term of a finite automaton
is therefore enumerated, but a recursive one yields only terms in which each
recursive position is that marker - and an automaton that is /itself/ a bare
'Mu', as @createMu@ returns, yields exactly @[Mu]@.

To see past the recursion, unfold it first with 'unfoldBounded', or read the
automaton with @microecta-generator@'s @fromECTA@, which counts and enumerates
a recursive language by size.

Two caveats. Enumeration lists accepting /runs/, not distinct terms, so an
ambiguous node - two edges that accept a common term - yields that term once
per edge. Use 'withoutRedundantEdges' first, or deduplicate the result, if you
need each term once. And a constraint whose paths descend into a truncated
'Mu' is dropped rather than checked, so a result term containing the marker is
not evidence that the language below it is non-empty.
-}
getAllTerms :: (Hashable symbol, Typeable symbol, IsString symbol) => Node symbol -> [Term symbol]
getAllTerms = getAllTermsWith "Mu"

-- | 'getAllTerms' with an explicit symbol for truncated recursion.
getAllTermsWith :: (Hashable symbol, Typeable symbol) => symbol -> Node symbol -> [Term symbol]
getAllTermsWith recursionSymbol n =
    map fst $ flip runEnumerateM (initEnumerationState n) $ do
        enumerateFully
        expandUVarWith recursionSymbol (intToUVar 0)
{-# SPECIALIZE getAllTermsWith :: Symbol -> Node Symbol -> [Term Symbol] #-}
