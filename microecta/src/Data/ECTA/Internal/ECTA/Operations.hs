{-# LANGUAGE OverloadedStrings #-}
-- For the 'Pathable' instance for 'Node'
{-# OPTIONS_GHC -Wno-orphans #-}

{- | Core ECTA operations.

This module contains traversal, intersection, union, reduction, and
constraint-propagation logic. Most users should import "Data.ECTA" instead; the
module is exposed so downstream code can reach lower-level helpers when needed.
-}
module Data.ECTA.Internal.ECTA.Operations (
    -- * Traversal
    nodeMapChildren,
    pathsMatching,
    mapNodes,
    crush,
    onNormalNodes,

    -- * Unfolding
    unfoldOuterRec,
    refold,
    nodeEdges,
    unfoldBounded,

    -- * Size operations
    nodeCount,
    edgeCount,
    maxIndegree,

    -- * Union
    union,

    -- * Membership
    nodeRepresents,
    edgeRepresents,

    -- * Constraints
    dropEdgeConstraints,
    dropConstraints,

    -- * Intersection
    intersect,
    dropRedundantEdges,
    intersectEdge,

    -- * Path operations
    requirePath,
    requirePathList,

    -- * Reduction
    withoutRedundantEdges,
    reducePartially,
    reduceEdgeIntersection,
    reduceEqConstraints,

    -- * Debugging
    getSubnodeById,
) where

import Control.Monad.State.Strict (MonadState (..), State, evalState, evalStateT, gets, modify')
import Control.Monad.Trans.Class (lift)
import Data.Functor.Identity (Identity (..))
import qualified Data.HashMap.Strict as HashMap
import Data.Hashable (Hashable (..))
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (compareLength)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Monoid (All (..), First (..), Sum (..))
import Data.Semigroup (Max (..))
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Data.Type.Equality ((:~~:) (HRefl))
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (Typeable, eqTypeRep, typeRep)

import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Internal.Paths
import Data.ECTA.Internal.Term

import Data.Interned.Extended.HashTableBased (Id)

import Data.Memoization (
    MemoCache,
    MemoCacheTag (..),
    TypeableMemoCache,
    memo,
    memo2TypeableWith,
    memo2With,
    memoTypeableWith,
    memoWith,
    newMemoCache,
    newTypeableMemoCache,
 )
import Utility.Fixpoint
import Utility.HashJoin
import Utility.List (adjustAt, atMay)

------------------------------------------------------------------------------------

mapWithIndex :: (Int -> a -> b) -> [a] -> [b]
mapWithIndex f = zipWith f [0 ..]

-----------------------
------ Traversal
-----------------------

{- | Apply an edge transformation to the outgoing alternatives of a node.

This is a shallow operation: for a normal @Node@ it maps over that node's
edges, and for a 'Mu' it first unfolds the outer recursion and then maps those
edges. It does not recursively traverse child nodes. That is the shape wanted
when pushing an edit across every immediate alternative of a node - rewriting
symbols or equality constraints, say - without touching the node's children.
-}
nodeMapChildren :: (Hashable symbol, Typeable symbol) => (Edge symbol -> Edge symbol) -> Node symbol -> Node symbol
nodeMapChildren _ EmptyNode = EmptyNode
nodeMapChildren f n@(Mu _) = nodeMapChildren f (unfoldOuterRec n)
nodeMapChildren f (Node es) = Node (map f es)
nodeMapChildren _ (Rec _) = error "nodeMapChildren: unexpected Rec"

{- | Warning: Linear in number of paths, exponential in size of graph.
  Only use for very small graphs.
-}
pathsMatching :: (Node symbol -> Bool) -> Node symbol -> [Path]
pathsMatching _ EmptyNode = []
pathsMatching _ (InternedMu _) = [] -- Unsound!
pathsMatching f n@(InternedNode node) =
    (concat $ map pathsMatchingEdge es)
        ++ if f n then [EmptyPath] else []
  where
    es = internedNodeEdges node
    pathsMatchingEdge e = concat $ mapWithIndex (\i x -> map (ConsPath i) $ pathsMatching f x) (edgeChildren e)
pathsMatching _ (Rec _) = error $ "pathsMatching: unexpected Rec"

{- | Precondition: For all i, f (Rec i) is either a Rec node meant to represent
                the enclosing Mu, or contains no Rec node not beneath another Mu.
-}
mapNodes :: forall symbol. (Hashable symbol, Typeable symbol) => (Node symbol -> Node symbol) -> Node symbol -> Node symbol
mapNodes f = go
  where
    -- Memoized separately for each mapNodes invocation
    go :: Node symbol -> Node symbol
    go = memo (NameTag "mapNodes") (mapNodesStep go f)
    {-# NOINLINE go #-}

-- | Perform one recursive traversal step using the supplied recursive call.
mapNodesStep ::
    (Hashable symbol, Typeable symbol) =>
    (Node symbol -> Node symbol) ->
    (Node symbol -> Node symbol) ->
    Node symbol ->
    Node symbol
mapNodesStep _ _ EmptyNode = EmptyNode
mapNodesStep recurse f (Node es) =
    f $ Node $ map (\edge -> setChildren edge (map recurse (edgeChildren edge))) es
mapNodesStep recurse f (Mu body) = f $ Mu (recurse . body)
mapNodesStep _ f (Rec recId) = f $ Rec recId

{- | Fold over all reachable nodes, visiting each shared node once.

This name originates from the @crush@ operator in the Stratego language.
Although @m@ is only constrained to be a monoid, this function makes no
guarantees about traversal order. Recursive nodes and ordinary nodes draw
identities from one counter, so one visited set covers both.
-}
crush :: forall symbol m. (Monoid m) => (Node symbol -> m) -> Node symbol -> m
crush f = \n -> evalState (go n) IntSet.empty
  where
    go :: Node symbol -> State IntSet m
    go EmptyNode = return mempty
    go (Rec _) = return mempty
    go n = do
        seen <- get
        let nId = nodeIdentity n
        if IntSet.member nId seen
            then return mempty
            else do
                modify' (IntSet.insert nId)
                mappend (f n) . mconcat <$> mapM go (children n)

    children (InternedMu mu) = [internedMuBody mu]
    children (InternedNode node) = [child | edge <- internedNodeEdges node, child <- edgeChildren edge]
    children _ = []

-- | Run a fold function only on normal non-recursive nodes.
onNormalNodes :: (Monoid m) => (Node symbol -> m) -> Node symbol -> m
onNormalNodes f n@(InternedNode _) = f n
onNormalNodes _ _ = mempty

-----------------------
------ Folding
-----------------------

-- | Memo tables for 'unfoldOuterRec'.
symbolUnfoldOuterRecCache :: MemoCache (Node Symbol) (Node Symbol)
symbolUnfoldOuterRecCache = unsafePerformIO newMemoCache
{-# NOINLINE symbolUnfoldOuterRecCache #-}

genericUnfoldOuterRecCache :: TypeableMemoCache
genericUnfoldOuterRecCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericUnfoldOuterRecCache #-}

-- | Unfold one outer 'Mu' layer. The unfolding of each recursive node is shared.
unfoldOuterRec :: forall symbol. (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol
unfoldOuterRec node = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> memoWith symbolUnfoldOuterRecCache go node
    Nothing -> memoTypeableWith genericUnfoldOuterRecCache go node
  where
    go :: Node symbol -> Node symbol
    go n@(Mu x) = x n
    go _ = error "unfoldOuterRec: Must be called on a Mu node"

-- | Outgoing alternatives of a node, unfolding one outer 'Mu' if needed.
nodeEdges :: (Hashable symbol, Typeable symbol) => Node symbol -> [Edge symbol]
nodeEdges (InternedNode node) = internedNodeEdges node
nodeEdges n@(Mu _) = nodeEdges (unfoldOuterRec n)
nodeEdges _ = []

-- | Memo tables for 'refold'.
symbolRefoldCache :: MemoCache (Node Symbol) (Node Symbol)
symbolRefoldCache = unsafePerformIO newMemoCache
{-# NOINLINE symbolRefoldCache #-}

genericRefoldCache :: TypeableMemoCache
genericRefoldCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericRefoldCache #-}

-- | Replace repeated unfoldings with recursive 'Mu' nodes where possible.
refold :: forall symbol. (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol
refold node = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> memoWith symbolRefoldCache go node
    Nothing -> memoTypeableWith genericRefoldCache go node
  where
    go :: Node symbol -> Node symbol
    go n =
        if HashMap.null muNodeMap
            then n
            else fixUnbounded (mapNodes tryUnfold) n
      where
        muNodeMap =
            crush
                ( \case
                    x@(Mu _) -> HashMap.singleton (unfoldOuterRec x) x
                    _ -> HashMap.empty
                )
                n

        tryUnfold x = case HashMap.lookup x muNodeMap of
            Just y -> y
            Nothing -> x

{- | Unfold recursive nodes at most the given number of rounds.

A bound of zero or less unfolds nothing and replaces every 'Mu' with
'EmptyNode', leaving only the terms that need no recursion at all. Matching
@0@ alone would leave a negative bound counting down forever.
-}
unfoldBounded :: (Hashable symbol, Typeable symbol) => Int -> Node symbol -> Node symbol
unfoldBounded rounds
    | rounds <= 0 =
        mapNodes
            ( \case
                Mu _ -> EmptyNode
                n -> n
            )
    | otherwise =
        unfoldBounded (rounds - 1)
            . mapNodes
                ( \case
                    n@(Mu _) -> unfoldOuterRec n
                    n -> n
                )

------------
------ Size operations
------------

-- | Count reachable non-recursive nodes, sharing-aware.
nodeCount :: Node symbol -> Int
nodeCount = getSum . crush (onNormalNodes $ const $ Sum 1)

-- | Count reachable outgoing edges, sharing-aware.
edgeCount :: Node symbol -> Int
edgeCount = getSum . crush (onNormalNodes go)
  where
    go (InternedNode node) = Sum (length (internedNodeEdges node))
    go _ = mempty

{- | Maximum number of outgoing alternatives on any reachable normal node.

Zero when there is no normal node to count, as for 'EmptyNode': the @Max@
monoid's identity is @minBound@, which is not an answer anyone can use.
-}
maxIndegree :: Node symbol -> Int
maxIndegree = max 0 . getMax . crush (onNormalNodes go)
  where
    go (InternedNode node) = Max (length (internedNodeEdges node))
    go _ = mempty

------------
------ Membership
------------

{- | Test whether a node accepts a concrete term.

The edges of a node are tried in order, and the children of an edge from left
to right. When the search comes to a subterm again with the same node, it uses
the first result. So each node is decided at most once at each position in the
term.
-}
nodeRepresents :: (Hashable symbol, Typeable symbol) => Node symbol -> Term symbol -> Bool
nodeRepresents node = runIdentity . acceptsBy nodeEdges edgeSymbol edgeChildren check node
  where
    check _ edge term = Identity (edgeEcsSatisfied edge term)

-- | Test whether an edge accepts a concrete term.
edgeRepresents :: (Hashable symbol, Typeable symbol) => Edge symbol -> Term symbol -> Bool
edgeRepresents e = \t@(Term s ts) ->
    s == edgeSymbol e
        && childrenRepresent (edgeChildren e) ts
        && edgeEcsSatisfied e t
  where
    childrenRepresent [] [] = True
    childrenRepresent (n : ns) (t : ts) = nodeRepresents n t && childrenRepresent ns ts
    childrenRepresent _ _ = False

-- | Whether every action succeeds, stopping at the first failure.
andM :: (Monad m) => [m Bool] -> m Bool
andM [] = pure True
andM (action : actions) = action >>= \ok -> if ok then andM actions else pure False

-- | Whether some action succeeds, stopping at the first success.
orM :: (Monad m) => [m Bool] -> m Bool
orM [] = pure False
orM (action : actions) = action >>= \ok -> if ok then pure True else orM actions

{- | Decide whether a key accepts a term, from the outgoing alternatives of each key.

An alternative matches a subterm when its symbol and its number of children
are those of the root of the subterm. The matching alternatives of a key are
tried in order, and the search stops at the first one that accepts. The
children of an alternative are tried from left to right. The check runs only
when all of them accept. This is the order of the direct recursion.

The direct recursion decides a subterm again for each alternative above it
that fails, so its time can be exponential in the depth of the term. This
search keeps a table below each subterm that two or more alternatives match.
In the table, each key at each position of the term is decided once, and a
later visit uses that result and runs no check. Above such a subterm, each
subterm has one visit, and the search keeps no table. Thus each check runs at
most once for each key, alternative, and position, in the order in which the
direct recursion first runs it.
-}
acceptsBy ::
    (Monad m, Ord key, Eq symbol) =>
    (key -> [alternative]) ->
    (alternative -> symbol) ->
    (alternative -> [key]) ->
    (key -> alternative -> Term symbol -> m Bool) ->
    key ->
    Term symbol ->
    m Bool
acceptsBy outgoing symbolOf childrenOf check = unshared
  where
    matches (Term symbol children) alternative =
        symbolOf alternative == symbol && length (childrenOf alternative) == length children

    -- The alternatives of a row from the first one that matches a subterm.
    fromMatch _ [] = []
    fromMatch term alternatives@(alternative : rest)
        | matches term alternative = alternatives
        | otherwise = fromMatch term rest

    -- No other visit reaches this subterm, so its result needs no table.
    unshared key term@(Term _ children) = case fromMatch term (outgoing key) of
        [] -> pure False
        alternative : rest -> case fromMatch term rest of
            [] ->
                childrenAccept (childrenOf alternative) children >>= \accepted ->
                    if accepted then check key alternative term else pure False
            _ -> evalStateT (shared key (positioned term)) Map.empty
    childrenAccept (key : keys) (child : rest) =
        unshared key child >>= \accepted -> if accepted then childrenAccept keys rest else pure False
    childrenAccept _ _ = pure True

    -- This subterm is at or below a subterm that two or more alternatives
    -- match. The table holds the result of each position and key.
    shared key (Tree.Node (_, term) children) =
        orM
            [ andM (zipWith visit (childrenOf alternative) children) >>= \accepted ->
                if accepted then lift (check key alternative term) else pure False
            | alternative <- outgoing key
            , matches term alternative
            ]
    visit key node@(Tree.Node (position, _) _) = do
        known <- gets (Map.lookup (position, key))
        case known of
            Just accepted -> pure accepted
            Nothing -> do
                accepted <- shared key node
                modify' (Map.insert (position, key) accepted)
                pure accepted

    -- Each subterm with its position in preorder.
    positioned whole = evalState (number whole) (0 :: Int)
      where
        number term@(Term _ children) = do
            position <- get
            modify' (+ 1)
            Tree.Node (position, term) <$> traverse number children

{- | Whether a term agrees with itself everywhere an edge's constraints say it
must.

Every path of a class must exist in the term, as in enumeration. A class
whose paths are all missing from the term is not satisfied.

'unsafeGetEclasses' is safe here: 'mkEdge' collapses a contradictory
constraint set to 'emptyEdge', so no interned edge carries 'EqContradiction'.
-}
edgeEcsSatisfied :: (Eq symbol) => Edge symbol -> Term symbol -> Bool
edgeEcsSatisfied e t = all eclassSatisfied (unsafeGetEclasses $ edgeEcs e)
  where
    eclassSatisfied :: PathEClass -> Bool
    eclassSatisfied pec = maybe False allTheSame $ traverse (`getPath` t) $ unPathEClass pec

    allTheSame :: (Eq a) => [a] -> Bool
    allTheSame [] = True
    allTheSame (x : xs) = go x xs
      where
        go !_ [] = True
        go !y (!z : zs) = (y == z) && go y zs
    {-# INLINE allTheSame #-}

-----------------------
------ Constraints
-----------------------

{- | Drop an edge's equality constraints.

Dropping constraints broadens the language to every combination of child
terms. Use it only when equality constraints are deliberately irrelevant.
-}
dropEdgeConstraints :: (Hashable symbol, Typeable symbol) => Edge symbol -> Edge symbol
dropEdgeConstraints e = Edge (edgeSymbol e) (edgeChildren e)

-- | Memo tables for 'dropConstraints'.
symbolDropConstraintsCache :: MemoCache (Node Symbol) (Node Symbol)
symbolDropConstraintsCache = unsafePerformIO newMemoCache
{-# NOINLINE symbolDropConstraintsCache #-}

genericDropConstraintsCache :: TypeableMemoCache
genericDropConstraintsCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericDropConstraintsCache #-}

-- | Drop the equality constraints of every edge in a node; see 'dropEdgeConstraints'.
dropConstraints :: forall symbol. (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol
dropConstraints node = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> memoWith symbolDropConstraintsCache go node
    Nothing -> memoTypeableWith genericDropConstraintsCache go node
  where
    go = mapNodesStep dropConstraints dropNodeConstraints

    dropNodeConstraints (Node es) = Node (map dropEdgeConstraints es)
    dropNodeConstraints n = n

------------
------ Intersect
------------

data RuleOutRes symbol = Keep | RuledOutBy (Edge symbol)

-- | Remove edges that are subsumed by another edge with the same symbol.
dropRedundantEdges :: forall symbol. (Hashable symbol, Typeable symbol) => [Edge symbol] -> [Edge symbol]
dropRedundantEdges origEs = concatMap reduceCluster clusters
  where
    clusters = map (nubByIdSinglePass edgeId) $ clusterByHash edgeSymbol origEs

    reduceCluster :: [Edge symbol] -> [Edge symbol]
    reduceCluster [] = []
    reduceCluster (e : es) = case ruleOut e es of
        -- Optimization: If e' > e, likely to be greater than other things;
        -- move it to front and rule out more stuff next iteration.
        --
        -- No noticeable difference in overall wall clock time (7/2/21),
        -- but a few % reduction in calls to intersectEdgeSameSymbol
        (RuledOutBy e', es') -> reduceCluster (e' : es')
        (Keep, es') -> e : reduceCluster es'

    ruleOut :: Edge symbol -> [Edge symbol] -> (RuleOutRes symbol, [Edge symbol])
    ruleOut _ [] = (Keep, [])
    ruleOut e (x : xs) =
        let e' = intersectEdgeSameSymbol e x
         in if e' == x
                then
                    ruleOut e xs
                else
                    if e' == e
                        then
                            (RuledOutBy x, xs)
                        else
                            let (res, notRuledOut) = ruleOut e xs
                             in (res, x : notRuledOut)

-- | Intersect two edges when they have the same symbol and the same number of children.
intersectEdge :: (Hashable symbol, Typeable symbol) => Edge symbol -> Edge symbol -> Maybe (Edge symbol)
intersectEdge e1 e2
    | edgeSymbol e1 /= edgeSymbol e2 = Nothing
    | length (edgeChildren e1) /= length (edgeChildren e2) = Nothing
    | otherwise = Just $ intersectEdgeSameSymbol e1 e2

symbolIntersectEdgeSameSymbolCache :: MemoCache (Edge Symbol, Edge Symbol) (Edge Symbol)
symbolIntersectEdgeSameSymbolCache = unsafePerformIO newMemoCache
{-# NOINLINE symbolIntersectEdgeSameSymbolCache #-}

genericIntersectEdgeSameSymbolCache :: TypeableMemoCache
genericIntersectEdgeSameSymbolCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericIntersectEdgeSameSymbolCache #-}

intersectEdgeSameSymbol :: forall symbol. (Hashable symbol, Typeable symbol) => Edge symbol -> Edge symbol -> Edge symbol
intersectEdgeSameSymbol left right = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> memo2With symbolIntersectEdgeSameSymbolCache go left right
    Nothing -> memo2TypeableWith genericIntersectEdgeSameSymbolCache go left right
  where
    go e1 e2
        | e2 < e1 = intersectEdgeSameSymbol e2 e1
        | length (edgeChildren e1) /= length (edgeChildren e2) = emptyEdge (edgeSymbol e1)
    go e1 e2 =
        mkEdge
            (edgeSymbol e1)
            (zipWith intersect (edgeChildren e1) (edgeChildren e2))
            (edgeEcs e1 `combineEqConstraints` edgeEcs e2)
{-# NOINLINE intersectEdgeSameSymbol #-}

------------
------ New intersection
------------

-- | Intersection of two ECTAs.
intersect :: (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol -> Node symbol
intersect l r = intersectOpen (emptyIntersectionDom, l, r)
{-# NOINLINE intersect #-}

------ Intersection internals

{- | Intersection domain

Information required to compute the intersection of open terms.
-}
data IntersectionDom symbol = ID
    { idFree :: Map Id (Node symbol)
    -- ^ Value of all free variables inside the term (so that we can unfold when necessary)
    , idRecInt :: Set IntersectId
    -- ^ Intersection problems we encountered previously (to avoid infinite unrolling)
    , idHash :: !Int
    -- ^ Hash of the two fields, computed once: every memo lookup hashes the domain.
    }
    deriving (Show, Eq)

instance Hashable (IntersectionDom symbol) where
    hashWithSalt s dom = hashWithSalt s (idHash dom)

-- | Build a domain and its hash. Both containers list their elements in key order, a canonical form.
mkIntersectionDom :: Map Id (Node symbol) -> Set IntersectId -> IntersectionDom symbol
mkIntersectionDom free recInt = ID free recInt (hash (Map.toList free, Set.toList recInt))

-- | An intersection environment with no free or pending variables.
emptyIntersectionDom :: IntersectionDom symbol
emptyIntersectionDom = mkIntersectionDom Map.empty Set.empty

symbolIntersectOpenCache :: MemoCache (IntersectionDom Symbol, Node Symbol, Node Symbol) (Node Symbol)
symbolIntersectOpenCache = unsafePerformIO newMemoCache
{-# NOINLINE symbolIntersectOpenCache #-}

genericIntersectOpenCache :: TypeableMemoCache
genericIntersectOpenCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericIntersectOpenCache #-}

intersectOpen :: forall symbol. (Hashable symbol, Typeable symbol) => (IntersectionDom symbol, Node symbol, Node symbol) -> Node symbol
{-# NOINLINE intersectOpen #-}
intersectOpen input = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> memoWith symbolIntersectOpenCache worker input
    Nothing -> memoTypeableWith genericIntersectOpenCache worker input
  where
    worker (dom, left, right) = onNode dom left right

    onNode :: IntersectionDom symbol -> Node symbol -> Node symbol -> Node symbol
    onNode !dom l r =
        case (l, r) of
            -- Rule out empty cases first
            -- This justifies the use of nodeIdentity (@i@, @j@) for the other cases
            (EmptyNode, _) -> EmptyNode
            (_, EmptyNode) -> EmptyNode
            -- For closed terms, improve memoization performance by using the empty environment
            _ | Set.null (freeVars l), Set.null (freeVars r), not (Map.null (idFree dom)) -> intersect l r
            -- Special case for self-intersection (equality check is cheap of course: just uses the interned 'Id')
            _ | l == r, Set.null (freeVars l) -> l
            -- Always intersect nodes in the same order. This is important for two reasons:
            --
            -- 1. It will increase the probability of a cache hit (i.e., improve memoization)
            -- 2. It will increase the probability of being able to use 'ieRecInt'
            _ | l > r -> intersectOpen (dom, r, l)
            -- If we have seen this exact problem before, refer to enclosing Mu.
            _ | Set.member (IntersectId i j) (idRecInt dom) -> Rec (RecIntersect (IntersectId i j))
            -- When encountering a 'Mu', extend the domain appropriately.
            (InternedMu l', InternedMu r') -> maybeMu $ intersectOpen (extendEnv [(i, l), (j, r)], internedMuBody l', internedMuBody r')
            (InternedMu l', _) -> maybeMu $ intersectOpen (extendEnv [(i, l)], internedMuBody l', r)
            (_, InternedMu r') -> maybeMu $ intersectOpen (extendEnv [(j, r)], l, internedMuBody r')
            -- When encountering a free variable, look up the corresponding value in the environment.
            -- (Recall that the case for already-seen intersection problems is are handled above.)
            (Rec l', _) -> intersectOpen (dom, findFreeVar l', r)
            (_, Rec r') -> intersectOpen (dom, l, findFreeVar r')
            -- Finally, the real intersection work happens here
            (InternedNode l', InternedNode r') ->
                Node $
                    hashJoin
                        edgeSymbol
                        (\e e' -> intersectOpenEdge (dom, e, e'))
                        (internedNodeEdges l')
                        (internedNodeEdges r')
      where
        -- Node identities (should only be used (forced) if previously established the nodes are not empty)
        i, j :: Id
        i = nodeIdentity l
        j = nodeIdentity r

        -- Extend domain when we encounter a 'Mu'
        -- We might see one or two 'Mu's (if we happen to see a 'Mu' on both sides at once)
        extendEnv :: [(Id, Node symbol)] -> IntersectionDom symbol
        extendEnv bindings =
            mkIntersectionDom
                (Map.union (Map.fromList bindings) (idFree dom))
                (Set.insert (IntersectId i j) (idRecInt dom))

        -- Find value of free variables in the terms
        -- Since we assume the input terms are fully interned, we only deal with 'RecInt'.
        findFreeVar :: RecNodeId -> Node symbol
        findFreeVar (RecInt intId) | Just n <- Map.lookup intId (idFree dom) = n
        findFreeVar recId = error $ "findFreeVar: unexpected " <> show recId

        -- We only insert a 'Mu' node when necessary.
        maybeMu :: Node symbol -> Node symbol
        maybeMu n
            | RecIntersect (IntersectId i j) `Set.member` freeVars n =
                Mu $ \recNode -> substFree (RecIntersect (IntersectId i j)) recNode n
            | otherwise =
                n

-- | Auxiliary to 'intersectOpen'.
symbolIntersectOpenEdgeCache :: MemoCache (IntersectionDom Symbol, Edge Symbol, Edge Symbol) (Edge Symbol)
symbolIntersectOpenEdgeCache = unsafePerformIO newMemoCache
{-# NOINLINE symbolIntersectOpenEdgeCache #-}

genericIntersectOpenEdgeCache :: TypeableMemoCache
genericIntersectOpenEdgeCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericIntersectOpenEdgeCache #-}

intersectOpenEdge :: forall symbol. (Hashable symbol, Typeable symbol) => (IntersectionDom symbol, Edge symbol, Edge symbol) -> Edge symbol
{-# NOINLINE intersectOpenEdge #-}
intersectOpenEdge input = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> memoWith symbolIntersectOpenEdgeCache worker input
    Nothing -> memoTypeableWith genericIntersectOpenEdgeCache worker input
  where
    worker (dom, left, right) = onEdge dom left right

    onEdge :: IntersectionDom symbol -> Edge symbol -> Edge symbol -> Edge symbol
    onEdge _ l r | length (edgeChildren l) /= length (edgeChildren r) = emptyEdge (edgeSymbol l)
    onEdge !dom l r =
        mkEdge
            (edgeSymbol l)
            (zipWith (\a b -> intersectOpen (dom, a, b)) (edgeChildren l) (edgeChildren r))
            (edgeEcs l `combineEqConstraints` edgeEcs r)

------------
------ Union
------------

{- | Union a list of ECTAs by concatenating their alternatives.

'EmptyNode' and 'Rec' contribute no alternatives, and the @Node@ constructor
maps an empty alternative list back to 'EmptyNode', so the empty cases need no
special handling. Inside a binder, the union with the binder's own reference is
the least fixed point, which is correct. The union with a reference to an
enclosing binder also loses that binder's terms, because a node holds only
edges and a reference has none. To keep them, put the union under the edges
that use it: @Node [Edge "wrap" [o], Edge "wrap" [b]]@ in place of
@Node [Edge "wrap" [union [o, b]]]@.
-}
union :: (Hashable symbol, Typeable symbol) => [Node symbol] -> Node symbol
union = Node . concatMap nodeEdges

-- | Union the nodes a partial function produces; see 'union'.
unionMapMaybe :: (Hashable symbol, Typeable symbol) => (a -> Maybe (Node symbol)) -> [a] -> Node symbol
unionMapMaybe f = union . mapMaybe f

----------------------
------ Path operations
----------------------

-- | Restrict an ECTA to terms that contain the given path.
requirePath :: (Hashable symbol, Typeable symbol) => Path -> Node symbol -> Node symbol
requirePath EmptyPath n = n
requirePath _ EmptyNode = EmptyNode
requirePath p n@(Mu _) = requirePath p (unfoldOuterRec n)
requirePath (ConsPath p ps) (Node es) =
    Node $
        map (\e -> setChildren e (requirePathList (ConsPath p ps) (edgeChildren e))) $
            filter
                (\e -> length (edgeChildren e) > p)
                es
requirePath _ (Rec _) = error "requirePath: unexpected Rec"

-- | Variant of 'requirePath' for a child list.
requirePathList :: (Hashable symbol, Typeable symbol) => Path -> [Node symbol] -> [Node symbol]
requirePathList EmptyPath ns = ns
requirePathList (ConsPath p ps) ns = adjustAt p (requirePath ps) ns

instance (Hashable symbol, Typeable symbol) => Pathable (Node symbol) (Node symbol) where
    type Emptyable (Node symbol) = Node symbol

    getPath _ EmptyNode = EmptyNode
    getPath EmptyPath n = n
    getPath p n@(Mu _) = getPath p (unfoldOuterRec n)
    getPath (ConsPath p ps) (Node es) = unionMapMaybe goEdge es
      where
        goEdge :: Edge symbol -> Maybe (Node symbol)
        goEdge (Edge _ ns) = getPath ps <$> atMay p ns
    getPath p _ = error $ "getPath: unexpected path " <> show p <> " for unresolved node"

    getAllAtPath _ EmptyNode = []
    getAllAtPath EmptyPath n = [n]
    getAllAtPath p n@(Mu _) = getAllAtPath p (unfoldOuterRec n)
    getAllAtPath (ConsPath p ps) (Node es) = concatMap (getAllAtPath ps) (mapMaybe goEdge es)
      where
        goEdge :: Edge symbol -> Maybe (Node symbol)
        goEdge (Edge _ ns) = atMay p ns
    getAllAtPath p _ = error $ "getAllAtPath: unexpected path " <> show p <> " for unresolved node"

    modifyAtPath f EmptyPath n = f n
    modifyAtPath _ _ EmptyNode = EmptyNode
    modifyAtPath f p n@(Mu _) = modifyAtPath f p (unfoldOuterRec n)
    modifyAtPath f (ConsPath p ps) (Node es) = Node (map goEdge es)
      where
        goEdge :: Edge symbol -> Edge symbol
        goEdge e = setChildren e (adjustAt p (modifyAtPath f ps) (edgeChildren e))
    modifyAtPath _ p _ = error $ "modifyAtPath: unexpected path " <> show p <> " for unresolved node"

instance (Hashable symbol, Typeable symbol) => Pathable [Node symbol] (Node symbol) where
    type Emptyable (Node symbol) = Node symbol

    getPath EmptyPath ns = union ns
    getPath (ConsPath p ps) ns = case atMay p ns of
        Nothing -> EmptyNode
        Just n -> getPath ps n

    getAllAtPath EmptyPath _ = []
    getAllAtPath (ConsPath p ps) ns = case atMay p ns of
        Nothing -> []
        Just n -> getAllAtPath ps n

    modifyAtPath _ EmptyPath ns = ns
    modifyAtPath f (ConsPath p ps) ns = adjustAt p (modifyAtPath f ps) ns

------------------------------------
------ Reduction
------------------------------------

-- | Memo tables for 'withoutRedundantEdges'.
symbolWithoutRedundantEdgesCache :: MemoCache (Node Symbol) (Node Symbol)
symbolWithoutRedundantEdgesCache = unsafePerformIO newMemoCache
{-# NOINLINE symbolWithoutRedundantEdgesCache #-}

genericWithoutRedundantEdgesCache :: TypeableMemoCache
genericWithoutRedundantEdgesCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericWithoutRedundantEdgesCache #-}

{- | Remove alternatives implied by another alternative at each node.

Only a node without free recursive variables is changed, because the
comparison intersects alternatives. A recursive node compares the alternatives
of its unfolding, and keeps the alternatives of its body that remain. A node
that refers to an enclosing recursive node keeps all of its alternatives.
-}
withoutRedundantEdges :: forall symbol. (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol
withoutRedundantEdges node = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> memoWith symbolWithoutRedundantEdgesCache go node
    Nothing -> memoTypeableWith genericWithoutRedundantEdgesCache go node
  where
    go = mapNodesStep withoutRedundantEdges dropReds

    dropReds n@(Node es) | Set.null (freeVars n) = Node (dropRedundantEdges es)
    dropReds n@(InternedMu mu)
        | Set.null (freeVars n)
        , InternedNode body <- internedMuBody mu =
            let self = RecInt (internedMuId mu)
                kept = Set.fromList (dropRedundantEdges (nodeEdges n))
                -- The alternative of the unfolding that a body alternative becomes.
                unfolded e = setChildren e (map (substFree self n) (edgeChildren e))
                es = internedNodeEdges body
                es' = filter ((`Set.member` kept) . unfolded) es
             in if length es' == length es then n else Mu $ \r -> substFree self r (Node es')
    dropReds n = n

---------------
--- Reducing Equality Constraints
---------------

{- | Propagate equality constraints through one reduction pass.

One pass narrows every child by the constraints that reach it, but a nested
constrained edge can narrow a child after an outer edge has already read it.
Iterate to a fixpoint, as 'fixUnbounded' does, when every constrained position
must agree with every other.

The pass does not unfold a recursive node that has constraints. A class that
reaches into such a node stays unreduced (see 'reduceEqConstraints'). The
language does not change, because enumeration and 'nodeRepresents' still check
that class.
-}
reducePartially :: (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol
reducePartially = reducePartially' EmptyConstraints

symbolReducePartiallyCache :: MemoCache (EqConstraints, Node Symbol) (Node Symbol)
symbolReducePartiallyCache = unsafePerformIO newMemoCache
{-# NOINLINE symbolReducePartiallyCache #-}

genericReducePartiallyCache :: TypeableMemoCache
genericReducePartiallyCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericReducePartiallyCache #-}

reducePartially' :: forall symbol. (Hashable symbol, Typeable symbol) => EqConstraints -> Node symbol -> Node symbol
reducePartially' constraints node = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> memo2With symbolReducePartiallyCache go constraints node
    Nothing -> memo2TypeableWith genericReducePartiallyCache go constraints node
  where
    go :: EqConstraints -> Node symbol -> Node symbol
    go _ EmptyNode = EmptyNode
    go _ (Mu n) = Mu n
    go inheritedEcs n@(Node _) = modifyNode n $ \es ->
        map (reduceChildren inheritedEcs) $
            map (reduceEdgeIntersection inheritedEcs) es
    go _ (Rec _) = error "reducePartially: unexpected Rec"

    reduceChildren :: EqConstraints -> Edge symbol -> Edge symbol
    reduceChildren inheritedEcs e = setChildren e $ reduceWithInheritedEcs (inheritedEcs `combineEqConstraints` edgeEcs e) (edgeChildren e)

    -- Reduce children with inherited constraints.
    --
    -- This function is used to avoid infinite unfolding of recursive nodes,
    -- and we do this by passing constraints from the current edge and ancestors to descendants.
    -- For example, let `tau` be "any" node, and we define
    --
    -- > let n1 = Node [ mkEdge "Pair" [tau, tau] (mkEqConstraints [[path [0, 0], path [0, 1], path [1]]])]
    -- > let n2 = Node [ Edge "Pair" [tau, tau] ]
    -- > let n  = Node [ mkEdge "Pair" [n1, n2]   (mkEqConstraints [[path [0, 0], path [0, 1], path [1]]])]
    --
    -- If `reducePartially n` does not propagate constraints down to its children `n1` or `n2`,
    -- the reduction can expand `tau` without end between rounds.
    --
    -- To break such cycles, we actively pass constraints down to children.
    -- In this example, we first call `reducePartially' EmptyConstraints n` at the top level, where the inherited constraint is empty,
    -- so we only need to consider the constraints from the current edge.
    -- Then, we pass the constraints `0.0=0.1=1` down to its children, and `n1` receives `0=1` and `n2` receives nothing.
    -- Next, we reduce the children of `n` by calling `reducePartially' (mkEqConstraints [[path [0], path [1]]]) n1`.
    -- At this node, we will have to combine the inherited constraints `0=1` and the local constraints `0.0=0.1=1`.
    -- Now, we can see that these two constraints contain a contradiction that requires `0=0.0=0.1`, so we can drop the edge.
    --
    -- This does not stop every recursive cycle. A cycle through a recursive
    -- node with constraints stops because 'reduceEqConstraints' does not
    -- unfold that node. 'go' returns a recursive node unchanged, and
    -- 'reduceEqConstraints' makes one pass over the classes of an edge, so one
    -- pass visits a finite part of the input. No proof shows that a
    -- repetition of passes ends on every input.
    reduceWithInheritedEcs :: EqConstraints -> [Node symbol] -> [Node symbol]
    reduceWithInheritedEcs EqContradiction children = map (const EmptyNode) children
    reduceWithInheritedEcs inheritedEcs children = zipWith (\i -> reducePartially' (eqConstraintsDescend inheritedEcs i)) [0 ..] children
{-# NOINLINE reducePartially' #-}

-- | Memo tables for 'reduceEdgeIntersection'.
symbolReduceEdgeIntersectionCache :: MemoCache (EqConstraints, Edge Symbol) (Edge Symbol)
symbolReduceEdgeIntersectionCache = unsafePerformIO newMemoCache
{-# NOINLINE symbolReduceEdgeIntersectionCache #-}

genericReduceEdgeIntersectionCache :: TypeableMemoCache
genericReduceEdgeIntersectionCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericReduceEdgeIntersectionCache #-}

{- | Narrow an edge's children by its own equality constraints. The edge becomes
empty when its constraints contradict the inherited constraints.
-}
reduceEdgeIntersection :: forall symbol. (Hashable symbol, Typeable symbol) => EqConstraints -> Edge symbol -> Edge symbol
reduceEdgeIntersection constraints edge = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> memo2With symbolReduceEdgeIntersectionCache go constraints edge
    Nothing -> memo2TypeableWith genericReduceEdgeIntersectionCache go constraints edge
  where
    go :: EqConstraints -> Edge symbol -> Edge symbol
    go ecs e =
        mkEdge
            (edgeSymbol e)
            (reduceEqConstraints (edgeEcs e) ecs (edgeChildren e))
            (edgeEcs e)
{-# NOINLINE reduceEdgeIntersection #-}

{- | Apply the local equality classes to a child list. Make every child empty
when the local and inherited classes contradict each other.

One pass over the classes is not always enough: the intersection for one class
can narrow a node that a class earlier in the pass already read. Iterate the
reduction, as 'fixUnbounded' does, to get a fixpoint. The reduction does not
iterate by itself. The next pass reads the new nodes of this pass, so its
intersections miss the memo. A fixpoint at each edge made the term search of
the ECTA paper about 100 times slower than a fixpoint of 'reducePartially'.

A class stays unreduced when one of its paths meets a recursive node with
constraints, at the end of the path or before it. Unfolding such a node shows
its constrained edges again, and their reduction unfolds the node again. A
recursive node without constraints can unfold, because its unfolding has no
constraints to reduce.
-}
reduceEqConstraints :: forall symbol. (Hashable symbol, Typeable symbol) => EqConstraints -> EqConstraints -> [Node symbol] -> [Node symbol]
reduceEqConstraints = go
  where
    propagateEmptyNodes :: [Node symbol] -> [Node symbol]
    propagateEmptyNodes ns = if EmptyNode `elem` ns then map (const EmptyNode) ns else ns

    go :: EqConstraints -> EqConstraints -> [Node symbol] -> [Node symbol]
    go EmptyConstraints EmptyConstraints origNs = origNs
    go ecs inheritedEcs origNs
        | constraintsAreContradictory (ecs `combineEqConstraints` inheritedEcs) = map (const EmptyNode) origNs
        | otherwise = propagateEmptyNodes $ foldr reduceEClass withNeededChildren eclasses
      where
        eclasses = filter (not . any (meetsConstrainedMu origNs) . unPathEClass) (unsafeSubsumptionOrderedEclasses ecs)

        withNeededChildren = requireAll (Set.fromList $ concatMap unPathEClass eclasses) origNs

        intersectList :: [Node symbol] -> Node symbol
        intersectList [] = EmptyNode
        intersectList (n : ns) = foldr intersect n ns

        -- Narrow the node at each path of the class to the nodes at the other paths.
        reduceEClass :: PathEClass -> [Node symbol] -> [Node symbol]
        reduceEClass pec ns =
            editAll
                [ (p, intersect $ intersectList [getPath other ns | other <- paths, other /= p])
                | p <- paths
                ]
                ns
          where
            paths = unPathEClass pec

    -- Whether a path meets a recursive node with constraints, at the end of
    -- the path or before it. A free recursive reference counts as such a
    -- node, because its edges are not known there. So does a node with free
    -- references at the end of the path, and an unconstrained recursive node
    -- with free references is followed through its unfolding.
    meetsConstrainedMu :: [Node symbol] -> Path -> Bool
    meetsConstrainedMu ns (ConsPath index rest) = maybe False (nodeMeetsConstrainedMu rest) (atMay index ns)
    meetsConstrainedMu _ EmptyPath = False

    nodeMeetsConstrainedMu :: Path -> Node symbol -> Bool
    nodeMeetsConstrainedMu _ (Rec _) = True
    nodeMeetsConstrainedMu _ n | numNestedMu n == 0 && null (freeVars n) = False
    nodeMeetsConstrainedMu p n@(InternedMu _)
        | not (unconstrained n) = True
        | null (freeVars n) = False
        | otherwise = nodeMeetsConstrainedMu p (unfoldOuterRec n)
    nodeMeetsConstrainedMu EmptyPath n = not (null (freeVars n))
    nodeMeetsConstrainedMu p (Node es) = any (\e -> meetsConstrainedMu (edgeChildren e) p) es
    nodeMeetsConstrainedMu _ _ = False

-- | A trie of child positions that must exist. An empty map ends a required path.
newtype Needed = Needed (IntMap.IntMap Needed)

{- | Restrict a child list to the terms that contain every path, in one
traversal. This gives the same nodes as requiring the paths one at a time.
-}
requireAll ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    Set Path -> [Node symbol] -> [Node symbol]
requireAll paths = requireList (foldr insertNeeded (Needed IntMap.empty) paths)
  where
    insertNeeded EmptyPath needed = needed
    insertNeeded (ConsPath index rest) (Needed children) =
        Needed $ IntMap.alter (Just . insertNeeded rest . fromMaybe (Needed IntMap.empty)) index children

    requireList :: Needed -> [Node symbol] -> [Node symbol]
    requireList (Needed children) ns = IntMap.foldrWithKey (\index needed -> adjustAt index (requireNode needed)) ns children

    requireNode :: Needed -> Node symbol -> Node symbol
    requireNode (Needed children) n | IntMap.null children = n
    requireNode _ EmptyNode = EmptyNode
    requireNode needed n@(Mu _) = requireNode needed (unfoldOuterRec n)
    requireNode needed@(Needed children) (Node es) =
        Node
            [ setChildren e (requireList needed (edgeChildren e))
            | e <- es
            , compareLength (edgeChildren e) (fst (IntMap.findMax children)) == GT
            ]
    requireNode _ (Rec _) = error "requireAll: unexpected Rec"

-- | Edits at child positions: one at the end of a path, or the edits below an index.
data Edits symbol
    = EditAt (Node symbol -> Node symbol)
    | EditBelow (IntMap.IntMap (Edits symbol))

{- | Apply edits at several paths, none a prefix of another, in one traversal.
This gives the same nodes as 'modifyAtPath' at each path in turn.
-}
editAll ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    [(Path, Node symbol -> Node symbol)] -> [Node symbol] -> [Node symbol]
editAll edits = editList (foldr (uncurry insertEdit) (EditBelow IntMap.empty) edits)
  where
    insertEdit EmptyPath f _ = EditAt f
    insertEdit (ConsPath index rest) f (EditBelow children) =
        EditBelow $ IntMap.alter (Just . insertEdit rest f . fromMaybe (EditBelow IntMap.empty)) index children
    insertEdit (ConsPath _ _) _ leaf@(EditAt _) = leaf

    editList :: Edits symbol -> [Node symbol] -> [Node symbol]
    editList (EditAt _) ns = ns
    editList (EditBelow children) ns = IntMap.foldrWithKey (\index below -> adjustAt index (editNode below)) ns children

    editNode :: Edits symbol -> Node symbol -> Node symbol
    editNode (EditAt f) n = f n
    editNode _ EmptyNode = EmptyNode
    editNode below n@(Mu _) = editNode below (unfoldOuterRec n)
    editNode below (Node es) = Node (map (\e -> setChildren e (editList below (edgeChildren e))) es)
    editNode _ (Rec _) = error "editAll: unexpected Rec"

-- | Memo tables for 'unconstrained'.
symbolUnconstrainedCache :: MemoCache (Node Symbol) Bool
symbolUnconstrainedCache = unsafePerformIO newMemoCache
{-# NOINLINE symbolUnconstrainedCache #-}

genericUnconstrainedCache :: TypeableMemoCache
genericUnconstrainedCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericUnconstrainedCache #-}

{- | Whether no edge reachable from the node carries an equality constraint.
Such an automaton is an ordinary tree automaton, recursive or not.
-}
unconstrained :: forall symbol. (Typeable symbol) => Node symbol -> Bool
unconstrained node = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> memoWith symbolUnconstrainedCache go node
    Nothing -> memoTypeableWith genericUnconstrainedCache go node
  where
    go = getAll . crush free
    free (Node es) = All (all ((== EmptyConstraints) . edgeEcs) es)
    free _ = All True

---------------
--- Debugging
---------------

-- | Find a reachable node by interned node id.
getSubnodeById :: Node symbol -> Id -> Maybe (Node symbol)
getSubnodeById n i = getFirst $ crush (onNormalNodes $ \x -> if nodeIdentity x == i then First (Just x) else First Nothing) n
