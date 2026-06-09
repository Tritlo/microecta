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

    -- * Membership of templates
    nodeRepresentsTemplate,
    edgeRepresentsTemplate,

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

import Control.Monad.State.Strict (MonadState (..), State, evalState, modify')
import qualified Data.HashMap.Strict as HashMap
import Data.Hashable (Hashable (..), hash)
import Data.List (inits, tails)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import Data.Monoid (First (..), Sum (..))
import Data.Semigroup (Max (..))
import Data.Set (Set)
import qualified Data.Set as Set

import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Internal.Paths
import Data.ECTA.Internal.Term

import Data.Interned.Extended.HashTableBased (Id)

import Data.Memoization (MemoCacheTag (..), memo, memo2)
import Utility.Fixpoint
import Utility.HashJoin

------------------------------------------------------------------------------------

mapWithIndex :: (Int -> a -> b) -> [a] -> [b]
mapWithIndex f = zipWith f [0 ..]

atMay :: Int -> [a] -> Maybe a
atMay i xs
    | i < 0 = Nothing
    | otherwise = case drop i xs of
        x : _ -> Just x
        [] -> Nothing

adjustAt :: Int -> (a -> a) -> [a] -> [a]
adjustAt i f xs
    | i < 0 = xs
    | otherwise = case splitAt i xs of
        (prefix, x : suffix) -> prefix ++ f x : suffix
        _ -> xs

-----------------------
------ Traversal
-----------------------

{- | Apply an edge transformation to the outgoing alternatives of a node.

This is a shallow operation: for a normal @Node@ it maps over that node's
edges, and for a 'Mu' it first unfolds the outer recursion and then maps those
edges. It does not recursively traverse child nodes. Spectacular uses this
shape to push environment/equality-constraint edits across every immediate
alternative of an ECTA node without changing the node's children directly.
-}
nodeMapChildren :: (Edge -> Edge) -> Node -> Node
nodeMapChildren _ EmptyNode = EmptyNode
nodeMapChildren f n@(Mu _) = nodeMapChildren f (unfoldOuterRec n)
nodeMapChildren f (Node es) = Node (map f es)
nodeMapChildren _ (Rec _) = error "nodeMapChildren: unexpected Rec"

{- | Warning: Linear in number of paths, exponential in size of graph.
  Only use for very small graphs.
-}
pathsMatching :: (Node -> Bool) -> Node -> [Path]
pathsMatching _ EmptyNode = []
pathsMatching _ (Mu _) = [] -- Unsound!
pathsMatching f n@(Node es) =
    (concat $ map pathsMatchingEdge es)
        ++ if f n then [EmptyPath] else []
  where
    pathsMatchingEdge :: Edge -> [Path]
    pathsMatchingEdge (Edge _ ns) = concat $ mapWithIndex (\i x -> map (ConsPath i) $ pathsMatching f x) ns
pathsMatching _ (Rec _) = error $ "pathsMatching: unexpected Rec"

{- | Precondition: For all i, f (Rec i) is either a Rec node meant to represent
                the enclosing Mu, or contains no Rec node not beneath another Mu.
-}
mapNodes :: (Node -> Node) -> Node -> Node
mapNodes f = go
  where
    -- \| Memoized separately for each mapNodes invocation
    go :: Node -> Node
    go = memo (NameTag "mapNodes") go'
    {-# NOINLINE go #-}

    go' :: Node -> Node
    go' EmptyNode = EmptyNode
    go' (Node es) = f $ (Node $ map (\e -> setChildren e $ (map go (edgeChildren e))) es)
    go' (Mu n) = f $ Mu (go . n)
    go' (Rec i) = f $ Rec i

{- | Fold over all reachable nodes with sharing awareness.

This name originates from the @crush@ operator in the Stratego language.
Although @m@ is only constrained to be a monoid, this function makes no
guarantees about traversal order.
-}
crush :: forall m. (Monoid m) => (Node -> m) -> Node -> m
crush f = \n -> evalState (go n) Set.empty
  where
    go :: (Monoid m) => Node -> State (Set Id) m
    go EmptyNode = return mempty
    go (Rec _) = return mempty
    go n@(InternedMu mu) = mappend (f n) <$> go (internedMuBody mu)
    go n@(InternedNode node) = do
        seen <- get
        let nId = nodeIdentity n
        if Set.member nId seen
            then
                return mempty
            else do
                modify' (Set.insert nId)
                mappend (f n) <$> (mconcat <$> mapM (\(Edge _ ns) -> mconcat <$> mapM go ns) (internedNodeEdges node))

-- | Run a fold function only on normal non-recursive nodes.
onNormalNodes :: (Monoid m) => (Node -> m) -> (Node -> m)
onNormalNodes f n@(Node _) = f n
onNormalNodes _ _ = mempty

-----------------------
------ Folding
-----------------------

-- | Unfold one outer 'Mu' layer.
unfoldOuterRec :: Node -> Node
unfoldOuterRec n@(Mu x) = x n
unfoldOuterRec _ = error "unfoldOuterRec: Must be called on a Mu node"

-- | Outgoing alternatives of a node, unfolding one outer 'Mu' if needed.
nodeEdges :: Node -> [Edge]
nodeEdges (Node es) = es
nodeEdges n@(Mu _) = nodeEdges (unfoldOuterRec n)
nodeEdges _ = []

-- | Replace repeated unfoldings with recursive 'Mu' nodes where possible.
refold :: Node -> Node
refold = memo (NameTag "refold") go
  where
    go :: Node -> Node
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

-- | Unfold recursive nodes at most the given number of rounds.
unfoldBounded :: Int -> Node -> Node
unfoldBounded 0 =
    mapNodes
        ( \case
            Mu _ -> EmptyNode
            n -> n
        )
unfoldBounded k =
    unfoldBounded (k - 1)
        . mapNodes
            ( \case
                n@(Mu _) -> unfoldOuterRec n
                n -> n
            )

------------
------ Size operations
------------

-- | Count reachable non-recursive nodes, sharing-aware.
nodeCount :: Node -> Int
nodeCount = getSum . crush (onNormalNodes $ const $ Sum 1)

-- | Count reachable outgoing edges, sharing-aware.
edgeCount :: Node -> Int
edgeCount = getSum . crush (onNormalNodes go)
  where
    go (Node es) = Sum (length es)
    go _ = mempty

-- | Maximum number of outgoing alternatives on any reachable normal node.
maxIndegree :: Node -> Int
maxIndegree = getMax . crush (onNormalNodes go)
  where
    go (Node es) = Max (length es)
    go _ = mempty

------------
------ Membership
------------

-- | Test whether a node accepts a concrete term.
nodeRepresents :: Node -> Term -> Bool
nodeRepresents EmptyNode _ = False
nodeRepresents (Node es) t = any (\e -> edgeRepresents e t) es
nodeRepresents n@(Mu _) t = nodeRepresents (unfoldOuterRec n) t
nodeRepresents _ _ = False

-- | Test whether an edge accepts a concrete term.
edgeRepresents :: Edge -> Term -> Bool
edgeRepresents e = \t@(Term s ts) ->
    s == edgeSymbol e
        && childrenRepresent (edgeChildren e) ts
        && all (eclassSatisfied t) (unsafeGetEclasses $ edgeEcs e)
  where
    childrenRepresent [] [] = True
    childrenRepresent (n : ns) (t : ts) = nodeRepresents n t && childrenRepresent ns ts
    childrenRepresent _ _ = False

    eclassSatisfied :: Term -> PathEClass -> Bool
    eclassSatisfied t pec = allTheSame $ map (\p -> getPath p t) $ unPathEClass pec

    allTheSame :: (Eq a) => [a] -> Bool
    allTheSame =
        \case
            [] -> True
            x : xs -> go x xs
      where
        go !_ [] = True
        go !x (!y : ys) = (x == y) && (go x ys)
    {-# INLINE allTheSame #-}

{- | Test whether a node can represent a template term.

This is the pruning-oriented variant of 'nodeRepresents', not a concrete
membership predicate. It delegates to 'edgeRepresentsTemplate', whose template
language treats the exact symbol @"<v>"@ as a wildcard for the edge symbol and
checks only the template children that are present. Pruning oracles use this
before expanding a UVar: if the current node already represents a forbidden
rewrite/template, the whole branch can be dropped without enumerating a full
term.
-}
nodeRepresentsTemplate :: Node -> Term -> Bool
nodeRepresentsTemplate EmptyNode _ = False
nodeRepresentsTemplate (Node es) t = any (`edgeRepresentsTemplate` t) es
nodeRepresentsTemplate n@(Mu _) t = nodeRepresentsTemplate (unfoldOuterRec n) t
nodeRepresentsTemplate _ _ = False

{- | Test whether one edge can represent a template term.

The term matches normally when its symbol is the edge symbol. It also matches
when the term symbol is exactly @"<v>"@, in which case the symbol is treated
as a wildcard. This is a prefix-style matcher: supplied template children must
match, but omitted template children are unresolved holes.
-}
edgeRepresentsTemplate :: Edge -> Term -> Bool
edgeRepresentsTemplate e = \t@(Term s@(Symbol txt) ts) ->
    let childrenSatisfied = and (zipWith nodeRepresentsTemplate (edgeChildren e) ts)
        consSatisfied = all (eclassSatisfied t) (unsafeGetEclasses $ edgeEcs e)
     in (s == edgeSymbol e && childrenSatisfied && consSatisfied)
            || (txt == "<v>" && childrenSatisfied && consSatisfied)
  where
    eclassSatisfied :: Term -> PathEClass -> Bool
    eclassSatisfied t pec = allTheSame $ map (\p -> getPath p t) $ unPathEClass pec

    allTheSame :: (Eq a) => [a] -> Bool
    allTheSame =
        \case
            [] -> True
            x : xs -> go x xs
      where
        go !_ [] = True
        go !x (!y : ys) = (x == y) && (go x ys)
    {-# INLINE allTheSame #-}

------------
------ Intersect
------------

{-# NOINLINE intersect #-}

data RuleOutRes = Keep | RuledOutBy Edge

-- | Remove edges that are subsumed by another edge with the same symbol.
dropRedundantEdges :: [Edge] -> [Edge]
dropRedundantEdges origEs = concatMap reduceCluster $ {- traceShow (map (\es -> (length es, edgeSymbol $ head es)) clusters, length $ concatMap reduceCluster clusters)-} clusters
  where
    clusters = map (nubByIdSinglePass edgeId) $ clusterByHash (hash . edgeSymbol) origEs

    reduceCluster :: [Edge] -> [Edge]
    reduceCluster [] = []
    reduceCluster (e : es) = case ruleOut e es of
        -- Optimization: If e' > e, likely to be greater than other things;
        -- move it to front and rule out more stuff next iteration.
        --
        -- No noticeable difference in overall wall clock time (7/2/21),
        -- but a few % reduction in calls to intersectEdgeSameSymbol
        (RuledOutBy e', es') -> reduceCluster (e' : es')
        (Keep, es') -> e : reduceCluster es'

    ruleOut :: Edge -> [Edge] -> (RuleOutRes, [Edge])
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

-- | Intersect two edges when they have the same symbol.
intersectEdge :: Edge -> Edge -> Maybe Edge
intersectEdge e1 e2
    | edgeSymbol e1 /= edgeSymbol e2 = Nothing
    | otherwise = Just $ intersectEdgeSameSymbol e1 e2

intersectEdgeSameSymbol :: Edge -> Edge -> Edge
intersectEdgeSameSymbol = memo2 (NameTag "intersectEdgeSameSymbol") go
  where
    go e1 e2
        | e2 < e1 = intersectEdgeSameSymbol e2 e1
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
intersect :: Node -> Node -> Node
intersect l r = intersectOpen (emptyIntersectionDom, l, r)

------ Intersection internals

{- | Intersection domain

Information required to compute the intersection of open terms.
-}
data IntersectionDom = ID
    { idFree :: Map Id Node
    -- ^ Value of all free variables inside the term (so that we can unfold when necessary)
    , idRecInt :: Set IntersectId
    -- ^ Intersection problems we encountered previously (to avoid infinite unrolling)
    }
    deriving (Show, Eq)

instance Hashable IntersectionDom where
    -- Implementation notes:
    --
    -- - Both `Map.toList` and `Set.toList` return elements in key-order, which is a suitable canonical form for hashing.
    -- - The cost of the hashing is linear in the size of the domain. If this becomes a concern, we could cache the hash.
    hashWithSalt s (ID free recInt) = hashWithSalt s (Map.toList free, Set.toList recInt)

emptyIntersectionDom :: IntersectionDom
emptyIntersectionDom = ID Map.empty Set.empty

intersectOpen :: (IntersectionDom, Node, Node) -> Node
{-# NOINLINE intersectOpen #-}
intersectOpen = memo (NameTag "intersectOpen") (\(dom, l, r) -> onNode dom l r)
  where
    onNode :: IntersectionDom -> Node -> Node -> Node
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
                        (hash . edgeSymbol)
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
        extendEnv :: [(Id, Node)] -> IntersectionDom
        extendEnv bindings =
            ID
                { idFree = Map.union (Map.fromList bindings) (idFree dom)
                , idRecInt = Set.insert (IntersectId i j) (idRecInt dom)
                }

        -- Find value of free variables in the terms
        -- Since we assume the input terms are fully interned, we only deal with 'RecInt'.
        findFreeVar :: RecNodeId -> Node
        findFreeVar (RecInt intId) | Just n <- Map.lookup intId (idFree dom) = n
        findFreeVar recId = error $ "findFreeVar: unexpected " <> show recId

        -- We only insert a 'Mu' node when necessary.
        maybeMu :: Node -> Node
        maybeMu n
            | RecIntersect (IntersectId i j) `Set.member` freeVars n =
                Mu $ \recNode -> substFree (RecIntersect (IntersectId i j)) recNode n
            | otherwise =
                n

-- | Auxiliary to 'intersectOpen'.
intersectOpenEdge :: (IntersectionDom, Edge, Edge) -> Edge
{-# NOINLINE intersectOpenEdge #-}
intersectOpenEdge = memo (NameTag "intersectOpenEdge") (\(dom, l, r) -> onEdge dom l r)
  where
    onEdge :: IntersectionDom -> Edge -> Edge -> Edge
    onEdge !dom l r =
        mkEdge
            (edgeSymbol l)
            (zipWith (\a b -> intersectOpen (dom, a, b)) (edgeChildren l) (edgeChildren r))
            (edgeEcs l `combineEqConstraints` edgeEcs r)

------------
------ Union
------------

-- | Union a list of ECTAs by concatenating their alternatives.
union :: [Node] -> Node
union ns = case foldr collect (False, []) ns of
    (False, _) -> EmptyNode
    (_, es) -> Node es
  where
    collect EmptyNode acc = acc
    collect n (_, es) = (True, nodeEdges n ++ es)

----------------------
------ Path operations
----------------------

-- | Restrict an ECTA to terms that contain the given path.
requirePath :: Path -> Node -> Node
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
requirePathList :: Path -> [Node] -> [Node]
requirePathList EmptyPath ns = ns
requirePathList (ConsPath p ps) ns = adjustAt p (requirePath ps) ns

instance Pathable Node Node where
    type Emptyable Node = Node

    getPath _ EmptyNode = EmptyNode
    getPath EmptyPath n = n
    getPath p n@(Mu _) = getPath p (unfoldOuterRec n)
    getPath (ConsPath p ps) (Node es) = union $ map (getPath ps) (mapMaybe goEdge es)
      where
        goEdge :: Edge -> Maybe Node
        goEdge (Edge _ ns) = atMay p ns
    getPath p n = error $ "getPath: unexpected path " <> show p <> " for node " <> show n

    getAllAtPath _ EmptyNode = []
    getAllAtPath EmptyPath n = [n]
    getAllAtPath p n@(Mu _) = getAllAtPath p (unfoldOuterRec n)
    getAllAtPath (ConsPath p ps) (Node es) = concatMap (getAllAtPath ps) (mapMaybe goEdge es)
      where
        goEdge :: Edge -> Maybe Node
        goEdge (Edge _ ns) = atMay p ns
    getAllAtPath p n = error $ "getAllAtPath: unexpected path " <> show p <> " for node " <> show n

    modifyAtPath f EmptyPath n = f n
    modifyAtPath _ _ EmptyNode = EmptyNode
    modifyAtPath f p n@(Mu _) = modifyAtPath f p (unfoldOuterRec n)
    modifyAtPath f (ConsPath p ps) (Node es) = Node (map goEdge es)
      where
        goEdge :: Edge -> Edge
        goEdge e = setChildren e (adjustAt p (modifyAtPath f ps) (edgeChildren e))
    modifyAtPath _ p n = error $ "modifyAtPath: unexpected path " <> show p <> " for node " <> show n

instance Pathable [Node] Node where
    type Emptyable Node = Node

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

-- | Remove alternatives represented by another alternative in the same node.
withoutRedundantEdges :: Node -> Node
withoutRedundantEdges n = mapNodes dropReds n
  where
    dropReds (Node es) = Node (dropRedundantEdges es)
    dropReds x = x

---------------
--- Reducing Equality Constraints
---------------

-- | Propagate equality constraints through one reduction pass.
reducePartially :: Node -> Node
reducePartially = reducePartially' EmptyConstraints

reducePartially' :: EqConstraints -> Node -> Node
reducePartially' = memo2 (NameTag "reducePartially'") go
  where
    go :: EqConstraints -> Node -> Node
    go _ EmptyNode = EmptyNode
    go _ (Mu n) = Mu n
    go inheritedEcs n@(Node _) = modifyNode n $ \es ->
        map (reduceChildren inheritedEcs) $
            map (reduceEdgeIntersection inheritedEcs) es
    go _ (Rec _) = error "reducePartially: unexpected Rec"

    reduceChildren :: EqConstraints -> Edge -> Edge
    reduceChildren inheritedEcs e = setChildren e $ reduceWithInheritedEcs (inheritedEcs `combineEqConstraints` edgeEcs e) (edgeChildren e)

    -- \| Reduce children with inherited constraints
    --
    -- This function is used to avoid infinite unfolding of recursive nodes,
    -- and we do this by passing constraints from the current edge and ancestors to descendants.
    -- For example, let `tau` be "any" node, and we define
    --
    -- > let n1 = Node [ mkEdge "Pair" [tau, tau] (mkEqConstraints [[path [0, 0], path [0, 1], path [1]]])]
    -- > let n2 = Node [ Edge "Pair" [tau, tau] ]
    -- > let n  = Node [ mkEdge "Pair" [n1, n2]   (mkEqConstraints [[path [0, 0], path [0, 1], path [1]]])]
    --
    -- We notice that, if we call `reducePartially n` without propagating constraints down to its children `n1` or `n2`,
    -- the `tau` can be infinitely expanded between rounds of reduction.
    --
    -- To break such cycles, we actively pass constraints down to children.
    -- In this example, we first call `reducePartially' EmptyConstraints n` at the top level, where the inherited constraint is empty,
    -- so we only need to consider the constraints from the current edge.
    -- Then, we pass the constraints `0.0=0.1=1` down to its children, and `n1` receives `0=1` and `n2` receives nothing.
    -- Next, we reduce the children of `n` by calling `reducePartially' (mkEqConstraints [[path [0], path [1]]]) n1`.
    -- At this node, we will have to combine the inherited constraints `0=1` and the local constraints `0.0=0.1=1`.
    -- Now, we can see that these two constraints contain a contradiction that requires `0=0.0=0.1`, so we can drop the edge.
    --
    -- TODO: this approach does not solve every recursive cycle.
    reduceWithInheritedEcs :: EqConstraints -> [Node] -> [Node]
    reduceWithInheritedEcs EqContradiction children = map (const EmptyNode) children
    reduceWithInheritedEcs inheritedEcs children = zipWith (\i -> reducePartially' (eqConstraintsDescend inheritedEcs i)) [0 ..] children
{-# NOINLINE reducePartially' #-}

-- | Reduce an edge's children using inherited constraints from ancestors.
reduceEdgeIntersection :: EqConstraints -> Edge -> Edge
reduceEdgeIntersection = memo2 (NameTag "reduceEdgeIntersection") go
  where
    go :: EqConstraints -> Edge -> Edge
    go ecs e =
        mkEdge
            (edgeSymbol e)
            (reduceEqConstraints (edgeEcs e) ecs (edgeChildren e))
            (edgeEcs e)
{-# NOINLINE reduceEdgeIntersection #-}

-- | Apply local and inherited equality constraints to a child list.
reduceEqConstraints :: EqConstraints -> EqConstraints -> [Node] -> [Node]
reduceEqConstraints = go
  where
    propagateEmptyNodes :: [Node] -> [Node]
    propagateEmptyNodes ns = if EmptyNode `elem` ns then map (const EmptyNode) ns else ns

    go :: EqConstraints -> EqConstraints -> [Node] -> [Node]
    go EmptyConstraints EmptyConstraints origNs = origNs
    go ecs inheritedEcs origNs
        | constraintsAreContradictory (ecs `combineEqConstraints` inheritedEcs) = map (const EmptyNode) origNs
        | otherwise = propagateEmptyNodes $ foldr reduceEClass withNeededChildren eclasses
      where
        eclasses = unsafeSubsumptionOrderedEclasses ecs

        -- \| TODO: Replace with a "requirePathTrie"
        withNeededChildren = foldr requirePathList origNs (concatMap unPathEClass eclasses)

        intersectList :: [Node] -> Node
        intersectList [] = EmptyNode
        intersectList (n : ns) = foldr intersect n ns

        reduceEClass :: PathEClass -> [Node] -> [Node]
        reduceEClass pec ns =
            foldr
                (\(p, nsRestIntersected) ns' -> modifyAtPath (intersect nsRestIntersected) p ns')
                ns
                (zip ps (toIntersect ns ps))
          where
            ps = unPathEClass pec

        toIntersect :: [Node] -> [Path] -> [Node]
        toIntersect ns [p1, p2] = [getPath p2 ns, getPath p1 ns]
        toIntersect ns ps = map intersectList $ dropOnes $ map (`getPath` ns) ps

        -- \| dropOnes [1,2,3,4] = [[2,3,4], [1,3,4], [1,2,4], [1,2,3]]
        dropOnes :: [a] -> [[a]]
        dropOnes xs = zipWith (++) (inits xs) (drop 1 $ tails xs)

---------------
--- Debugging
---------------

-- | Find a reachable node by interned node id.
getSubnodeById :: Node -> Id -> Maybe Node
getSubnodeById n i = getFirst $ crush (onNormalNodes $ \x -> if nodeIdentity x == i then First (Just x) else First Nothing) n
