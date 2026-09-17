{-# LANGUAGE OverloadedStrings #-}
-- For the 'Pathable' instance for 'Node'
{-# OPTIONS_GHC -Wno-orphans #-}

{- | Core ECTA operations.

This module contains traversal, intersection, union, reduction, and
constraint-propagation logic. Most users should import "Data.ECTA" instead; the
module is exposed so downstream code can reach lower-level helpers when needed.
Its exports are not covered by the PVP contract of the package.
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

import Data.Coerce (coerce)
import Data.Hashable (Hashable (..))
import Data.List (compareLength, inits, tails, (!?))
import Data.Maybe (mapMaybe)
import qualified Data.Tree as Tree
import Data.Type.Equality ((:~~:) (HRefl))
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (Typeable, eqTypeRep, typeRep)

import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Internal.Paths
import Data.ECTA.Internal.Term (Symbol)
import qualified Data.Tree.FTA.Interned.Operations as Common

import Data.Interned.Extended.HashTableBased (Id)

import Data.Memoization (
    MemoCache,
    TypeableMemoCache,
    memo2TypeableWith,
    memo2With,
    newMemoCache,
    newTypeableMemoCache,
 )
import Utility.List (adjustAt)

------------------------------------------------------------------------------------

mapWithIndex :: (Int -> a -> b) -> [a] -> [b]
mapWithIndex f = zipWith f [0 ..]

-----------------------
------ Traversal
-----------------------

{- | Paths to every reachable node that satisfies a predicate.

Linear in the number of paths and exponential in the size of the graph, so
use it on very small graphs only. A recursive node contributes no paths: the
search does not unfold recursion, so a match below a 'Mu' is not reported.
-}
pathsMatching :: (Node symbol -> Bool) -> Node symbol -> [Path]
pathsMatching _ EmptyNode = []
pathsMatching _ (InternedMu _) = []
pathsMatching f n@(InternedNode node) =
    (concatMap pathsMatchingEdge es)
        ++ ([EmptyPath | f n])
  where
    es = internedNodeEdges node
    pathsMatchingEdge e = concat $ mapWithIndex (\i x -> map (ConsPath i) $ pathsMatching f x) (edgeChildren e)
pathsMatching _ (Rec _) = error "pathsMatching: unexpected Rec"

------------
------ Membership
------------

{- | Whether a term agrees with itself everywhere an edge's constraints say it
must.

'unsafeGetEclasses' is safe here: 'mkEdge' collapses a contradictory
constraint set to 'emptyEdge', so no interned edge carries 'EqContradiction'.
-}
equalitiesSatisfied :: (Eq symbol) => EqConstraints -> Tree.Tree symbol -> Bool
equalitiesSatisfied equalities t = all eclassSatisfied (unsafeGetEclasses equalities)
  where
    eclassSatisfied :: PathEClass -> Bool
    eclassSatisfied pec = allTheSame $ map (`getPath` t) $ unPathEClass pec

    allTheSame :: (Eq a) => [a] -> Bool
    allTheSame [] = True
    allTheSame (x : xs) = go x xs
      where
        go !_ [] = True
        go !y (!z : zs) = (y == z) && go y zs
    {-# INLINE allTheSame #-}

----------------------
------ Path operations
----------------------

-- | Restrict an ECTA to terms that contain the given path.
requirePath :: (Hashable symbol, Typeable symbol) => Path -> Node symbol -> Node symbol
requirePath EmptyPath n = n
requirePath _ EmptyNode = EmptyNode
requirePath p n@(Mu _) = requirePath p (unfoldOuterRec n)
requirePath (ConsPath p ps) (Node es) =
    Node
        $ map (\e -> setChildren e (requirePathList (ConsPath p ps) (edgeChildren e)))
        $ filter
            (\e -> compareLength (edgeChildren e) p == GT)
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
        goEdge (Edge _ ns) = getPath ps <$> ns !? p
    getPath p _ = error $ "getPath: unexpected path " <> show p <> " for unresolved node"

    getAllAtPath _ EmptyNode = []
    getAllAtPath EmptyPath n = [n]
    getAllAtPath p n@(Mu _) = getAllAtPath p (unfoldOuterRec n)
    getAllAtPath (ConsPath p ps) (Node es) = concatMap (getAllAtPath ps) (mapMaybe goEdge es)
      where
        goEdge :: Edge symbol -> Maybe (Node symbol)
        goEdge (Edge _ ns) = ns !? p
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
    getPath (ConsPath p ps) ns = case ns !? p of
        Nothing -> EmptyNode
        Just n -> getPath ps n

    getAllAtPath EmptyPath _ = []
    getAllAtPath (ConsPath p ps) ns = case ns !? p of
        Nothing -> []
        Just n -> getAllAtPath ps n

    modifyAtPath _ EmptyPath ns = ns
    modifyAtPath f (ConsPath p ps) ns = adjustAt p (modifyAtPath f ps) ns

------------------------------------
------ Reduction
------------------------------------

{- | Propagate equality constraints through one reduction pass.

One pass narrows every child by the constraints that reach it, but a nested
constrained edge can narrow a child after an outer edge has already read it.
Iterate to a fixpoint, as 'Utility.Fixpoint.fixUnbounded' does, when every
constrained position must agree with every other.
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
        map
            (reduceChildren inheritedEcs . reduceEdgeIntersection inheritedEcs)
            es
    go _ (Rec _) = error "reducePartially: unexpected Rec"

    reduceChildren :: EqConstraints -> Edge symbol -> Edge symbol
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
    reduceWithInheritedEcs :: EqConstraints -> [Node symbol] -> [Node symbol]
    reduceWithInheritedEcs EqContradiction children = map (const EmptyNode) children
    reduceWithInheritedEcs inheritedEcs children = zipWith (\i -> reducePartially' (eqConstraintsDescend inheritedEcs i)) [0 ..] children
{-# NOINLINE reducePartially' #-}

-- | Reduce an edge's children using inherited constraints from ancestors.
symbolReduceEdgeIntersectionCache :: MemoCache (EqConstraints, Edge Symbol) (Edge Symbol)
symbolReduceEdgeIntersectionCache = unsafePerformIO newMemoCache
{-# NOINLINE symbolReduceEdgeIntersectionCache #-}

genericReduceEdgeIntersectionCache :: TypeableMemoCache
genericReduceEdgeIntersectionCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericReduceEdgeIntersectionCache #-}

-- | Narrow an edge's children by its own and the inherited equality constraints.
reduceEdgeIntersection ::
    forall symbol. (Hashable symbol, Typeable symbol) => EqConstraints -> Edge symbol -> Edge symbol
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

{- | Apply local and inherited equality constraints to a child list.
Nested constraints can require further passes. This pass is not idempotent.
-}
reduceEqConstraints ::
    forall symbol. (Hashable symbol, Typeable symbol) => EqConstraints -> EqConstraints -> [Node symbol] -> [Node symbol]
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
        eclasses = unsafeSubsumptionOrderedEclasses ecs

        -- \| TODO: Replace with a "requirePathTrie"
        withNeededChildren = foldr requirePathList origNs (concatMap unPathEClass eclasses)

        intersectList :: [Node symbol] -> Node symbol
        intersectList [] = EmptyNode
        intersectList (n : ns) = foldr intersect n ns

        reduceEClass :: PathEClass -> [Node symbol] -> [Node symbol]
        reduceEClass pec ns =
            foldr
                (\(p, nsRestIntersected) ns' -> modifyAtPath (intersect nsRestIntersected) p ns')
                ns
                (zip ps (toIntersect ns ps))
          where
            ps = unPathEClass pec

        toIntersect :: [Node symbol] -> [Path] -> [Node symbol]
        toIntersect ns [p1, p2] = [getPath p2 ns, getPath p1 ns]
        toIntersect ns ps = map intersectList $ dropOnes $ map (`getPath` ns) ps

        -- \| dropOnes [1,2,3,4] = [[2,3,4], [1,3,4], [1,2,4], [1,2,3]]
        dropOnes :: [a] -> [[a]]
        dropOnes xs = zipWith (++) (inits xs) (drop 1 $ tails xs)

---------------
--- Common engine specializations
---------------

{- The wrappers below specialize the shared engine to 'EqConstraints'. Each
one checks at run time whether the symbol is the interned 'Symbol' and, if
so, calls the engine at that concrete type. Both branches compute the same
value; the split exists so GHC specializes the INLINEABLE engine code for the
common alphabet, which the common-engine benchmarks rely on. -}

-- | Change the immediate alternatives.
nodeMapChildren ::
    forall symbol. (Hashable symbol, Typeable symbol) => (Edge symbol -> Edge symbol) -> Node symbol -> Node symbol
nodeMapChildren = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.nodeMapChildren @Symbol @EqConstraints)
    Nothing -> coerce (Common.nodeMapChildren @symbol @EqConstraints)

-- | Transform a shared graph.
mapNodes ::
    forall symbol. (Hashable symbol, Typeable symbol) => (Node symbol -> Node symbol) -> Node symbol -> Node symbol
mapNodes = coerce (Common.mapNodes @symbol @EqConstraints)

-- | Fold a graph with shared-node tracking.
crush :: forall symbol m. (Monoid m) => (Node symbol -> m) -> Node symbol -> m
crush = coerce (Common.crush @symbol @EqConstraints @m)

-- | Apply a fold only to non-recursive nodes.
onNormalNodes :: forall symbol m. (Monoid m) => (Node symbol -> m) -> Node symbol -> m
onNormalNodes = coerce (Common.onNormalNodes @symbol @EqConstraints @m)

-- | Unfold one outer recursive binder.
unfoldOuterRec :: forall symbol. (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol
unfoldOuterRec = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.unfoldOuterRec @Symbol @EqConstraints)
    Nothing -> coerce (Common.unfoldOuterRec @symbol @EqConstraints)

-- | Recover recursive binders from repeated unfoldings.
refold :: forall symbol. (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol
refold = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.refold @Symbol @EqConstraints)
    Nothing -> coerce (Common.refold @symbol @EqConstraints)

-- | Read alternatives, unfolding one recursive binder if needed.
nodeEdges :: forall symbol. (Hashable symbol, Typeable symbol) => Node symbol -> [Edge symbol]
nodeEdges = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.nodeEdges @Symbol @EqConstraints)
    Nothing -> coerce (Common.nodeEdges @symbol @EqConstraints)

-- | Unfold at most the specified number of rounds.
unfoldBounded :: forall symbol. (Hashable symbol, Typeable symbol) => Int -> Node symbol -> Node symbol
unfoldBounded = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.unfoldBounded @Symbol @EqConstraints)
    Nothing -> coerce (Common.unfoldBounded @symbol @EqConstraints)

-- | Count reachable non-recursive nodes.
nodeCount :: forall symbol. Node symbol -> Int
nodeCount = coerce (Common.nodeCount @symbol @EqConstraints)

-- | Count alternatives of reachable non-recursive nodes.
edgeCount :: forall symbol. Node symbol -> Int
edgeCount = coerce (Common.edgeCount @symbol @EqConstraints)

-- | Find the largest alternative count.
maxIndegree :: forall symbol. Node symbol -> Int
maxIndegree = coerce (Common.maxIndegree @symbol @EqConstraints)

-- | Forget the equality constraint on one edge.
dropEdgeConstraints :: forall symbol. (Hashable symbol, Typeable symbol) => Edge symbol -> Edge symbol
dropEdgeConstraints = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.dropEdgeConstraints @Symbol @EqConstraints)
    Nothing -> coerce (Common.dropEdgeConstraints @symbol @EqConstraints)

-- | Forget equality constraints throughout the graph.
dropConstraints :: forall symbol. (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol
dropConstraints = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.dropConstraints @Symbol @EqConstraints)
    Nothing -> coerce (Common.dropConstraints @symbol @EqConstraints)

-- | Intersect structure and conjoin path equalities.
intersect :: forall symbol. (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol -> Node symbol
intersect = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.intersect @Symbol @EqConstraints)
    Nothing -> coerce (Common.intersect @symbol @EqConstraints)

-- | Intersect compatible constructor alternatives.
intersectEdge :: forall symbol. (Hashable symbol, Typeable symbol) => Edge symbol -> Edge symbol -> Maybe (Edge symbol)
intersectEdge = coerce (Common.intersectEdge @symbol @EqConstraints)

-- | Remove implied alternatives.
dropRedundantEdges :: forall symbol. (Hashable symbol, Typeable symbol) => [Edge symbol] -> [Edge symbol]
dropRedundantEdges = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.dropRedundantEdges @Symbol @EqConstraints)
    Nothing -> coerce (Common.dropRedundantEdges @symbol @EqConstraints)

-- | Remove implied alternatives throughout the graph.
withoutRedundantEdges :: forall symbol. (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol
withoutRedundantEdges = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.withoutRedundantEdges @Symbol @EqConstraints)
    Nothing -> coerce (Common.withoutRedundantEdges @symbol @EqConstraints)

-- | Combine alternatives from several nodes.
union :: forall symbol. (Hashable symbol, Typeable symbol) => [Node symbol] -> Node symbol
union = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.union @Symbol @EqConstraints)
    Nothing -> coerce (Common.union @symbol @EqConstraints)

-- | Combine the nodes returned by a partial function.
unionMapMaybe :: forall symbol a. (Hashable symbol, Typeable symbol) => (a -> Maybe (Node symbol)) -> [a] -> Node symbol
unionMapMaybe = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.unionMapMaybe @Symbol @EqConstraints @a)
    Nothing -> coerce (Common.unionMapMaybe @symbol @EqConstraints @a)

-- | Find a non-recursive node by canonical identity.
getSubnodeById :: forall symbol. Node symbol -> Id -> Maybe (Node symbol)
getSubnodeById = coerce (Common.getSubnodeById @symbol @EqConstraints)

-- | Recognize through the common traversal and the equality interpreter.
nodeRepresents :: (Hashable symbol, Typeable symbol) => Node symbol -> Tree.Tree symbol -> Bool
nodeRepresents node = Common.nodeRepresentsWith equalitiesSatisfied (toInterned node)

-- | Recognize one edge through the common traversal.
edgeRepresents :: forall symbol. (Hashable symbol, Typeable symbol) => Edge symbol -> Tree.Tree symbol -> Bool
edgeRepresents = coerce (Common.edgeRepresentsWith @symbol @EqConstraints equalitiesSatisfied)
