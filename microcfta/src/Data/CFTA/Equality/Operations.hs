{-# LANGUAGE OverloadedStrings #-}

{- | Operations that interpret path equalities: reduction, concrete
membership, and template restriction. Most users import "Data.CFTA.Equality".

'reducePartially' and 'reduceEdgeIntersection' are memoized per alphabet;
the interned 'Symbol' alphabet has its own table.
-}
module Data.CFTA.Equality.Operations (
    nodeRepresents,
    edgeRepresents,
    reducePartially,
    reduceEdgeIntersection,
    reduceEqConstraints,
    termsMatching,
) where

import Data.Hashable (Hashable (..))
import Data.List (inits, tails)
import qualified Data.Tree as Tree
import Data.Type.Equality ((:~~:) (HRefl))
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (Typeable, eqTypeRep, typeRep)

import Data.CFTA.Constraint.Equality
import Data.CFTA.Interned
import Data.CFTA.Interned.Memo (
    MemoCache,
    TypeableMemoCache,
    memo2TypeableWith,
    memo2With,
    newMemoCache,
    newTypeableMemoCache,
 )
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Template (Template (..), restrict)

------------
------ Membership
------------

{- | Whether a term agrees with itself everywhere an edge's constraints say it
must.

'unsafeGetEclasses' is safe here: 'mkEdge' collapses a contradictory
constraint set to 'emptyEdge', so no interned edge carries 'EqContradiction'.
-}
equalitiesSatisfied :: (Eq symbol) => EqConstraints -> Tree.Tree symbol -> Bool
equalitiesSatisfied constraints t = all eclassSatisfied (unsafeGetEclasses constraints)
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

-- | Recognize through the common traversal and the equality interpreter.
nodeRepresents :: (Hashable symbol, Typeable symbol) => Node symbol EqConstraints -> Tree.Tree symbol -> Bool
nodeRepresents = nodeRepresentsWith equalitiesSatisfied

-- | Recognize one edge through the common traversal.
edgeRepresents :: (Hashable symbol, Typeable symbol) => Edge symbol EqConstraints -> Tree.Tree symbol -> Bool
edgeRepresents = edgeRepresentsWith equalitiesSatisfied

------------------------------------
------ Reduction
------------------------------------

{- | Propagate equality constraints through one reduction pass.

One pass narrows every child by the constraints that reach it, but a nested
constrained edge can narrow a child after an outer edge has already read it.
Iterate to a fixpoint, as 'fixUnbounded' does, when every
constrained position must agree with every other.
-}
reducePartially :: (Hashable symbol, Typeable symbol) => Node symbol EqConstraints -> Node symbol EqConstraints
reducePartially = reducePartially' EmptyConstraints

symbolReducePartiallyCache :: MemoCache (EqConstraints, Node Symbol EqConstraints) (Node Symbol EqConstraints)
symbolReducePartiallyCache = unsafePerformIO newMemoCache
{-# NOINLINE symbolReducePartiallyCache #-}

genericReducePartiallyCache :: TypeableMemoCache
genericReducePartiallyCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericReducePartiallyCache #-}

reducePartially' ::
    forall symbol.
    (Hashable symbol, Typeable symbol) => EqConstraints -> Node symbol EqConstraints -> Node symbol EqConstraints
reducePartially' constraints node = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> memo2With symbolReducePartiallyCache go constraints node
    Nothing -> memo2TypeableWith genericReducePartiallyCache go constraints node
  where
    go :: EqConstraints -> Node symbol EqConstraints -> Node symbol EqConstraints
    go _ EmptyNode = EmptyNode
    go _ (Mu n) = Mu n
    go inheritedEcs n@(Node _) = modifyNode n $ \es ->
        map
            (reduceChildren inheritedEcs . reduceEdgeIntersection inheritedEcs)
            es
    go _ (Rec _) = error "reducePartially: unexpected Rec"

    reduceChildren :: EqConstraints -> Edge symbol EqConstraints -> Edge symbol EqConstraints
    reduceChildren inheritedEcs e =
        setChildren e $ reduceWithInheritedEcs (inheritedEcs `combineEqConstraints` edgeConstraint e) (edgeChildren e)

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
    reduceWithInheritedEcs :: EqConstraints -> [Node symbol EqConstraints] -> [Node symbol EqConstraints]
    reduceWithInheritedEcs EqContradiction children = map (const EmptyNode) children
    reduceWithInheritedEcs inheritedEcs children = zipWith (\i -> reducePartially' (eqConstraintsDescend inheritedEcs i)) [0 ..] children
{-# NOINLINE reducePartially' #-}

-- | Reduce an edge's children using inherited constraints from ancestors.
symbolReduceEdgeIntersectionCache :: MemoCache (EqConstraints, Edge Symbol EqConstraints) (Edge Symbol EqConstraints)
symbolReduceEdgeIntersectionCache = unsafePerformIO newMemoCache
{-# NOINLINE symbolReduceEdgeIntersectionCache #-}

genericReduceEdgeIntersectionCache :: TypeableMemoCache
genericReduceEdgeIntersectionCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericReduceEdgeIntersectionCache #-}

-- | Narrow an edge's children by its own and the inherited equality constraints.
reduceEdgeIntersection ::
    forall symbol.
    (Hashable symbol, Typeable symbol) => EqConstraints -> Edge symbol EqConstraints -> Edge symbol EqConstraints
reduceEdgeIntersection constraints edge = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> memo2With symbolReduceEdgeIntersectionCache go constraints edge
    Nothing -> memo2TypeableWith genericReduceEdgeIntersectionCache go constraints edge
  where
    go :: EqConstraints -> Edge symbol EqConstraints -> Edge symbol EqConstraints
    go ecs e =
        mkEdge
            (edgeSymbol e)
            (reduceEqConstraints (edgeConstraint e) ecs (edgeChildren e))
            (edgeConstraint e)
{-# NOINLINE reduceEdgeIntersection #-}

{- | Apply local and inherited equality constraints to a child list.
Nested constraints can require further passes. This pass is not idempotent.
-}
reduceEqConstraints ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    EqConstraints ->
    EqConstraints ->
    [Node symbol EqConstraints] ->
    [Node symbol EqConstraints]
reduceEqConstraints = go
  where
    propagateEmptyNodes :: [Node symbol EqConstraints] -> [Node symbol EqConstraints]
    propagateEmptyNodes ns = if EmptyNode `elem` ns then map (const EmptyNode) ns else ns

    go :: EqConstraints -> EqConstraints -> [Node symbol EqConstraints] -> [Node symbol EqConstraints]
    go EmptyConstraints EmptyConstraints origNs = origNs
    go ecs inheritedEcs origNs
        | constraintsAreContradictory (ecs `combineEqConstraints` inheritedEcs) = map (const EmptyNode) origNs
        | otherwise = propagateEmptyNodes $ foldr reduceEClass withNeededChildren eclasses
      where
        eclasses = unsafeSubsumptionOrderedEclasses ecs

        -- \| TODO: Replace with a "requirePathTrie"
        withNeededChildren = foldr requirePathList origNs (concatMap unPathEClass eclasses)

        intersectList :: [Node symbol EqConstraints] -> Node symbol EqConstraints
        intersectList [] = EmptyNode
        intersectList (n : ns) = foldr intersect n ns

        reduceEClass :: PathEClass -> [Node symbol EqConstraints] -> [Node symbol EqConstraints]
        reduceEClass pec ns =
            foldr
                (\(p, nsRestIntersected) ns' -> modifyAtPath (intersect nsRestIntersected) p ns')
                ns
                (zip ps (toIntersect ns ps))
          where
            ps = unPathEClass pec

        toIntersect :: [Node symbol EqConstraints] -> [Path] -> [Node symbol EqConstraints]
        toIntersect ns [p1, p2] = [getPath p2 ns, getPath p1 ns]
        toIntersect ns ps = map intersectList $ dropOnes $ map (`getPath` ns) ps

        -- \| dropOnes [1,2,3,4] = [[2,3,4], [1,3,4], [1,2,4], [1,2,3]]
        dropOnes :: [a] -> [[a]]
        dropOnes xs = zipWith (++) (inits xs) (drop 1 $ tails xs)

{- | Keep exactly the terms in a node that match a template.

The graph is restricted and then reduced, so a 'Hole' at a constrained
position can be narrowed by a concrete pattern at an equal one.
-}
termsMatching ::
    (Hashable symbol, Typeable symbol) => Template symbol -> Node symbol EqConstraints -> Node symbol EqConstraints
termsMatching Hole = id
termsMatching (AnyPrefix []) = id
termsMatching template = reducePartially . restrict template
