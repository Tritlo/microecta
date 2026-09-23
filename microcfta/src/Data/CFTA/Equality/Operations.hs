{-# LANGUAGE OverloadedStrings #-}

{- | Operations that interpret path equalities: reduction, concrete
membership, and template restriction. Most users import "Data.CFTA.Equality".

'reducePartially' and 'reduceEdgeIntersection' narrow children by the
'equalities' of any constraint theory. They are memoized per alphabet and
theory; the interned 'Symbol' alphabet with 'EqConstraints' has its own table.
-}
module Data.CFTA.Equality.Operations (
    accepts,
    reducePartially,
    reduceEdgeIntersection,
    reduceEqConstraints,
    termsMatching,
) where

import Data.Hashable (Hashable (..))
import qualified Data.IntMap.Strict as IntMap
import Data.List (compareLength, inits, tails)
import Data.Maybe (fromMaybe)
import qualified Data.Tree as Tree
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (Typeable)

import Data.CFTA.Equality.Constraint
import Data.CFTA.Internal.Tree (adjustAt)
import Data.CFTA.Interned
import Data.CFTA.Interned.Memo (
    MemoCache,
    TypeableMemoCache,
    memo2TypeableWith,
    memo2With,
    newMemoCache,
    newTypeableMemoCache,
 )
import Data.CFTA.Path (Path (..), Pathable (..))
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
accepts :: (Hashable symbol, Typeable symbol) => Node symbol EqConstraints -> Tree.Tree symbol -> Bool
accepts = acceptsWith equalitiesSatisfied

------------------------------------
------ Reduction
------------------------------------

{- | Propagate equality constraints through one reduction pass.

One pass narrows every child by the constraints that reach it, but a nested
constrained edge can narrow a child after an outer edge has already read it.
Iterate to a fixpoint, as 'fixUnbounded' does, when every
constrained position must agree with every other.
-}
reducePartially ::
    (Hashable symbol, Typeable symbol, Constraint constraint) => Node symbol constraint -> Node symbol constraint
reducePartially = reducePartially' EmptyConstraints

symbolReducePartiallyCache :: MemoCache (EqConstraints, Node Symbol EqConstraints) (Node Symbol EqConstraints)
symbolReducePartiallyCache = unsafePerformIO newMemoCache
{-# NOINLINE symbolReducePartiallyCache #-}

genericReducePartiallyCache :: TypeableMemoCache
genericReducePartiallyCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericReducePartiallyCache #-}

reducePartially' ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    EqConstraints -> Node symbol constraint -> Node symbol constraint
reducePartially' constraints node =
    onCommon @symbol @constraint
        (memo2With symbolReducePartiallyCache go constraints node)
        (memo2TypeableWith @symbol @constraint genericReducePartiallyCache go constraints node)
  where
    go :: EqConstraints -> Node symbol constraint -> Node symbol constraint
    go _ EmptyNode = EmptyNode
    go _ (Mu n) = Mu n
    go inheritedEcs n@(Node _) = modifyNode n $ \es ->
        map
            (reduceChildren inheritedEcs . reduceEdgeIntersection inheritedEcs)
            es
    go _ (Rec _) = error "reducePartially: unexpected Rec"

    reduceChildren :: EqConstraints -> Edge symbol constraint -> Edge symbol constraint
    reduceChildren inheritedEcs e =
        setChildren e $
            reduceWithInheritedEcs (inheritedEcs `combineEqConstraints` equalities (edgeConstraint e)) (edgeChildren e)

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
    reduceWithInheritedEcs :: EqConstraints -> [Node symbol constraint] -> [Node symbol constraint]
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
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    EqConstraints -> Edge symbol constraint -> Edge symbol constraint
reduceEdgeIntersection constraints edge =
    onCommon @symbol @constraint
        (memo2With symbolReduceEdgeIntersectionCache go constraints edge)
        (memo2TypeableWith @symbol @constraint genericReduceEdgeIntersectionCache go constraints edge)
  where
    go :: EqConstraints -> Edge symbol constraint -> Edge symbol constraint
    go ecs e =
        mkEdge
            (edgeSymbol e)
            (reduceEqConstraints (equalities (edgeConstraint e)) ecs (edgeChildren e))
            (edgeConstraint e)
{-# NOINLINE reduceEdgeIntersection #-}

{- | Apply local and inherited equality constraints to a child list.

One pass over the classes is not always enough: the intersection for one class
can narrow a node that a class earlier in the pass already read. The reduction
repeats the pass until the children stop changing, so the result is a
fixpoint. Constraints on nested edges can still require further passes of
'reducePartially'.
-}
reduceEqConstraints ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    EqConstraints ->
    EqConstraints ->
    [Node symbol constraint] ->
    [Node symbol constraint]
reduceEqConstraints local inherited = fixUnbounded (go local inherited)
  where
    propagateEmptyNodes :: [Node symbol constraint] -> [Node symbol constraint]
    propagateEmptyNodes ns = if EmptyNode `elem` ns then map (const EmptyNode) ns else ns

    go :: EqConstraints -> EqConstraints -> [Node symbol constraint] -> [Node symbol constraint]
    go EmptyConstraints EmptyConstraints origNs = origNs
    go ecs inheritedEcs origNs
        | constraintsAreContradictory (ecs `combineEqConstraints` inheritedEcs) = map (const EmptyNode) origNs
        | otherwise = propagateEmptyNodes $ foldr reduceEClass withNeededChildren eclasses
      where
        eclasses = unsafeSubsumptionOrderedEclasses ecs

        withNeededChildren = requireAll (concatMap unPathEClass eclasses) origNs

        intersectList :: [Node symbol constraint] -> Node symbol constraint
        intersectList [] = EmptyNode
        intersectList (n : ns) = foldr intersect n ns

        reduceEClass :: PathEClass -> [Node symbol constraint] -> [Node symbol constraint]
        reduceEClass pec ns = editAll (zip ps (map intersect (toIntersect ns ps))) ns
          where
            ps = unPathEClass pec

        toIntersect :: [Node symbol constraint] -> [Path] -> [Node symbol constraint]
        toIntersect ns [p1, p2] = [getPath p2 ns, getPath p1 ns]
        toIntersect ns ps = map intersectList $ dropOnes $ map (`getPath` ns) ps

        -- \| dropOnes [1,2,3,4] = [[2,3,4], [1,3,4], [1,2,4], [1,2,3]]
        dropOnes :: [a] -> [[a]]
        dropOnes xs = zipWith (++) (inits xs) (drop 1 $ tails xs)

-- | A trie of child positions that must exist. An empty map ends a required path.
newtype Needed = Needed (IntMap.IntMap Needed)

{- | Restrict a child list to the terms that contain every path, in one
traversal. This gives the same nodes as requiring the paths one at a time.
-}
requireAll ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    [Path] -> [Node symbol constraint] -> [Node symbol constraint]
requireAll paths = requireList (foldr insertNeeded (Needed IntMap.empty) paths)
  where
    insertNeeded EmptyPath needed = needed
    insertNeeded (ConsPath index rest) (Needed children) =
        Needed $ IntMap.alter (Just . insertNeeded rest . fromMaybe (Needed IntMap.empty)) index children

    requireList :: Needed -> [Node symbol constraint] -> [Node symbol constraint]
    requireList (Needed children) ns = IntMap.foldrWithKey (\index needed -> adjustAt index (requireNode needed)) ns children

    requireNode :: Needed -> Node symbol constraint -> Node symbol constraint
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
data Edits symbol constraint
    = EditAt (Node symbol constraint -> Node symbol constraint)
    | EditBelow (IntMap.IntMap (Edits symbol constraint))

{- | Apply edits at several paths, none a prefix of another, in one traversal.
This gives the same nodes as 'modifyAtPath' at each path in turn.
-}
editAll ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    [(Path, Node symbol constraint -> Node symbol constraint)] -> [Node symbol constraint] -> [Node symbol constraint]
editAll edits = editList (foldr (uncurry insertEdit) (EditBelow IntMap.empty) edits)
  where
    insertEdit EmptyPath f _ = EditAt f
    insertEdit (ConsPath index rest) f (EditBelow children) =
        EditBelow $ IntMap.alter (Just . insertEdit rest f . fromMaybe (EditBelow IntMap.empty)) index children
    insertEdit (ConsPath _ _) _ leaf@(EditAt _) = leaf

    editList :: Edits symbol constraint -> [Node symbol constraint] -> [Node symbol constraint]
    editList (EditAt _) ns = ns
    editList (EditBelow children) ns = IntMap.foldrWithKey (\index below -> adjustAt index (editNode below)) ns children

    editNode :: Edits symbol constraint -> Node symbol constraint -> Node symbol constraint
    editNode (EditAt f) n = f n
    editNode _ EmptyNode = EmptyNode
    editNode below n@(Mu _) = editNode below (unfoldOuterRec n)
    editNode below (Node es) = Node (map (\e -> setChildren e (editList below (edgeChildren e))) es)
    editNode _ (Rec _) = error "editAll: unexpected Rec"

{- | Keep exactly the terms in a node that match a template.

The graph is restricted and then reduced, so a 'Hole' at a constrained
position can be narrowed by a concrete pattern at an equal one.
-}
termsMatching ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Template symbol -> Node symbol constraint -> Node symbol constraint
termsMatching Hole = id
termsMatching (AnyPrefix []) = id
termsMatching template = reducePartially . restrict template
