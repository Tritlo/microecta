{-# LANGUAGE OverloadedStrings #-}

{- | Operations that interpret path equalities: reduction, concrete
membership, and template restriction. Most users import "Data.CFTA.Equality".

'reducePartially' and 'reduceEdgeIntersection' narrow children by the
'equalities' of the edge constraints. They are memoized per alphabet.
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
import Data.List (compareLength, (!?))
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (Typeable)

import Data.CFTA.Enumeration (unconstrained)
import Data.CFTA.Equality.Constraint
import Data.CFTA.Internal.Tree (adjustAt)
import Data.CFTA.Interned
import Data.CFTA.Interned.Memo (
    TypeableMemoCache,
    memo2TypeableWith,
    newTypeableMemoCache,
 )
import Data.CFTA.Path (ChildIndex (..), Path (..), Pathable (..))
import Data.CFTA.Template (Template (..), restrict)

------------
------ Membership
------------

{- | Recognize through the common traversal and the equality interpreter. A
constraint's residual beyond its path equalities is not decided here.
-}
accepts :: (Hashable symbol, Typeable symbol) => Node symbol -> Tree.Tree symbol -> Bool
accepts = acceptsWith equalitiesHold

------------------------------------
------ Reduction
------------------------------------

{- | Propagate equality constraints through one reduction pass.

One pass narrows every child by the constraints that reach it, but a nested
constrained edge can narrow a child after an outer edge has already read it.
Iterate to a fixpoint, as 'fixUnbounded' does, when every
constrained position must agree with every other.

The pass does not unfold a recursive node that has constraints. A class that
reaches into such a node stays unreduced (see 'reduceEqConstraints'). The
language does not change, because enumeration and 'accepts' still check that
class.
-}
reducePartially ::
    (Hashable symbol, Typeable symbol) => Node symbol -> Node symbol
reducePartially = reducePartially' EmptyConstraints

genericReducePartiallyCache :: TypeableMemoCache
genericReducePartiallyCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericReducePartiallyCache #-}

reducePartially' ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    EqConstraints -> Node symbol -> Node symbol
reducePartially' constraints node =
    memo2TypeableWith @symbol genericReducePartiallyCache go constraints node
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
    -- This does not stop every recursive cycle. A cycle through a recursive
    -- node with constraints stops because 'reduceEqConstraints' does not
    -- unfold that node. 'go' returns a recursive node unchanged, so one pass
    -- visits a finite part of the input, and only the fixpoint in
    -- 'reduceEqConstraints' can repeat. No proof shows that this fixpoint, or
    -- a repetition of passes, ends on every input. The reduction tests "stops
    -- on the example that needs inherited constraints", "stops on a class over
    -- three recursive children", and "stops on classes over recursive
    -- children" check this example and random recursive inputs.
    reduceWithInheritedEcs :: EqConstraints -> [Node symbol] -> [Node symbol]
    reduceWithInheritedEcs EqContradiction children = map (const EmptyNode) children
    reduceWithInheritedEcs inheritedEcs children = zipWith (\i -> reducePartially' (eqConstraintsDescend inheritedEcs i)) [0 ..] children
{-# NOINLINE reducePartially' #-}

genericReduceEdgeIntersectionCache :: TypeableMemoCache
genericReduceEdgeIntersectionCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericReduceEdgeIntersectionCache #-}

-- | Narrow an edge's children by its own and the inherited equality constraints.
reduceEdgeIntersection ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    EqConstraints -> Edge symbol -> Edge symbol
reduceEdgeIntersection constraints edge =
    memo2TypeableWith @symbol genericReduceEdgeIntersectionCache go constraints edge
  where
    go :: EqConstraints -> Edge symbol -> Edge symbol
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

A class stays unreduced when one of its paths meets a recursive node with
constraints, at the end of the path or before it. Unfolding such a node shows
its constrained edges again, and their reduction unfolds the node again. A
recursive node without constraints can unfold, because its unfolding has no
constraints to reduce.
-}
reduceEqConstraints ::
    forall symbol.
    (Hashable symbol, Typeable symbol) =>
    EqConstraints ->
    EqConstraints ->
    [Node symbol] ->
    [Node symbol]
reduceEqConstraints local inherited = fixUnbounded (go local inherited)
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

        withNeededChildren = requireAll (Set.unions $ map unPathEClass eclasses) origNs

        intersectList :: [Node symbol] -> Node symbol
        intersectList [] = EmptyNode
        intersectList (n : ns) = foldr intersect n ns

        -- Narrow the node at each path of the class to the nodes at the other paths.
        reduceEClass :: PathEClass -> [Node symbol] -> [Node symbol]
        reduceEClass pec ns =
            editAll
                [ (p, intersect $ intersectList [getPath other ns | other <- Set.toAscList paths, other /= p])
                | p <- Set.toAscList paths
                ]
                ns
          where
            paths = unPathEClass pec

    -- Whether a path meets a recursive node with constraints, at the end of
    -- the path or before it. A free recursive reference counts as such a
    -- node: pruning a recursive body leaves references to the node that is
    -- being pruned, and its edges are not known there. So does a node with
    -- free references at the end of the path, and an unconstrained recursive
    -- node with free references is followed through its unfolding.
    meetsConstrainedMu :: [Node symbol] -> Path -> Bool
    meetsConstrainedMu ns (ConsPath (ChildIndex index) rest) = maybe False (nodeMeetsConstrainedMu rest) (ns !? index)
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
    insertNeeded (ConsPath (ChildIndex index) rest) (Needed children) =
        Needed $ IntMap.alter (Just . insertNeeded rest . fromMaybe (Needed IntMap.empty)) index children

    requireList :: Needed -> [Node symbol] -> [Node symbol]
    requireList (Needed children) ns = IntMap.foldrWithKey (\index needed -> adjustAt (ChildIndex index) (requireNode needed)) ns children

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
    insertEdit (ConsPath (ChildIndex index) rest) f (EditBelow children) =
        EditBelow $ IntMap.alter (Just . insertEdit rest f . fromMaybe (EditBelow IntMap.empty)) index children
    insertEdit (ConsPath _ _) _ leaf@(EditAt _) = leaf

    editList :: Edits symbol -> [Node symbol] -> [Node symbol]
    editList (EditAt _) ns = ns
    editList (EditBelow children) ns = IntMap.foldrWithKey (\index below -> adjustAt (ChildIndex index) (editNode below)) ns children

    editNode :: Edits symbol -> Node symbol -> Node symbol
    editNode (EditAt f) n = f n
    editNode _ EmptyNode = EmptyNode
    editNode below n@(Mu _) = editNode below (unfoldOuterRec n)
    editNode below (Node es) = Node (map (\e -> setChildren e (editList below (edgeChildren e))) es)
    editNode _ (Rec _) = error "editAll: unexpected Rec"

{- | Keep exactly the terms in a node that match a template.

The graph is restricted and then reduced, so a 'Hole' at a constrained
position can be narrowed by a concrete pattern at an equal one. 'restrict'
keeps an edge only if its symbol and arity can match, restricts its children
with the child templates, and keeps the edge constraints. The reduction only
narrows the children and removes no accepted term. So the result accepts
exactly the terms of the node that match the template. 'restrict' does not end
on a 'Mu' whose body is its own variable, which only 'createMuDontCleanup' can
build: @createMu (\r -> r)@ is 'EmptyNode'.
-}
termsMatching ::
    (Hashable symbol, Typeable symbol) =>
    Template symbol -> Node symbol -> Node symbol
termsMatching Hole = id
termsMatching (AnyPrefix []) = id
termsMatching template = reducePartially . restrict template
