{-# LANGUAGE OverloadedStrings #-}

-- | Constraint-independent operations on shared interned automata.
module Data.Tree.FTA.Interned.Operations (
    nodeMapChildren,
    mapNodes,
    crush,
    onNormalNodes,
    unfoldOuterRec,
    refold,
    nodeEdges,
    unfoldBounded,
    nodeCount,
    edgeCount,
    maxIndegree,
    union,
    unionMapMaybe,
    nodeRepresentsWith,
    edgeRepresentsWith,
    dropEdgeConstraints,
    dropConstraints,
    intersect,
    dropRedundantEdges,
    withoutRedundantEdges,
    getSubnodeById,
    intersectEdge,
) where

import Control.Monad.State.Strict (State, evalState, get, modify')
import qualified Data.HashMap.Strict as HashMap
import Data.Hashable (Hashable (..))
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Monoid (First (..), Sum (..))
import Data.Semigroup (Max (..))
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)
import System.IO.Unsafe (unsafePerformIO)

import Data.Interned.Extended.HashTableBased (Id)
import Data.Memoization
import Data.Tree.FTA.Constraint (Constraint (..))
import Data.Tree.FTA.Interned.Type
import Utility.Fixpoint
import Utility.HashJoin

-- | Transform the immediate alternatives of one node.
{-# INLINEABLE nodeMapChildren #-}
nodeMapChildren ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (Edge symbol constraint -> Edge symbol constraint) -> Node symbol constraint -> Node symbol constraint
nodeMapChildren _ EmptyNode = EmptyNode
nodeMapChildren f n@(Mu _) = nodeMapChildren f (unfoldOuterRec n)
nodeMapChildren f (Node es) = Node (map f es)
nodeMapChildren _ (Rec _) = error "nodeMapChildren: unexpected Rec"

-- | Transform each reachable node. Memoize separately for each transformation.
{-# INLINEABLE mapNodes #-}
mapNodes ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (Node symbol constraint -> Node symbol constraint) -> Node symbol constraint -> Node symbol constraint
mapNodes f = go
  where
    -- This table belongs to this transformation.
    go :: Node symbol constraint -> Node symbol constraint
    go = memo (NameTag "mapNodes") (mapNodesStep go f)
    {-# NOINLINE go #-}

-- | Perform one recursive traversal step using the supplied recursive call.
{-# INLINEABLE mapNodesStep #-}
mapNodesStep ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (Node symbol constraint -> Node symbol constraint) ->
    (Node symbol constraint -> Node symbol constraint) ->
    Node symbol constraint ->
    Node symbol constraint
mapNodesStep _ _ EmptyNode = EmptyNode
mapNodesStep recurse f (Node es) =
    f $ Node $ map (\edge -> setChildren edge (map recurse (edgeChildren edge))) es
mapNodesStep recurse f (Mu body) = f $ Mu (recurse . body)
mapNodesStep _ f (Rec recId) = f $ Rec recId

{- | Fold over all reachable nodes with sharing awareness.

This name originates from the @crush@ operator in the Stratego language.
Although @m@ is only constrained to be a monoid, this function makes no
guarantees about traversal order.
-}
{-# INLINEABLE crush #-}
crush :: forall symbol constraint m. (Monoid m) => (Node symbol constraint -> m) -> Node symbol constraint -> m
crush f = \n -> evalState (go n) IntSet.empty
  where
    go :: Node symbol constraint -> State IntSet m
    go EmptyNode = return mempty
    go (Rec _) = return mempty
    go n@(InternedMu mu) = mappend (f n) <$> go (internedMuBody mu)
    go n@(InternedNode node) = do
        seen <- get
        let nId = nodeIdentity n
        if IntSet.member nId seen
            then
                return mempty
            else do
                modify' (IntSet.insert nId)
                mappend (f n) . mconcat <$> mapM (\e -> mconcat <$> mapM go (edgeChildren e)) (internedNodeEdges node)

-- | Run a fold function only on normal non-recursive nodes.
{-# INLINEABLE onNormalNodes #-}
onNormalNodes :: forall symbol constraint m. (Monoid m) => (Node symbol constraint -> m) -> Node symbol constraint -> m
onNormalNodes f n@(InternedNode _) = f n
onNormalNodes _ _ = mempty

-- Folding

-- | Unfold one outer 'Mu' layer.
{-# INLINEABLE unfoldOuterRec #-}
unfoldOuterRec ::
    (Hashable symbol, Typeable symbol, Constraint constraint) => Node symbol constraint -> Node symbol constraint
unfoldOuterRec n@(Mu x) = x n
unfoldOuterRec _ = error "unfoldOuterRec: Must be called on a Mu node"

-- | Outgoing alternatives of a node, unfolding one outer 'Mu' if needed.
{-# INLINEABLE nodeEdges #-}
nodeEdges ::
    (Hashable symbol, Typeable symbol, Constraint constraint) => Node symbol constraint -> [Edge symbol constraint]
nodeEdges (InternedNode node) = internedNodeEdges node
nodeEdges n@(Mu _) = nodeEdges (unfoldOuterRec n)
nodeEdges _ = []

-- | Tables for recursive refolding.
genericRefoldCache :: TypeableMemoCache
genericRefoldCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericRefoldCache #-}

-- | Replace repeated unfoldings with recursive nodes where possible.
{-# INLINEABLE refold #-}
refold ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) => Node symbol constraint -> Node symbol constraint
refold node = memoTypeableWith genericRefoldCache go node
  where
    go :: Node symbol constraint -> Node symbol constraint
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

        tryUnfold x = fromMaybe x (HashMap.lookup x muNodeMap)

{- | Unfold recursive nodes at most the given number of rounds.

A bound of zero or less unfolds nothing and replaces every 'Mu' with
'EmptyNode', leaving only the terms that need no recursion at all. Matching
@0@ alone would leave a negative bound counting down forever.
-}
{-# INLINEABLE unfoldBounded #-}
unfoldBounded ::
    (Hashable symbol, Typeable symbol, Constraint constraint) => Int -> Node symbol constraint -> Node symbol constraint
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

-- Size operations

-- | Count reachable non-recursive nodes, sharing-aware.
{-# INLINEABLE nodeCount #-}
nodeCount :: Node symbol constraint -> Int
nodeCount = getSum . crush (onNormalNodes $ const $ Sum 1)

-- | Count reachable outgoing edges, sharing-aware.
{-# INLINEABLE edgeCount #-}
edgeCount :: Node symbol constraint -> Int
edgeCount = getSum . crush (onNormalNodes go)
  where
    go (InternedNode node) = Sum (length (internedNodeEdges node))
    go _ = mempty

{- | Maximum number of outgoing alternatives on any reachable normal node.

Zero when there is no normal node to count, as for 'EmptyNode': the @Max@
monoid's identity is @minBound@, which is not an answer anyone can use.
-}
{-# INLINEABLE maxIndegree #-}
maxIndegree :: Node symbol constraint -> Int
maxIndegree = max 0 . getMax . crush (onNormalNodes go)
  where
    go (InternedNode node) = Max (length (internedNodeEdges node))
    go _ = mempty

-- | Replace the edge constraint with the unconstrained value.
{-# INLINEABLE dropEdgeConstraints #-}
dropEdgeConstraints ::
    (Hashable symbol, Typeable symbol, Constraint constraint) => Edge symbol constraint -> Edge symbol constraint
dropEdgeConstraints e = Edge (edgeSymbol e) (edgeChildren e)

-- | Tables for constraint removal.
genericDropConstraintsCache :: TypeableMemoCache
genericDropConstraintsCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericDropConstraintsCache #-}

-- | Remove every edge constraint. This can broaden the accepted language.
{-# INLINEABLE dropConstraints #-}
dropConstraints ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) => Node symbol constraint -> Node symbol constraint
dropConstraints node = memoTypeableWith genericDropConstraintsCache go node
  where
    go = mapNodesStep dropConstraints dropNodeConstraints

    dropNodeConstraints (Node es) = Node (map dropEdgeConstraints es)
    dropNodeConstraints n = n

-- Intersect

-- | Result of comparing one alternative with the remaining alternatives.
data RuleOutRes symbol constraint = Keep | RuledOutBy (Edge symbol constraint)

-- | Remove edges that are subsumed by another edge with the same symbol.
{-# INLINEABLE dropRedundantEdges #-}
dropRedundantEdges ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) => [Edge symbol constraint] -> [Edge symbol constraint]
dropRedundantEdges origEs = concatMap reduceCluster clusters
  where
    clusters = map (nubByIdSinglePass edgeId) $ clusterByHash edgeSymbol origEs

    reduceCluster :: [Edge symbol constraint] -> [Edge symbol constraint]
    reduceCluster [] = []
    reduceCluster (e : es) = case ruleOut e es of
        -- Optimization: If e' > e, likely to be greater than other things;
        -- move it to front and rule out more stuff next iteration.
        --
        -- No noticeable difference in overall wall clock time (7/2/21),
        -- but a few % reduction in calls to intersectEdgeSameSymbol
        (RuledOutBy e', es') -> reduceCluster (e' : es')
        (Keep, es') -> e : reduceCluster es'

    ruleOut ::
        Edge symbol constraint -> [Edge symbol constraint] -> (RuleOutRes symbol constraint, [Edge symbol constraint])
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
{-# INLINEABLE intersectEdge #-}
intersectEdge ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Edge symbol constraint -> Edge symbol constraint -> Maybe (Edge symbol constraint)
intersectEdge e1 e2
    | edgeSymbol e1 /= edgeSymbol e2 = Nothing
    | length (edgeChildren e1) /= length (edgeChildren e2) = Nothing
    | otherwise = Just $ intersectEdgeSameSymbol e1 e2

-- | Tables for intersection of edges with the same symbol.
genericIntersectEdgeSameSymbolCache :: TypeableMemoCache
genericIntersectEdgeSameSymbolCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericIntersectEdgeSameSymbolCache #-}

-- | Intersect edges with equal symbols and reject unequal arities.
intersectEdgeSameSymbol ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Edge symbol constraint -> Edge symbol constraint -> Edge symbol constraint
intersectEdgeSameSymbol left right = memo2TypeableWith genericIntersectEdgeSameSymbolCache go left right
  where
    go e1 e2
        | e2 < e1 = intersectEdgeSameSymbol e2 e1
    go e1 e2
        | length (edgeChildren e1) /= length (edgeChildren e2) = emptyEdge (edgeSymbol e1)
    go e1 e2 =
        mkEdge
            (edgeSymbol e1)
            (zipWith intersect (edgeChildren e1) (edgeChildren e2))
            (edgeConstraint e1 `conjoinConstraints` edgeConstraint e2)
{-# INLINEABLE intersectEdgeSameSymbol #-}

-- | Intersection of two automata.
intersect ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Node symbol constraint -> Node symbol constraint -> Node symbol constraint
intersect l r = intersectOpen (emptyIntersectionDom, l, r)
{-# INLINEABLE intersect #-}

-- Intersection internals

{- | Intersection domain

Information required to compute the intersection of open terms.
-}
data IntersectionDom symbol constraint = ID
    { idFree :: IntMap (Node symbol constraint)
    -- ^ Value of all free variables inside the term (so that we can unfold when necessary)
    , idRecInt :: Set IntersectId
    -- ^ Intersection problems we encountered previously (to avoid infinite unrolling)
    }
    deriving (Eq)

instance Hashable (IntersectionDom symbol constraint) where
    -- Implementation notes:
    --
    -- - Both `IntMap.toList` and `Set.toList` return elements in key-order, which is a suitable canonical form for hashing.
    -- - The cost of the hashing is linear in the size of the domain. If this becomes a concern, we could cache the hash.
    hashWithSalt s (ID free recInt) = hashWithSalt s (IntMap.toList free, Set.toList recInt)

-- | An intersection environment with no free or pending variables.
{-# INLINEABLE emptyIntersectionDom #-}
emptyIntersectionDom :: IntersectionDom symbol constraint
emptyIntersectionDom = ID IntMap.empty Set.empty

-- | Tables for node intersection in a recursive environment.
genericIntersectOpenCache :: TypeableMemoCache
genericIntersectOpenCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericIntersectOpenCache #-}

-- | Intersect two nodes under the same recursive environment.
intersectOpen ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (IntersectionDom symbol constraint, Node symbol constraint, Node symbol constraint) -> Node symbol constraint
{-# INLINEABLE intersectOpen #-}
intersectOpen input = memoTypeableWith genericIntersectOpenCache worker input
  where
    worker (dom, left, right) = onNode dom left right

    onNode ::
        IntersectionDom symbol constraint -> Node symbol constraint -> Node symbol constraint -> Node symbol constraint
    onNode !dom l r =
        case (l, r) of
            -- Rule out empty cases first
            -- This justifies the use of nodeIdentity (@i@, @j@) for the other cases
            (EmptyNode, _) -> EmptyNode
            (_, EmptyNode) -> EmptyNode
            -- For closed terms, improve memoization performance by using the empty environment
            _ | Set.null (freeVars l), Set.null (freeVars r), not (IntMap.null (idFree dom)) -> l `intersect` r
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
        extendEnv :: [(Id, Node symbol constraint)] -> IntersectionDom symbol constraint
        extendEnv bindings =
            ID
                { idFree = IntMap.union (IntMap.fromList bindings) (idFree dom)
                , idRecInt = Set.insert (IntersectId i j) (idRecInt dom)
                }

        -- Find value of free variables in the terms
        -- Since we assume the input terms are fully interned, we only deal with 'RecInt'.
        findFreeVar :: RecNodeId -> Node symbol constraint
        findFreeVar (RecInt intId) | Just n <- IntMap.lookup intId (idFree dom) = n
        findFreeVar recId = error $ "findFreeVar: unexpected " <> show recId

        -- We only insert a 'Mu' node when necessary.
        maybeMu :: Node symbol constraint -> Node symbol constraint
        maybeMu n
            | RecIntersect (IntersectId i j) `Set.member` freeVars n =
                Mu $ \recNode -> substFree (RecIntersect (IntersectId i j)) recNode n
            | otherwise =
                n

-- | Tables for edge intersection in a recursive environment.
genericIntersectOpenEdgeCache :: TypeableMemoCache
genericIntersectOpenEdgeCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericIntersectOpenEdgeCache #-}

-- | Intersect two edges under the same recursive environment.
intersectOpenEdge ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (IntersectionDom symbol constraint, Edge symbol constraint, Edge symbol constraint) -> Edge symbol constraint
{-# INLINEABLE intersectOpenEdge #-}
intersectOpenEdge input = memoTypeableWith genericIntersectOpenEdgeCache worker input
  where
    worker (dom, left, right) = onEdge dom left right

    onEdge ::
        IntersectionDom symbol constraint -> Edge symbol constraint -> Edge symbol constraint -> Edge symbol constraint
    onEdge _ l r | length (edgeChildren l) /= length (edgeChildren r) = emptyEdge (edgeSymbol l)
    onEdge !dom l r =
        mkEdge
            (edgeSymbol l)
            (zipWith (\a b -> intersectOpen (dom, a, b)) (edgeChildren l) (edgeChildren r))
            (edgeConstraint l `conjoinConstraints` edgeConstraint r)

-- Union

{- | Union a list of automata by concatenating their alternatives.

'EmptyNode' and 'Rec' contribute no alternatives, and the @Node@ constructor
maps an empty alternative list back to 'EmptyNode', so the empty cases need no
special handling.
-}
{-# INLINEABLE union #-}
union :: (Hashable symbol, Typeable symbol, Constraint constraint) => [Node symbol constraint] -> Node symbol constraint
union = Node . concatMap nodeEdges

-- | Union the nodes a partial function produces; see 'union'.
{-# INLINEABLE unionMapMaybe #-}
unionMapMaybe ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (a -> Maybe (Node symbol constraint)) -> [a] -> Node symbol constraint
unionMapMaybe f = union . mapMaybe f

-- | Recognize a term with an explicit pure constraint interpreter.
{-# INLINEABLE nodeRepresentsWith #-}
nodeRepresentsWith ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (constraint -> Tree.Tree symbol -> Bool) -> Node symbol constraint -> Tree.Tree symbol -> Bool
nodeRepresentsWith _ EmptyNode _ = False
nodeRepresentsWith acceptsConstraint (Node es) term = any (\edge -> edgeRepresentsWith acceptsConstraint edge term) es
nodeRepresentsWith acceptsConstraint node@(Mu _) term = nodeRepresentsWith acceptsConstraint (unfoldOuterRec node) term
nodeRepresentsWith _ _ _ = False

-- | Recognize one constructor and apply its constraint interpreter.
{-# INLINEABLE edgeRepresentsWith #-}
edgeRepresentsWith ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (constraint -> Tree.Tree symbol -> Bool) -> Edge symbol constraint -> Tree.Tree symbol -> Bool
edgeRepresentsWith acceptsConstraint edge term@(Tree.Node symbol children) =
    symbol == edgeSymbol edge
        && childrenRepresent (edgeChildren edge) children
        && acceptsConstraint (edgeConstraint edge) term
  where
    childrenRepresent [] [] = True
    childrenRepresent (node : nodes) (child : rest) = nodeRepresentsWith acceptsConstraint node child && childrenRepresent nodes rest
    childrenRepresent _ _ = False

-- | Tables for removal of redundant alternatives.
genericWithoutRedundantEdgesCache :: TypeableMemoCache
genericWithoutRedundantEdgesCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericWithoutRedundantEdgesCache #-}

-- | Remove alternatives implied by another alternative at each node.
{-# INLINEABLE withoutRedundantEdges #-}
withoutRedundantEdges ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) => Node symbol constraint -> Node symbol constraint
withoutRedundantEdges node = memoTypeableWith genericWithoutRedundantEdgesCache go node
  where
    go = mapNodesStep withoutRedundantEdges dropReds

    dropReds (Node es) = Node (dropRedundantEdges es)
    dropReds x = x

-- | Find a reachable non-recursive node by its canonical identity.
{-# INLINEABLE getSubnodeById #-}
getSubnodeById :: Node symbol constraint -> Id -> Maybe (Node symbol constraint)
getSubnodeById node ident =
    getFirst $
        crush (onNormalNodes $ \current -> if nodeIdentity current == ident then First (Just current) else First Nothing) node
