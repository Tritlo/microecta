{-# OPTIONS_GHC -Wno-orphans #-}

-- | Constraint-independent operations on shared interned automata.
module Data.CFTA.Interned.Operations (
    nodeMapChildren,
    mapNodes,
    crush,
    unfoldOuterRec,
    refold,
    nodeEdges,
    unfoldBounded,
    boundDepth,
    nodeCount,
    edgeCount,
    union,
    acceptsWith,
    edgeAcceptsWith,
    dropEdgeConstraints,
    dropConstraints,
    intersect,
    dropRedundantEdges,
    withoutRedundantEdges,
    intersectEdge,
    fixUnbounded,
    pathsMatching,
    requirePath,
    onCommon,
) where

import Control.Monad.State.Strict (State, evalState, get, modify')
import qualified Data.HashMap.Lazy as HashMap
import Data.Hashable (Hashable (..))
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List (compareLength, (!?))
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Monoid (Sum (..))
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Data.Type.Equality ((:~~:) (HRefl))
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (Typeable, eqTypeRep, typeRep)

import Data.CFTA.Constraint (Constraint (..))
import Data.CFTA.Equality.Constraint (EqConstraints)
import Data.CFTA.Internal.Tree (adjustAt)
import Data.CFTA.Interned.Cache (Id)
import Data.CFTA.Interned.Memo
import Data.CFTA.Interned.Type
import Data.CFTA.Path (Path (ConsPath, EmptyPath), Pathable (..))
import Data.CFTA.Symbol (Symbol)

{- | Choose the specialization for the common interned alphabet and equality
theory, or the generic definition for any other instantiation.
-}
onCommon ::
    forall symbol constraint r.
    (Typeable symbol, Typeable constraint) =>
    ((symbol ~ Symbol, constraint ~ EqConstraints) => r) ->
    r ->
    r
onCommon common generic =
    case (eqTypeRep (typeRep @symbol) (typeRep @Symbol), eqTypeRep (typeRep @constraint) (typeRep @EqConstraints)) of
        (Just HRefl, Just HRefl) -> common
        _ -> generic
{-# INLINE onCommon #-}

-- | Transform the immediate alternatives of one node.
{-# INLINEABLE nodeMapChildren #-}
nodeMapChildren ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (Edge symbol constraint -> Edge symbol constraint) -> Node symbol constraint -> Node symbol constraint
nodeMapChildren _ EmptyNode = EmptyNode
nodeMapChildren f n@(Mu _) = nodeMapChildren f (unfoldOuterRec n)
nodeMapChildren f (Node es) = Node (map f es)
nodeMapChildren _ (Rec _) = error "nodeMapChildren: unexpected Rec"

{- | Transform each reachable node. Memoize separately for each transformation.

Under a 'Mu', the body is rebuilt three times with different placeholders, so
the function also receives 'Rec' nodes that hold 'RecDepth' and 'RecUnint'.
Return such nodes unchanged.
-}
{-# INLINEABLE mapNodes #-}
mapNodes ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (Node symbol constraint -> Node symbol constraint) -> Node symbol constraint -> Node symbol constraint
mapNodes f = go
  where
    -- This table belongs to this transformation.
    go :: Node symbol constraint -> Node symbol constraint
    go = memo (mapNodesStep go f)
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

{- | Fold over all reachable nodes, visiting each shared node once.

This name originates from the @crush@ operator in the Stratego language.
Although @m@ is only constrained to be a monoid, this function makes no
guarantees about traversal order. Recursive nodes and ordinary nodes draw
identities from one counter, so one visited set covers both.
-}
{-# INLINEABLE crush #-}
crush :: forall symbol constraint m. (Monoid m) => (Node symbol constraint -> m) -> Node symbol constraint -> m
crush f = \n -> evalState (go n) IntSet.empty
  where
    go :: Node symbol constraint -> State IntSet m
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
{-# INLINEABLE onNormalNodes #-}
onNormalNodes :: forall symbol constraint m. (Monoid m) => (Node symbol constraint -> m) -> Node symbol constraint -> m
onNormalNodes f n@(InternedNode _) = f n
onNormalNodes _ _ = mempty

-- Folding

-- | Tables for the unfolding of recursive nodes.
unfoldOuterRecCache :: TypeableMemoCache
unfoldOuterRecCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE unfoldOuterRecCache #-}

-- | Unfold one outer 'Mu' layer. The unfolding of each recursive node is shared.
unfoldOuterRec ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) => Node symbol constraint -> Node symbol constraint
unfoldOuterRec = memoTypeableWith @symbol @constraint unfoldOuterRecCache go
  where
    go n@(Mu x) = x n
    go _ = error "unfoldOuterRec: Must be called on a Mu node"

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
refold node = memoTypeableWith @symbol @constraint genericRefoldCache go node
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

{- | Retain terms whose leaves are at most the given depth from the root.

A leaf has depth zero. A recursive node unfolds until the depth is spent, so
the result is finite for a cyclic input, and a negative depth is the empty
language. Symbols and constraints remain unchanged. The order of alternatives
can change. A node lists its alternatives in the order of their identities,
and a bounded alternative is a new edge with a new identity.
-}
boundDepth ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Int -> Node symbol constraint -> Node symbol constraint
boundDepth maximumDepth root = evalState (go maximumDepth root) Map.empty
  where
    go :: Int -> Node symbol constraint -> State (Map.Map (Int, Id) (Node symbol constraint)) (Node symbol constraint)
    go _ EmptyNode = pure EmptyNode
    go _ (Rec _) = error "boundDepth: unexpected Rec"
    go remaining node
        | remaining < 0 = pure EmptyNode
        | otherwise = do
            known <- get
            case Map.lookup (remaining, nodeIdentity node) known of
                Just bounded -> pure bounded
                Nothing -> do
                    bounded <- case node of
                        Mu _ -> go remaining (unfoldOuterRec node)
                        _ -> Node <$> traverse edge (filter (\e -> remaining > 0 || null (edgeChildren e)) (nodeEdges node))
                    modify' (Map.insert (remaining, nodeIdentity node) bounded)
                    pure bounded
      where
        edge e = setChildren e <$> traverse (go (remaining - 1)) (edgeChildren e)

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
dropConstraints node = memoTypeableWith @symbol @constraint genericDropConstraintsCache go node
  where
    go = mapNodesStep dropConstraints dropNodeConstraints

    dropNodeConstraints (Node es) = Node (map dropEdgeConstraints es)
    dropNodeConstraints n = n

-- Intersect

{- | Remove edges that are subsumed by another edge with the same symbol.

The input is the alternative list of a node, which is already free of
duplicates. The comparison order within a symbol group follows the input.
-}
{-# INLINEABLE dropRedundantEdges #-}
dropRedundantEdges ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) => [Edge symbol constraint] -> [Edge symbol constraint]
dropRedundantEdges origEs = concatMap reduceCluster clusters
  where
    clusters = clusterByHash edgeSymbol origEs

    reduceCluster :: [Edge symbol constraint] -> [Edge symbol constraint]
    reduceCluster [] = []
    reduceCluster (e : es) = case ruleOut e es of
        -- Optimization: If e' > e, likely to be greater than other things;
        -- move it to front and rule out more stuff next iteration.
        --
        -- No noticeable difference in overall wall clock time (7/2/21),
        -- but a few % reduction in calls to intersectEdgeSameSymbol
        (Just e', es') -> reduceCluster (e' : es')
        (Nothing, es') -> e : reduceCluster es'

    -- Drop the alternatives that @e@ accepts, or report one that accepts @e@.
    ruleOut ::
        Edge symbol constraint -> [Edge symbol constraint] -> (Maybe (Edge symbol constraint), [Edge symbol constraint])
    ruleOut _ [] = (Nothing, [])
    ruleOut e (x : xs)
        | common == x = ruleOut e xs
        | common == e = (Just x, xs)
        | otherwise = let (res, notRuledOut) = ruleOut e xs in (res, x : notRuledOut)
      where
        common = intersectEdgeSameSymbol e x

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

commonIntersectEdgeSameSymbolCache ::
    MemoCache (Edge Symbol EqConstraints, Edge Symbol EqConstraints) (Edge Symbol EqConstraints)
commonIntersectEdgeSameSymbolCache = unsafePerformIO newMemoCache
{-# NOINLINE commonIntersectEdgeSameSymbolCache #-}

-- | Intersect edges with equal symbols and reject unequal arities.
intersectEdgeSameSymbol ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Edge symbol constraint -> Edge symbol constraint -> Edge symbol constraint
intersectEdgeSameSymbol left right =
    onCommon @symbol @constraint
        (memo2With commonIntersectEdgeSameSymbolCache go left right)
        (memo2TypeableWith @symbol @constraint genericIntersectEdgeSameSymbolCache go left right)
  where
    go e1 e2
        | e2 < e1 = intersectEdgeSameSymbol e2 e1
        | length (edgeChildren e1) /= length (edgeChildren e2) = emptyEdge (edgeSymbol e1)
        | otherwise =
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
    , idHash :: !Int
    -- ^ Hash of the two fields, computed once: every memo lookup hashes the domain.
    }
    deriving (Eq)

instance Hashable (IntersectionDom symbol constraint) where
    hashWithSalt s dom = hashWithSalt s (idHash dom)

-- | Build a domain and its hash. Both containers list their elements in key order, a canonical form.
mkIntersectionDom :: IntMap (Node symbol constraint) -> Set IntersectId -> IntersectionDom symbol constraint
mkIntersectionDom free recInt = ID free recInt (hash (IntMap.toList free, Set.toList recInt))

-- | An intersection environment with no free or pending variables.
{-# INLINEABLE emptyIntersectionDom #-}
emptyIntersectionDom :: IntersectionDom symbol constraint
emptyIntersectionDom = mkIntersectionDom IntMap.empty Set.empty

-- | Tables for node intersection in a recursive environment.
genericIntersectOpenCache :: TypeableMemoCache
genericIntersectOpenCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericIntersectOpenCache #-}

commonIntersectOpenCache ::
    MemoCache
        (IntersectionDom Symbol EqConstraints, Node Symbol EqConstraints, Node Symbol EqConstraints)
        (Node Symbol EqConstraints)
commonIntersectOpenCache = unsafePerformIO newMemoCache
{-# NOINLINE commonIntersectOpenCache #-}

-- | Intersect two nodes under the same recursive environment.
intersectOpen ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (IntersectionDom symbol constraint, Node symbol constraint, Node symbol constraint) -> Node symbol constraint
{-# INLINEABLE intersectOpen #-}
intersectOpen input =
    onCommon @symbol @constraint
        (memoWith commonIntersectOpenCache worker input)
        (memoTypeableWith @symbol @constraint genericIntersectOpenCache worker input)
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
            -- 2. It will increase the probability of being able to use 'idRecInt'
            _ | l > r -> intersectOpen (dom, r, l)
            -- If we have seen this exact problem before, refer to enclosing Mu.
            _ | Set.member (IntersectId i j) (idRecInt dom) -> Rec (RecIntersect (IntersectId i j))
            -- When encountering a 'Mu', extend the domain appropriately.
            (InternedMu l', InternedMu r') -> maybeMu $ intersectOpen (extendEnv [(i, l), (j, r)], internedMuBody l', internedMuBody r')
            (InternedMu l', _) -> maybeMu $ intersectOpen (extendEnv [(i, l)], internedMuBody l', r)
            (_, InternedMu r') -> maybeMu $ intersectOpen (extendEnv [(j, r)], l, internedMuBody r')
            -- When encountering a free variable, look up the corresponding value in the environment.
            -- (Recall that already-seen intersection problems are handled above.)
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
            mkIntersectionDom
                (IntMap.union (IntMap.fromList bindings) (idFree dom))
                (Set.insert (IntersectId i j) (idRecInt dom))

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

commonIntersectOpenEdgeCache ::
    MemoCache
        (IntersectionDom Symbol EqConstraints, Edge Symbol EqConstraints, Edge Symbol EqConstraints)
        (Edge Symbol EqConstraints)
commonIntersectOpenEdgeCache = unsafePerformIO newMemoCache
{-# NOINLINE commonIntersectOpenEdgeCache #-}

-- | Intersect two edges under the same recursive environment.
intersectOpenEdge ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (IntersectionDom symbol constraint, Edge symbol constraint, Edge symbol constraint) -> Edge symbol constraint
{-# INLINEABLE intersectOpenEdge #-}
intersectOpenEdge input =
    onCommon @symbol @constraint
        (memoWith commonIntersectOpenEdgeCache worker input)
        (memoTypeableWith @symbol @constraint genericIntersectOpenEdgeCache worker input)
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

-- | Recognize a term with an explicit pure constraint interpreter.
{-# INLINEABLE acceptsWith #-}
acceptsWith ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (constraint -> Tree.Tree symbol -> Bool) -> Node symbol constraint -> Tree.Tree symbol -> Bool
acceptsWith _ EmptyNode _ = False
acceptsWith acceptsConstraint (Node es) term = any (\edge -> edgeAcceptsWith acceptsConstraint edge term) es
acceptsWith acceptsConstraint node@(Mu _) term = acceptsWith acceptsConstraint (unfoldOuterRec node) term
acceptsWith _ _ _ = False

-- | Recognize one constructor and apply its constraint interpreter.
{-# INLINEABLE edgeAcceptsWith #-}
edgeAcceptsWith ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (constraint -> Tree.Tree symbol -> Bool) -> Edge symbol constraint -> Tree.Tree symbol -> Bool
edgeAcceptsWith acceptsConstraint edge term@(Tree.Node symbol children) =
    symbol == edgeSymbol edge
        && childrenRepresent (edgeChildren edge) children
        && acceptsConstraint (edgeConstraint edge) term
  where
    childrenRepresent [] [] = True
    childrenRepresent (node : nodes) (child : rest) = acceptsWith acceptsConstraint node child && childrenRepresent nodes rest
    childrenRepresent _ _ = False

-- | Tables for removal of redundant alternatives.
genericWithoutRedundantEdgesCache :: TypeableMemoCache
genericWithoutRedundantEdgesCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericWithoutRedundantEdgesCache #-}

{- | Remove alternatives implied by another alternative at each node.

Only a node without free recursive variables is changed, because the
comparison intersects alternatives. A recursive node compares the alternatives
of its unfolding, and keeps the alternatives of its body that remain. A node
that refers to an enclosing recursive node keeps all of its alternatives.
-}
{-# INLINEABLE withoutRedundantEdges #-}
withoutRedundantEdges ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) => Node symbol constraint -> Node symbol constraint
withoutRedundantEdges node = memoTypeableWith @symbol @constraint genericWithoutRedundantEdgesCache go node
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

-- | Iterate until stable with no iteration bound.
fixUnbounded :: (Eq a) => (a -> a) -> a -> a
fixUnbounded f x
    | x' == x = x
    | otherwise = fixUnbounded f x'
  where
    x' = f x

{- | Group values by a key.

Key equality defines each group. Different keys remain separate even when
their hashes are equal. Each group keeps its input order; the order of groups
is not specified.
-}
clusterByHash :: (Hashable k) => (a -> k) -> [a] -> [[a]]
clusterByHash key ls =
    map reverse $ HashMap.elems $ HashMap.fromListWith (++) [(key x, [x]) | x <- ls]

{- | Join two lists by equal keys and combine matching pairs.

As for 'clusterByHash', the table is keyed by the key itself, so the combining
function sees exactly the pairs whose keys are equal however the key hashes.
-}
hashJoin :: (Hashable k) => (a -> k) -> (a -> a -> b) -> [a] -> [a] -> [b]
hashJoin key j l1 l2 =
    [j x y | x <- l1, y <- HashMap.findWithDefault [] (key x) right]
  where
    right = HashMap.fromListWith (++) [(key x, [x]) | x <- l2]

-- Paths into graphs

instance (Hashable symbol, Typeable symbol, Constraint constraint) => Pathable (Node symbol constraint) (Node symbol constraint) where
    type Emptyable (Node symbol constraint) = Node symbol constraint

    getPath _ EmptyNode = EmptyNode
    getPath EmptyPath n = n
    getPath p n@(Mu _) = getPath p (unfoldOuterRec n)
    getPath (ConsPath p ps) (Node es) = union (mapMaybe (\e -> getPath ps <$> edgeChildren e !? p) es)
    getPath p _ = error $ "getPath: unexpected path " <> show p <> " for unresolved node"

    getAllAtPath _ EmptyNode = []
    getAllAtPath EmptyPath n = [n]
    getAllAtPath p n@(Mu _) = getAllAtPath p (unfoldOuterRec n)
    getAllAtPath (ConsPath p ps) (Node es) = concatMap (getAllAtPath ps) (mapMaybe (\e -> edgeChildren e !? p) es)
    getAllAtPath p _ = error $ "getAllAtPath: unexpected path " <> show p <> " for unresolved node"

    modifyAtPath f EmptyPath n = f n
    modifyAtPath _ _ EmptyNode = EmptyNode
    modifyAtPath f p n@(Mu _) = modifyAtPath f p (unfoldOuterRec n)
    modifyAtPath f (ConsPath p ps) (Node es) = Node (map goEdge es)
      where
        goEdge e = setChildren e (adjustAt p (modifyAtPath f ps) (edgeChildren e))
    modifyAtPath _ p _ = error $ "modifyAtPath: unexpected path " <> show p <> " for unresolved node"

instance (Hashable symbol, Typeable symbol, Constraint constraint) => Pathable [Node symbol constraint] (Node symbol constraint) where
    type Emptyable (Node symbol constraint) = Node symbol constraint

    getPath EmptyPath ns = union ns
    getPath (ConsPath p ps) ns = maybe EmptyNode (getPath ps) (ns !? p)

    getAllAtPath EmptyPath _ = []
    getAllAtPath (ConsPath p ps) ns = maybe [] (getAllAtPath ps) (ns !? p)

    modifyAtPath _ EmptyPath ns = ns
    modifyAtPath f (ConsPath p ps) ns = adjustAt p (modifyAtPath f ps) ns

{- | Paths to every reachable node that satisfies a predicate.

Linear in the number of paths and exponential in the size of the graph, so
use it on very small graphs only. A recursive node contributes no paths: the
search does not unfold recursion, so a match below a 'Mu' is not reported.
-}
pathsMatching :: (Node symbol constraint -> Bool) -> Node symbol constraint -> [Path]
pathsMatching _ EmptyNode = []
pathsMatching _ (InternedMu _) = []
pathsMatching f n@(InternedNode node) = concatMap pathsMatchingEdge (internedNodeEdges node) ++ [EmptyPath | f n]
  where
    pathsMatchingEdge e = concat $ zipWith (\i x -> map (ConsPath i) $ pathsMatching f x) [0 ..] (edgeChildren e)
pathsMatching _ (Rec _) = error "pathsMatching: unexpected Rec"

-- | Restrict a graph to the terms that contain the given path.
requirePath ::
    (Hashable symbol, Typeable symbol, Constraint constraint) => Path -> Node symbol constraint -> Node symbol constraint
requirePath EmptyPath n = n
requirePath _ EmptyNode = EmptyNode
requirePath p n@(Mu _) = requirePath p (unfoldOuterRec n)
requirePath (ConsPath p ps) (Node es) =
    Node
        [ setChildren e (requirePathList (ConsPath p ps) (edgeChildren e))
        | e <- es
        , compareLength (edgeChildren e) p == GT
        ]
requirePath _ (Rec _) = error "requirePath: unexpected Rec"

-- | Variant of 'requirePath' for a child list.
requirePathList ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Path -> [Node symbol constraint] -> [Node symbol constraint]
requirePathList EmptyPath ns = ns
requirePathList (ConsPath p ps) ns = adjustAt p (requirePath ps) ns
