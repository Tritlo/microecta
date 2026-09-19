{- | Shared interned tree automata.

The constraint parameter determines the transition theory. Use @()@ for an
ordinary automaton, 'EqConstraints' for path equalities, or a theory of your
own with a 'Constraint' instance. Nodes and edges retain canonical
identities. The engine is specialized for the interned 'Symbol' alphabet with
'EqConstraints'; every other alphabet and theory runs the same code
generically.
-}
module Data.CFTA.Interned (
    -- * Nodes and edges
    Node (EmptyNode, InternedNode, InternedMu, Rec, Node, Mu),
    Edge (InternedEdge, Edge),
    PlainNode,
    RecNodeId (..),
    UninternedEdge (..),
    UninternedNode (..),
    InternedNode (..),
    InternedMu (..),
    IntersectId,
    pattern IntersectId,
    mkNode,
    mkEdge,
    emptyEdge,
    setChildren,
    modifyNode,
    createMu,
    createMuDontCleanup,
    matchMu,
    substFree,
    edgeChildren,
    edgeConstraint,
    edgeSymbol,
    nodeIdentity,
    numNestedMu,
    freeVars,
    shape,
    module Data.CFTA.Constraint,

    -- * Operations
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
    intersect,
    intersectEdge,
    dropRedundantEdges,
    withoutRedundantEdges,
    dropEdgeConstraints,
    dropConstraints,
    nodeRepresentsWith,
    edgeRepresentsWith,
    getSubnodeById,
    fixUnbounded,
    pathsMatching,
    requirePath,
    requirePathList,

    -- * Views and conversion
    InternedState,
    FTAViewError (..),
    FTAImportError (..),
    toFTA,
    fromFTA,
    ViewPath,
    StateView (..),
    toTree,
    reachable,
) where

import Data.Bifunctor (first)
import Data.Hashable (Hashable)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Data.Type.Equality ((:~~:) (HRefl))
import Type.Reflection (Typeable, eqTypeRep, typeRep)

import Data.CFTA (StateView (..), ViewPath)
import qualified Data.CFTA as FTA
import Data.CFTA.Constraint
import Data.CFTA.Constraint.Equality (EqConstraints)
import Data.CFTA.Internal.Tree (toTreeBy)
import Data.CFTA.Interned.Operations hiding (
    dropConstraints,
    dropEdgeConstraints,
    dropRedundantEdges,
    intersect,
    nodeEdges,
    nodeMapChildren,
    refold,
    unfoldBounded,
    unfoldOuterRec,
    union,
    withoutRedundantEdges,
 )
import qualified Data.CFTA.Interned.Operations as Generic (
    dropConstraints,
    dropEdgeConstraints,
    dropRedundantEdges,
    intersect,
    nodeEdges,
    nodeMapChildren,
    refold,
    unfoldBounded,
    unfoldOuterRec,
    union,
    withoutRedundantEdges,
 )
import Data.CFTA.Interned.Type hiding (
    createMu,
    createMuDontCleanup,
    emptyEdge,
    matchMu,
    mkEdge,
    mkNode,
    modifyNode,
    setChildren,
    substFree,
    pattern Edge,
    pattern Mu,
    pattern Node,
 )
import qualified Data.CFTA.Interned.Type as Generic (
    createMu,
    createMuDontCleanup,
    emptyEdge,
    matchMu,
    mkEdge,
    mkNode,
    modifyNode,
    setChildren,
    substFree,
 )
import Data.CFTA.Symbol (Symbol)

{- | Run the engine at the interned 'Symbol' alphabet with 'EqConstraints'
when the types match, so GHC compiles a specialized copy for the common
case, and run it generically otherwise. Both branches compute the same value.
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

-- | Construct or inspect one unconstrained edge.
pattern Edge ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    symbol -> [Node symbol constraint] -> Edge symbol constraint
pattern Edge s ns <- InternedEdge _ (UninternedEdge s ns _)
  where
    Edge s ns = mkEdge s ns noConstraint

-- | Construct or inspect a set of alternatives.
pattern Node :: (Typeable symbol, Typeable constraint) => [Edge symbol constraint] -> Node symbol constraint
pattern Node es <- InternedNode (internedNodeEdges -> es)
  where
    Node = mkNode

-- | Construct or inspect a recursive binder.
pattern Mu ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (Node symbol constraint -> Node symbol constraint) -> Node symbol constraint
pattern Mu f <- (matchMu -> Just f)
  where
    Mu = createMu

{-# COMPLETE Node, EmptyNode, Mu, Rec #-}
{-# COMPLETE Edge #-}

-- | Build a canonical node from outgoing alternatives.
mkNode ::
    forall symbol constraint.
    (Typeable symbol, Typeable constraint) =>
    [Edge symbol constraint] -> Node symbol constraint
mkNode = onCommon @symbol @constraint (Generic.mkNode @Symbol @EqConstraints) Generic.mkNode

-- | Build an edge with a transition constraint.
mkEdge ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    symbol -> [Node symbol constraint] -> constraint -> Edge symbol constraint
mkEdge = onCommon @symbol @constraint (Generic.mkEdge @Symbol @EqConstraints) Generic.mkEdge

-- | Build an edge whose child language is empty.
emptyEdge ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    symbol -> Edge symbol constraint
emptyEdge = onCommon @symbol @constraint (Generic.emptyEdge @Symbol @EqConstraints) Generic.emptyEdge

-- | Replace children and retain the edge constraint.
setChildren ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Edge symbol constraint -> [Node symbol constraint] -> Edge symbol constraint
setChildren = onCommon @symbol @constraint (Generic.setChildren @Symbol @EqConstraints) Generic.setChildren

-- | Edit alternatives and retain an unchanged node.
modifyNode ::
    forall symbol constraint.
    (Typeable symbol, Typeable constraint) =>
    Node symbol constraint -> ([Edge symbol constraint] -> [Edge symbol constraint]) -> Node symbol constraint
modifyNode = onCommon @symbol @constraint (Generic.modifyNode @Symbol @EqConstraints) Generic.modifyNode

-- | Intern a recursive binder and remove a redundant binder.
createMu ::
    forall symbol constraint.
    (Typeable symbol, Typeable constraint) =>
    (Node symbol constraint -> Node symbol constraint) -> Node symbol constraint
createMu = onCommon @symbol @constraint (Generic.createMu @Symbol @EqConstraints) Generic.createMu

-- | Intern a recursive binder without removing it.
createMuDontCleanup ::
    forall symbol constraint.
    (Typeable symbol, Typeable constraint) =>
    (Node symbol constraint -> Node symbol constraint) -> Node symbol constraint
createMuDontCleanup = onCommon @symbol @constraint (Generic.createMuDontCleanup @Symbol @EqConstraints) Generic.createMuDontCleanup

-- | Inspect a recursive binder through its substitution function.
matchMu ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Node symbol constraint -> Maybe (Node symbol constraint -> Node symbol constraint)
matchMu = onCommon @symbol @constraint (Generic.matchMu @Symbol @EqConstraints) Generic.matchMu

-- | Substitute one free recursive variable.
substFree ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    RecNodeId -> Node symbol constraint -> Node symbol constraint -> Node symbol constraint
substFree = onCommon @symbol @constraint (Generic.substFree @Symbol @EqConstraints) Generic.substFree

-- | Change the immediate alternatives.
nodeMapChildren ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (Edge symbol constraint -> Edge symbol constraint) -> Node symbol constraint -> Node symbol constraint
nodeMapChildren = onCommon @symbol @constraint (Generic.nodeMapChildren @Symbol @EqConstraints) Generic.nodeMapChildren

-- | Unfold one outer recursive binder.
unfoldOuterRec ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Node symbol constraint -> Node symbol constraint
unfoldOuterRec = onCommon @symbol @constraint (Generic.unfoldOuterRec @Symbol @EqConstraints) Generic.unfoldOuterRec

-- | Recover recursive binders from repeated unfoldings.
refold ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Node symbol constraint -> Node symbol constraint
refold = onCommon @symbol @constraint (Generic.refold @Symbol @EqConstraints) Generic.refold

-- | Read alternatives, unfolding one recursive binder if needed.
nodeEdges ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Node symbol constraint -> [Edge symbol constraint]
nodeEdges = onCommon @symbol @constraint (Generic.nodeEdges @Symbol @EqConstraints) Generic.nodeEdges

-- | Unfold at most the specified number of rounds.
unfoldBounded ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Int -> Node symbol constraint -> Node symbol constraint
unfoldBounded = onCommon @symbol @constraint (Generic.unfoldBounded @Symbol @EqConstraints) Generic.unfoldBounded

-- | Forget the constraint on one edge.
dropEdgeConstraints ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Edge symbol constraint -> Edge symbol constraint
dropEdgeConstraints = onCommon @symbol @constraint (Generic.dropEdgeConstraints @Symbol @EqConstraints) Generic.dropEdgeConstraints

-- | Forget constraints throughout the graph.
dropConstraints ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Node symbol constraint -> Node symbol constraint
dropConstraints = onCommon @symbol @constraint (Generic.dropConstraints @Symbol @EqConstraints) Generic.dropConstraints

-- | Intersect structure and conjoin constraints.
intersect ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Node symbol constraint -> Node symbol constraint -> Node symbol constraint
intersect = onCommon @symbol @constraint (Generic.intersect @Symbol @EqConstraints) Generic.intersect

-- | Remove implied alternatives.
dropRedundantEdges ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    [Edge symbol constraint] -> [Edge symbol constraint]
dropRedundantEdges = onCommon @symbol @constraint (Generic.dropRedundantEdges @Symbol @EqConstraints) Generic.dropRedundantEdges

-- | Remove implied alternatives throughout the graph.
withoutRedundantEdges ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Node symbol constraint -> Node symbol constraint
withoutRedundantEdges = onCommon @symbol @constraint (Generic.withoutRedundantEdges @Symbol @EqConstraints) Generic.withoutRedundantEdges

-- | Combine alternatives from several nodes.
union ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    [Node symbol constraint] -> Node symbol constraint
union = onCommon @symbol @constraint (Generic.union @Symbol @EqConstraints) Generic.union

-- | An interned ordinary automaton.
type PlainNode symbol = Node symbol ()

-- | State identity in the explicit view of an interned automaton.
data InternedState = EmptyState | InternedState !Int
    deriving (Eq, Ord, Show)

-- | Failure while exposing an interned graph as an explicit-state automaton.
data FTAViewError symbol
    = -- | A recursive variable is free in the root node.
      OpenNode
    | -- | The graph does not have a consistently ranked alphabet.
      InvalidFTA !(FTA.FTAError InternedState symbol)
    deriving (Eq, Show)

{- | Expose the shared graph with its constraints unchanged.

Each interned node becomes one state. The operation does not enumerate terms
or interpret transition constraints. Use the explicit-state interface when
an operation must retain caller-supplied state names.
-}
toFTA ::
    (Hashable symbol, Ord symbol, Typeable symbol, Constraint constraint) =>
    Node symbol constraint ->
    Either (FTAViewError symbol) (FTA.FTA InternedState symbol constraint)
toFTA root
    | not (Set.null $ freeVars root) = Left OpenNode
    | otherwise = first InvalidFTA $ FTA.mkFTA (stateOf root) rows
  where
    rows = case root of
        EmptyNode -> [(EmptyState, [])]
        _ -> [(InternedState ident, map transition edges) | (ident, edges) <- IntMap.toList (reachable root)]

    transition edge =
        FTA.Transition
            (edgeSymbol edge)
            (map stateOf $ edgeChildren edge)
            (edgeConstraint edge)

{- | Expose typed state and transition labels for a closed interned grammar.

The view retains the original nodes, edges, and constraints. Recursive and
shared references use the same finite representation as 'FTA.toTree'. Open
roots return 'OpenNode'. The view does not require a ranked alphabet.
-}
toTree ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Node symbol constraint ->
    Either
        (FTAViewError symbol)
        (Tree.Tree (Either (StateView (Node symbol constraint)) (Edge symbol constraint)))
toTree root
    | not (Set.null $ freeVars root) = Left OpenNode
    | otherwise = Right $ toTreeBy nodeEdges edgeChildren root

-- | Outgoing alternatives of every node reachable from a non-empty root, by identity.
reachable ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Node symbol constraint -> IntMap [Edge symbol constraint]
reachable root = collect IntMap.empty [root]
  where
    collect seen [] = seen
    collect seen (node : pending)
        | IntMap.member ident seen = collect seen pending
        | otherwise = collect (IntMap.insert ident edges seen) (concatMap edgeChildren edges <> pending)
      where
        ident = nodeIdentity node
        edges = nodeEdges node

-- | Failure while importing a finite explicit-state graph.
newtype FTAImportError state = RecursiveFTAState state
    deriving (Eq, Show)

{- | Intern an acyclic explicit-state graph without interpreting constraints.

Each state is compiled once. Use 'FTA.boundDepth' before importing a recursive
graph. The graph is trimmed first, so only a reachable cycle is rejected. Constraint layers can annotate the source before this conversion.
-}
fromFTA ::
    (Ord state, Hashable symbol, Typeable symbol, Constraint constraint) =>
    FTA.FTA state symbol constraint -> Either (FTAImportError state) (Node symbol constraint)
fromFTA graph = case FTA.cycleState trimmed of
    Just state -> Left $ RecursiveFTAState state
    Nothing -> Right $ nodes Map.! FTA.initialState trimmed
  where
    trimmed = FTA.trim graph
    -- The map is lazy in its values, so each state is built once, on demand.
    nodes = fmap (mkNode . map edge) (FTA.transitionTable trimmed)
    edge transition =
        mkEdge
            (FTA.transitionSymbol transition)
            (map (nodes Map.!) (FTA.transitionChildren transition))
            (FTA.transitionConstraint transition)

-- | Name the empty state or read the shared canonical identity.
stateOf :: Node symbol constraint -> InternedState
stateOf EmptyNode = EmptyState
stateOf node = InternedState (nodeIdentity node)
