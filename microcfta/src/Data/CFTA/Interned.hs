{- | Shared interned tree automata.

Every edge carries a 'Constraint': none for an ordinary automaton, path
equalities for an equality automaton, and a guard for a liquid automaton.
Nodes and edges retain canonical identities. Every alphabet runs the same
code.
-}
module Data.CFTA.Interned (
    -- * Nodes and edges
    Node (EmptyNode, InternedNode, InternedMu, Rec, Node, Mu),
    Edge (InternedEdge, Edge),
    RecNodeId (..),
    UninternedEdge (..),
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
    unfoldOuterRec,
    refold,
    nodeEdges,
    unfoldBounded,
    boundDepth,
    nodeCount,
    edgeCount,
    union,
    intersect,
    intersectEdge,
    dropRedundantEdges,
    withoutRedundantEdges,
    dropEdgeConstraints,
    dropConstraints,
    acceptsWith,
    edgeAcceptsWith,
    fixUnbounded,
    pathsMatching,
    requirePath,

    -- * Views and conversion
    InternedState (..),
    FTAViewError (..),
    toFTA,
    fromFTA,
    ViewPath,
    ViewStep (..),
    StateView (..),
    toTree,
    reachable,
) where

import Data.Bifunctor (first)
import Data.Graph (SCC (CyclicSCC), flattenSCC, stronglyConnComp)
import Data.Hashable (Hashable)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Type.Reflection (Typeable)

import Data.CFTA (StateView (..), ViewPath, ViewStep (..))
import qualified Data.CFTA as FTA
import Data.CFTA.Constraint
import Data.CFTA.Internal.Tree (toTreeBy)
import Data.CFTA.Interned.Operations
import Data.CFTA.Interned.Type

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
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    Node symbol ->
    Either (FTAViewError symbol) (FTA.FTA InternedState symbol Constraint)
toFTA root
    | not (Set.null $ freeVars root) = Left OpenNode
    | otherwise = first InvalidFTA $ FTA.mkFTA (stateOf root) rows
  where
    rows = case root of
        EmptyNode -> [(EmptyState, [])]
        _ -> [(InternedState ident, map transition edges) | (ident, edges) <- IntMap.toList (reachable root)]
      where
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
    (Hashable symbol, Typeable symbol) =>
    Node symbol ->
    Either
        (FTAViewError symbol)
        (Tree.Tree (Either (StateView (Node symbol)) (Edge symbol)))
toTree root
    | not (Set.null $ freeVars root) = Left OpenNode
    | otherwise = Right $ toTreeBy nodeEdges edgeChildren root

-- | Outgoing alternatives of every node reachable from a root, by identity. An empty root reaches no node.
reachable ::
    (Hashable symbol, Typeable symbol) =>
    Node symbol -> IntMap [Edge symbol]
reachable root = collect IntMap.empty [root]
  where
    collect seen [] = seen
    collect seen (EmptyNode : pending) = collect seen pending
    collect seen (node : pending)
        | IntMap.member ident seen = collect seen pending
        | otherwise = collect (IntMap.insert ident edges seen) (concatMap edgeChildren edges <> pending)
      where
        ident = nodeIdentity node
        edges = nodeEdges node

{- | Intern an explicit-state graph without interpreting constraints.

The graph is trimmed first. Each reachable state becomes one node. A state on
a cycle becomes a 'Mu' whose body refers back to it through 'Rec', so a
recursive graph imports without a bound. Inside a 'Mu', a state that an
enclosing 'Mu' binds refers to that binder, and a state becomes a 'Mu' only
when a cycle through it avoids the bound states. Thus a path through the
result passes at most one binder for each state of a strongly connected
component. Each node is built once for each set of enclosing binders. When
each of the k states of a component refers to all k states, the result can
have about e * (k - 1)! binders. Constraint layers can annotate the source
before this conversion.
-}
fromFTA ::
    forall state symbol.
    (Ord state, Hashable symbol, Typeable symbol) =>
    FTA.FTA state symbol Constraint -> Node symbol
fromFTA graph = shared Map.! FTA.initialState trimmed
  where
    trimmed = FTA.trim graph
    successors state = concatMap FTA.transitionChildren (FTA.transitionsFrom trimmed state)
    components = map flattenSCC (stronglyConnComp [(state, state, successors state) | state <- FTA.states trimmed])
    component = Map.fromList [(state, index) | (index, states) <- zip [0 :: Int ..] components, state <- states]
    -- The states of the component of each state.
    members = Map.fromList [(state, set) | states <- components, let set = Set.fromList states, state <- states]

    -- The given states that are on a cycle through the given states only.
    cycles states =
        Set.fromList $
            concat
                [ scc
                | CyclicSCC scc <- stronglyConnComp [(state, state, successors state) | state <- Set.toList states]
                ]

    -- The node of each state outside every binder. The lazy map builds each
    -- node once, when a parent or the root first needs it.
    shared = LazyMap.fromSet (build (cycles (Map.keysSet component)) Map.empty shared) (Map.keysSet component)

    -- Build the node of a state in one binder context. The context has the
    -- states of a component that are on a cycle that avoids the bound states,
    -- the bound states with the placeholders of their binders, and a lazy map
    -- with the node of each state of the component in the context. Thus each
    -- node is built once in each context, not once for each occurrence. A
    -- bound state is its placeholder. A state on a cycle that avoids the bound
    -- states gets a binder and starts a new context. Another state gets no
    -- binder: the binder would not occur in the body, and 'createMu' would
    -- remove it after it evaluated the body two or three times.
    build :: Set.Set state -> Map.Map state (Node symbol) -> Map.Map state (Node symbol) -> state -> Node symbol
    build free binders nodes state
        | Just self <- Map.lookup state binders = self
        | Set.member state free =
            let free' = cycles (Set.delete state (Set.difference (members Map.! state) (Map.keysSet binders)))
             in createMu $ \self ->
                    let binders' = Map.insert state self binders
                        nodes' = LazyMap.fromSet (build free' binders' nodes') (members Map.! state)
                     in body nodes' state
        | otherwise = body nodes state

    -- A child in another component cannot reach a bound state, so it is the
    -- shared node of that child.
    body nodes state = mkNode (map edge (FTA.transitionsFrom trimmed state))
      where
        edge transition =
            mkEdge
                (FTA.transitionSymbol transition)
                (map child (FTA.transitionChildren transition))
                (FTA.transitionConstraint transition)
        child next
            | component Map.! next == component Map.! state = nodes Map.! next
            | otherwise = shared Map.! next

-- | Name the empty state or read the shared canonical identity.
stateOf :: Node symbol -> InternedState
stateOf EmptyNode = EmptyState
stateOf node = InternedState (nodeIdentity node)
