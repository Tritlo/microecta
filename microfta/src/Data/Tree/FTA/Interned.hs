{- | Shared interned tree automata.

The constraint parameter determines the transition theory. Use @()@ for an
ordinary automaton. Constraint layers supply their own 'Constraint' instance
and concrete-term interpreter. Nodes and edges retain canonical identities.
-}
module Data.Tree.FTA.Interned (
    PlainNode,
    InternedState,
    FTAViewError (..),
    FTAImportError (..),
    toFTA,
    fromFTA,
    ViewPath,
    StateView (..),
    toTree,
    terms,
    module Data.Tree.FTA.Constraint,
    module Data.Tree.FTA.Interned.Type,
    module Data.Tree.FTA.Interned.Operations,
) where

import Data.Bifunctor (first)
import Data.Hashable (Hashable)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import Data.Tree.FTA (StateView (..), ViewPath)
import qualified Data.Tree.FTA as FTA
import Data.Tree.FTA.Constraint
import Data.Tree.FTA.Internal.Tree (termsBy, toTreeBy)
import Data.Tree.FTA.Interned.Operations
import Data.Tree.FTA.Interned.Type

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

{- | Every term of the underlying ordinary graph of a closed root, ordered by depth.

See 'FTA.terms': each term appears once, constraints are not interpreted,
and a recursive graph gives an infinite list.
-}
terms ::
    (Hashable symbol, Ord symbol, Typeable symbol, Constraint constraint) => Node symbol constraint -> [Tree.Tree symbol]
terms EmptyNode = []
terms root =
    termsBy
        [ (ident, [(edgeSymbol edge, map nodeIdentity (edgeChildren edge)) | edge <- edges])
        | (ident, edges) <- IntMap.toList (reachable root)
        ]
        (nodeIdentity root)

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
            (FTA.transitionGuard transition)

-- | Name the empty state or read the shared canonical identity.
stateOf :: Node symbol constraint -> InternedState
stateOf EmptyNode = EmptyState
stateOf node = InternedState (nodeIdentity node)
