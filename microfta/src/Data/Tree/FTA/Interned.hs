{- | Shared interned tree automata.

The constraint parameter determines the transition theory. Use @()@ for an
ordinary automaton. Constraint layers supply their own 'Constraint' instance
and concrete-term interpreter. Nodes and edges retain canonical identities.
-}
module Data.Tree.FTA.Interned (
    PlainNode,
    PlainEdge,
    InternedState,
    FTAViewError (..),
    FTAImportError (..),
    toFTA,
    fromFTA,
    ViewPath,
    StateView (..),
    toTree,
    module Data.Tree.FTA.Constraint,
    module Data.Tree.FTA.Interned.Type,
    module Data.Tree.FTA.Interned.Operations,
) where

import qualified Control.Monad.State.Strict as State
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import Data.Tree.FTA (StateView (..), ViewPath)
import qualified Data.Tree.FTA as FTA
import Data.Tree.FTA.Constraint
import Data.Tree.FTA.Internal.Tree (toTreeBy)
import Data.Tree.FTA.Interned.Operations
import Data.Tree.FTA.Interned.Type

-- | An interned ordinary automaton.
type PlainNode symbol = Node symbol ()

-- | An interned ordinary transition.
type PlainEdge symbol = Edge symbol ()

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
    | otherwise =
        case FTA.mkFTA (stateOf root) (Map.toList $ collect Map.empty [root]) of
            Left err -> Left (InvalidFTA err)
            Right graph -> Right graph
  where
    collect seen [] = seen
    collect seen (node : pending)
        | Map.member state seen = collect seen pending
        | otherwise =
            collect
                (Map.insert state (map transition edges) seen)
                (concatMap edgeChildren edges <> pending)
      where
        state = stateOf node
        edges = nodeEdges node

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

-- | Failure while importing a finite explicit-state graph.
newtype FTAImportError state = RecursiveFTAState state
    deriving (Eq, Show)

{- | Intern an acyclic explicit-state graph without interpreting constraints.

Each state is compiled once. Use 'FTA.boundDepth' before importing a recursive
graph. Constraint layers can annotate the source before this conversion.
-}
fromFTA ::
    (Ord state, Hashable symbol, Typeable symbol, Constraint constraint) =>
    FTA.FTA state symbol constraint -> Either (FTAImportError state) (Node symbol constraint)
fromFTA graph = case FTA.cycleState graph of
    Just state -> Left $ RecursiveFTAState state
    Nothing -> Right $ State.evalState (buildState $ FTA.initialState graph) Map.empty
  where
    buildState state = do
        built <- State.get
        case Map.lookup state built of
            Just node -> pure node
            Nothing -> do
                edges <- traverse buildTransition $ FTA.transitionsFrom graph state
                let node = case edges of
                        [] -> EmptyNode
                        _ -> Node edges
                State.modify' $ Map.insert state node
                pure node
    buildTransition transition = do
        children <- traverse buildState $ FTA.transitionChildren transition
        pure $ mkEdge (FTA.transitionSymbol transition) children (FTA.transitionGuard transition)

-- | Name the empty state or read the shared canonical identity.
stateOf :: Node symbol constraint -> InternedState
stateOf EmptyNode = EmptyState
stateOf node = InternedState (nodeIdentity node)
