{-# LANGUAGE DeriveFunctor #-}

-- | Shared finite tree views of graph nodes and their outgoing alternatives.
module Data.Tree.FTA.Internal.Tree (StateView (..), toTreeBy) where

import qualified Control.Monad.State.Strict as State
import qualified Data.Set as Set
import Data.Tree (Tree (Node))

-- | A node definition or reference in an automaton's tree view.
data StateView node
    = -- | The node is expanded here, with its outgoing alternatives as children.
      Expanded node
    | -- | The node is already on the current path.
      Recursive node
    | -- | The node was expanded on an earlier path.
      Shared node
    deriving (Eq, Ord, Read, Show, Functor)

-- | Expand each reachable node once and retain the original node and edge labels.
toTreeBy ::
    (Ord node) =>
    (node -> [edge]) ->
    (edge -> [node]) ->
    node ->
    Tree (Either (StateView node) edge)
toTreeBy outgoing children root = State.evalState (visit Set.empty root) Set.empty
  where
    visit ancestors node
        | Set.member node ancestors = pure $ Node (Left $ Recursive node) []
        | otherwise = do
            seen <- State.get
            if Set.member node seen
                then pure $ Node (Left $ Shared node) []
                else do
                    State.modify' (Set.insert node)
                    alternatives <- traverse (transition $ Set.insert node ancestors) $ outgoing node
                    pure $ Node (Left $ Expanded node) alternatives

    transition ancestors edge = Node (Right edge) <$> traverse (visit ancestors) (children edge)
