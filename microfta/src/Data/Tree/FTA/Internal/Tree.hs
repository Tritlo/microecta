{-# LANGUAGE DeriveFunctor #-}

-- | Shared finite tree views of graph nodes and their outgoing alternatives.
module Data.Tree.FTA.Internal.Tree (ViewPath, StateView (..), toTreeBy) where

import Control.Monad (zipWithM)
import qualified Control.Monad.State.Strict as State
import qualified Data.Set as Set
import Data.Tree (Tree (Node))

{- | A root-relative location in a tree view.

Each step selects a zero-based transition alternative and then a zero-based
child of that transition. The root has path @[]@. This location belongs to one
view; it is not a persistent node identity or a child-only constraint path.
-}
type ViewPath = [(Int, Int)]

-- | A node definition or reference with its location in the tree view.
data StateView node
    = -- | The node is expanded here, with its outgoing alternatives as children.
      Expanded
        { viewPath :: ViewPath
        -- ^ Location of this occurrence, including recursive and shared references.
        , viewNode :: node
        -- ^ Original node. References retain the same identity as its definition.
        }
    | -- | The node is already on the current path.
      Recursive {viewPath :: ViewPath, viewNode :: node}
    | -- | The node was expanded on an earlier path.
      Shared {viewPath :: ViewPath, viewNode :: node}
    deriving (Eq, Ord, Show, Functor)

-- | Expand each reachable node once and retain the original node and edge labels.
toTreeBy ::
    (Ord node) =>
    (node -> [edge]) ->
    (edge -> [node]) ->
    node ->
    Tree (Either (StateView node) edge)
toTreeBy outgoing children root = State.evalState (visit Set.empty [] root) Set.empty
  where
    visit ancestors reversedPath node
        | Set.member node ancestors = pure $ Node (Left $ Recursive (reverse reversedPath) node) []
        | otherwise = do
            seen <- State.get
            if Set.member node seen
                then pure $ Node (Left $ Shared (reverse reversedPath) node) []
                else do
                    State.modify' (Set.insert node)
                    alternatives <- zipWithM (transition (Set.insert node ancestors) reversedPath) [0 ..] $ outgoing node
                    pure $ Node (Left $ Expanded (reverse reversedPath) node) alternatives

    transition ancestors reversedPath alternative edge =
        Node (Right edge)
            <$> zipWithM
                (\child -> visit ancestors ((alternative, child) : reversedPath))
                [0 ..]
                (children edge)
