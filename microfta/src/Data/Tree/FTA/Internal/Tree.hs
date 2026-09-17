{-# LANGUAGE DeriveFunctor #-}

-- | Shared finite tree views of graph nodes and their outgoing alternatives.
module Data.Tree.FTA.Internal.Tree (ViewPath, StateView (..), toTreeBy, termsBy) where

import Control.Monad (zipWithM)
import qualified Control.Monad.State.Strict as State
import qualified Data.Map.Strict as Map
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

{- | Every accepted term of a graph given as rows, ordered by depth.

A leaf has depth zero. All terms of one depth are listed before deeper
terms, so every term of a cyclic graph appears after finitely many others.
The list ends once no row has a term of the current depth, so an acyclic
graph gives a finite list. Rows must be closed: every child key has a row.
-}
termsBy :: (Ord key) => [(key, [(symbol, [key])])] -> key -> [Tree symbol]
termsBy rows root = concat [exactly depth root | depth <- takeWhile populated [0 ..]]
  where
    -- Terms of each depth for each row. Each level is computed once.
    levels = Map.fromList [(key, map (level outgoing) [0 ..]) | (key, outgoing) <- rows]
    level outgoing depth =
        [Node symbol children | (symbol, childKeys) <- outgoing, children <- deepest (depth - 1) childKeys]
    populated depth = not (all (null . (!! depth)) (Map.elems levels))
    exactly depth key = levels Map.! key !! depth
    atMost depth key = concat (take (depth + 1) (levels Map.! key))

    -- Child lists whose deepest child has exactly the given depth. The first
    -- child at that depth is fixed, so no list is produced twice.
    deepest depth []
        | depth < 0 = [[]]
        | otherwise = []
    deepest depth (key : keys)
        | depth < 0 = []
        | otherwise =
            [child : rest | child <- exactly depth key, rest <- traverse (atMost depth) keys]
                ++ [child : rest | child <- atMost (depth - 1) key, rest <- deepest depth keys]
