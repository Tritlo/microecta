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
Rows that accept nothing, or that the root cannot reach, are removed first;
the list then ends once no remaining row has a term of the current depth, so
an acyclic graph gives a finite list. Every child key must have a row.
-}
termsBy :: (Ord key) => [(key, [(symbol, [key])])] -> key -> [Tree symbol]
termsBy rows root
    | Map.member root table = concatMap (Map.! root) $ takeWhile (not . all null) $ map exactly levels
    | otherwise = []
  where
    table = Map.restrictKeys (Map.fromList liveRows) (reachable Set.empty [root])
    liveRows =
        [ (key, [alternative | alternative@(_, childKeys) <- outgoing, all (`Set.member` live) childKeys])
        | (key, outgoing) <- rows
        , Set.member key live
        ]

    -- Keys with at least one term: the least fixed point of "some alternative
    -- has only live children".
    live = grow Set.empty
    grow known
        | Set.size more == Set.size known = known
        | otherwise = grow more
      where
        more = Set.fromList [key | (key, outgoing) <- rows, any (all (`Set.member` known) . snd) outgoing]

    reachable seen [] = seen
    reachable seen (key : pending)
        | Set.member key seen = reachable seen pending
        | otherwise = reachable (Set.insert key seen) (concatMap snd (Map.findWithDefault [] key liveTable) <> pending)
    liveTable = Map.fromList liveRows

    -- Each level holds, for every row, the terms of exactly its depth, of at
    -- most its depth, and of at most the depth before it.
    levels = iterate next (leaves, leaves, fmap (const []) table)
    exactly (terms, _, _) = terms
    leaves = fmap (\outgoing -> [Node symbol [] | (symbol, []) <- outgoing]) table
    next (current, atMost, shallower) = (deeper, Map.unionWith (++) deeper atMost, atMost)
      where
        deeper =
            fmap
                (\outgoing -> [Node symbol children | (symbol, childKeys@(_ : _)) <- outgoing, children <- deepest childKeys])
                table
        -- Child lists whose deepest child has exactly the current depth. The
        -- first child at that depth is fixed, so no list is produced twice.
        deepest [] = []
        deepest (key : keys) =
            [child : rest | child <- current Map.! key, rest <- traverse (atMost Map.!) keys]
                <> [child : rest | rest <- deepest keys, child <- shallower Map.! key]
