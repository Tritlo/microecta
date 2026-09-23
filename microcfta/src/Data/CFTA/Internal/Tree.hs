{-# LANGUAGE DeriveFunctor #-}

-- | Shared finite tree views of graph nodes and their outgoing alternatives.
module Data.CFTA.Internal.Tree (
    adjustAt,
    ViewPath,
    StateView (..),
    toTreeBy,
    trimRows,
    termsBy,
    termLevelsBy,
    termsUpToBy,
    allM,
    anyM,
) where

import Control.Monad (filterM, zipWithM)
import qualified Control.Monad.State.Strict as State
import Data.Containers.ListUtils (nubOrd)
import Data.Map.Strict (Map)
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

{- | Keep the rows the root reaches through alternatives whose children all
accept a term.

A key accepts a term when some alternative has only accepting children; this
is the least fixed point over the rows. Alternatives with a removed child are
removed. The root is absent from the result when it accepts nothing.
-}
trimRows :: (Ord key) => (alternative -> [key]) -> [(key, [alternative])] -> key -> Map key [alternative]
trimRows childrenOf rows root = Map.restrictKeys liveTable (reachable Set.empty [root])
  where
    live = grow Set.empty
    grow known
        | Set.size more == Set.size known = known
        | otherwise = grow more
      where
        more = Set.fromList [key | (key, outgoing) <- rows, any (all (`Set.member` known) . childrenOf) outgoing]
    liveTable =
        Map.fromList
            [ (key, [alternative | alternative <- outgoing, all (`Set.member` live) (childrenOf alternative)])
            | (key, outgoing) <- rows
            , Set.member key live
            ]
    reachable seen [] = seen
    reachable seen (key : pending)
        | Set.member key seen = reachable seen pending
        | otherwise = reachable (Set.insert key seen) (concatMap childrenOf (Map.findWithDefault [] key liveTable) <> pending)

{- | Every accepted term of a graph given as rows, ordered by depth.

A leaf has depth zero. All terms of one depth are listed before deeper
terms, so every term of a cyclic graph appears after finitely many others.
The rows are trimmed first with 'trimRows'; the list then ends once no
remaining row has a term of the current depth, so an acyclic graph gives a
finite list. Each key lists a term once per depth: rows whose alternatives
all carry distinct symbols cannot repeat a term, and the others are
deduplicated per level. Every child key must have a row.
-}
termsBy :: (Ord key, Ord symbol) => [(key, [(symbol, [key])])] -> key -> [Tree symbol]
termsBy rows root = concat $ termLevelsBy rows root

{- | The terms of 'termsBy' grouped by depth: the terms of depth zero first,
then the terms of depth one, and so on. The list of levels is lazy, so a
prefix of it bounds the depth without building the deeper terms.
-}
termLevelsBy :: (Ord key, Ord symbol) => [(key, [(symbol, [key])])] -> key -> [[Tree symbol]]
termLevelsBy rows root
    | Map.member root table = map (Map.! root) $ takeWhile (not . all null) $ map exactly levels
    | otherwise = []
  where
    table = trimRows snd rows root
    dedup = dedupUnless (all (distinctSymbols . map fst) table)

    -- Each level holds, for every row, the terms of exactly its depth, of at
    -- most its depth, and of at most the depth before it.
    levels = iterate next (leaves, leaves, fmap (const []) table)
    exactly (terms, _, _) = terms
    leaves = fmap (\outgoing -> dedup [Node symbol [] | (symbol, []) <- outgoing]) table
    next (current, atMost, shallower) = (deeper, Map.unionWith (++) deeper atMost, atMost)
      where
        deeper =
            fmap
                (\outgoing -> dedup [Node symbol children | (symbol, childKeys@(_ : _)) <- outgoing, children <- deepest childKeys])
                table
        -- Child lists whose deepest child has exactly the current depth. The
        -- first child at that depth is fixed, so no list is produced twice.
        deepest [] = []
        deepest (key : keys) =
            [child : rest | child <- current Map.! key, rest <- traverse (atMost Map.!) keys]
                <> [child : rest | rest <- deepest keys, child <- shallower Map.! key]

{- | The terms of depth at most the bound that a check accepts, from rows.

Terms are built level by level, as in 'termsBy'. The check sees each
candidate once, with the key and alternative that built it, and a rejected
candidate is never a child. Each key lists a term once per depth, as in
'termsBy'.
-}
termsUpToBy ::
    (Monad m, Ord key, Ord symbol) =>
    (alternative -> symbol) ->
    (alternative -> [key]) ->
    (key -> alternative -> Tree symbol -> m Bool) ->
    [(key, [alternative])] ->
    Int ->
    key ->
    m [Tree symbol]
termsUpToBy symbolOf childrenOf accept rows bound root
    | bound < 0 || Map.notMember root table = pure []
    | otherwise = do
        leaves <- level (\keys -> [[] | null keys])
        collect 1 (leaves, leaves, fmap (const []) table) [leaves Map.! root]
  where
    table = trimRows childrenOf rows root
    dedup = dedupUnless (all (distinctSymbols . map symbolOf) table)

    level combos = Map.traverseWithKey (\key outgoing -> dedup . concat <$> traverse (candidates key) outgoing) table
      where
        candidates key alternative =
            filterM (accept key alternative) [Node (symbolOf alternative) children | children <- combos (childrenOf alternative)]

    collect depth (current, atMost, shallower) collected
        | depth > bound || all null current = pure (concat (reverse collected))
        | otherwise = do
            deeper <- level (\keys -> if null keys then [] else deepest keys)
            collect (depth + 1) (deeper, Map.unionWith (++) deeper atMost, atMost) (deeper Map.! root : collected)
      where
        deepest [] = []
        deepest (key : keys) =
            [child : rest | child <- current Map.! key, rest <- traverse (atMost Map.!) keys]
                <> [child : rest | rest <- deepest keys, child <- shallower Map.! key]

{- | Whether alternatives carry pairwise distinct symbols. Then no two of
them build the same term, so a level built from deduplicated levels has no
duplicates.
-}
distinctSymbols :: (Ord symbol) => [symbol] -> Bool
distinctSymbols symbols = length (nubOrd symbols) == length symbols

{- | Deduplicate a level unless it cannot contain duplicates.

A set beats hashing here by a factor of four to six: comparing two different
terms stops at the first differing node, while a hash visits every node, and
hashing one small term with the standard instances costs microseconds. The
order within a level is not specified.
-}
dedupUnless :: (Ord a) => Bool -> [a] -> [a]
dedupUnless unambiguous
    | unambiguous = id
    | otherwise = Set.toList . Set.fromList

-- | Apply a function to the element at an index, if it exists.
adjustAt :: Int -> (a -> a) -> [a] -> [a]
adjustAt i f xs
    | i < 0 = xs
    | otherwise = case splitAt i xs of
        (prefix, x : suffix) -> prefix ++ f x : suffix
        _ -> xs

-- | Whether every action succeeds, stopping at the first failure.
allM :: (Monad m) => [m Bool] -> m Bool
allM [] = pure True
allM (action : actions) = action >>= \ok -> if ok then allM actions else pure False

-- | Whether some action succeeds, stopping at the first success.
anyM :: (Monad m) => [m Bool] -> m Bool
anyM [] = pure False
anyM (action : actions) = action >>= \ok -> if ok then pure True else anyM actions
