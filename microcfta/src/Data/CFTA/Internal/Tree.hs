{-# LANGUAGE DeriveFunctor #-}

-- | Shared finite tree views of graph nodes and their outgoing transitions.
module Data.CFTA.Internal.Tree (
    adjustAt,
    ViewStep (..),
    ViewPath,
    StateView (..),
    toTreeBy,
    trimRows,
    termsBy,
    termLevelsBy,
    termsUpToBy,
    acceptsBy,
    andM,
    orM,
) where

import Control.Monad (filterM, zipWithM)
import qualified Control.Monad.State.Strict as State
import Control.Monad.Trans.Class (lift)
import Data.Containers.ListUtils (nubOrd)
import Data.Foldable (toList)
import qualified Data.Graph as Graph
import qualified Data.HashSet as HashSet
import Data.Hashable (Hashable)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Sequence
import qualified Data.Set as Set
import Data.Tree (Tree (Node))

import Data.CFTA.Index (ChildIndex (..), Depth (..), TransitionIndex (..))

{- | A root-relative location in a tree view.

Each step selects a transition and then a child of that transition. The root
has path @[]@. This location belongs to one view; it is not a persistent node
identity or a child-only constraint path.
-}
type ViewPath = [ViewStep]

-- | One step of a 'ViewPath': a transition of a node, then a child of that transition.
data ViewStep = ViewStep
    { stepTransition :: !TransitionIndex
    , stepChild :: !ChildIndex
    }
    deriving (Eq, Ord, Show)

-- | A node definition or reference with its location in the tree view.
data StateView node
    = -- | The node is expanded here, with its outgoing transitions as children.
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
toTreeBy outgoing children root = State.evalState (visit Set.empty Empty root) Set.empty
  where
    visit ancestors path node
        | Set.member node ancestors = pure $ Node (Left $ Recursive (toList path) node) []
        | otherwise = do
            seen <- State.get
            if Set.member node seen
                then pure $ Node (Left $ Shared (toList path) node) []
                else do
                    State.modify' (Set.insert node)
                    transitions <- zipWithM (transition (Set.insert node ancestors) path) [0 ..] $ outgoing node
                    pure $ Node (Left $ Expanded (toList path) node) transitions

    transition ancestors path index edge =
        Node (Right edge)
            <$> zipWithM
                (\child -> visit ancestors (path :|> ViewStep index child))
                [0 ..]
                (children edge)

{- | Keep the rows the root reaches through alternatives whose children all
accept a term.

A key accepts a term when some alternative has only accepting children; this
is the least fixed point over the rows. Alternatives with a removed child are
removed. The root is absent from the result when it accepts nothing.
-}
trimRows :: (Ord key) => (alternative -> [key]) -> [(key, [alternative])] -> key -> Map key [alternative]
trimRows childrenOf rows root = Map.restrictKeys liveTable reached
  where
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
      where
        live = grow Set.empty
    (graph, nodeOf, vertexOf) =
        Graph.graphFromEdges [((), key, concatMap childrenOf alternatives) | (key, alternatives) <- Map.toList liveTable]
    reached =
        Set.fromList
            [key | start <- toList (vertexOf root), vertex <- Graph.reachable graph start, let ((), key, _) = nodeOf vertex]

{- | Every accepted term of a graph given as rows, ordered by depth.

A leaf has depth zero. All terms of one depth are listed before deeper
terms, so every term of a cyclic graph appears after finitely many others.
The rows are trimmed first with 'trimRows'; the list then ends once no
remaining row has a term of the current depth, so an acyclic graph gives a
finite list. Each key lists a term once per depth: rows whose alternatives
all carry distinct symbols cannot repeat a term, and the others are
deduplicated per level. A child key without a row accepts nothing, so
'trimRows' removes the alternatives that use it.
-}
termsBy :: (Ord key, Ord symbol, Hashable symbol) => [(key, [(symbol, [key])])] -> key -> [Tree symbol]
termsBy rows root = concat $ termLevelsBy rows root

{- | The terms of 'termsBy' grouped by depth: the terms of depth zero first,
then the terms of depth one, and so on. The list of levels is lazy, so a
prefix of it bounds the depth without building the deeper terms.
-}
termLevelsBy :: (Ord key, Ord symbol, Hashable symbol) => [(key, [(symbol, [key])])] -> key -> [[Tree symbol]]
termLevelsBy rows root
    | Map.member root table = map (Map.! root) $ takeWhile (not . all null) $ map exactly levels
    | otherwise = []
  where
    table = trimRows snd rows root
    dedup = dedupUnless (all (distinctSymbols . map fst) table)

    -- Each level holds, for every row, the terms of exactly its depth, of at
    -- most its depth, and of at most the depth before it.
    levels = iterate next (leaves, leaves, fmap (const []) table)
      where
        leaves = fmap (\outgoing -> dedup [Node symbol [] | (symbol, []) <- outgoing]) table
    exactly (terms, _, _) = terms
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
    (Monad m, Ord key, Ord symbol, Hashable symbol) =>
    (alternative -> symbol) ->
    (alternative -> [key]) ->
    (key -> alternative -> Tree symbol -> m Bool) ->
    [(key, [alternative])] ->
    Depth ->
    key ->
    m [Tree symbol]
termsUpToBy symbolOf childrenOf accept rows bound root
    | bound < 0 || Map.notMember root table = pure []
    | otherwise = do
        leaves <- level (\keys -> [[] | null keys])
        collect 1 (leaves, leaves, fmap (const []) table) (Sequence.singleton $ leaves Map.! root)
  where
    table = trimRows childrenOf rows root
    dedup = dedupUnless (all (distinctSymbols . map symbolOf) table)

    level combos = Map.traverseWithKey (\key outgoing -> dedup . concat <$> traverse (candidates key) outgoing) table
      where
        candidates key alternative =
            filterM (accept key alternative) [Node (symbolOf alternative) children | children <- combos (childrenOf alternative)]

    collect depth (current, atMost, shallower) collected
        | depth > bound || all null current = pure (concat collected)
        | otherwise = do
            deeper <- level (\keys -> if null keys then [] else deepest keys)
            collect (depth + 1) (deeper, Map.unionWith (++) deeper atMost, atMost) (collected :|> deeper Map.! root)
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

With an optimized @hashable@, a hash set does this in less than half the
time of an ordered set: on the four ambiguous cells of @enumeration-speed@,
the hash set takes 35% to 39% of the time of the ordered set. An ordered set
compares each new term with about log n terms of the level, and terms of one
level often share long prefixes. A hash set visits each term once to hash it
and compares terms only when the hashes match. An unoptimized @hashable@ makes
the hash set slower than the ordered set: on the same cells, it takes 2.7 to 4.9
times the time of the ordered set. The order within a level is not specified.
-}
dedupUnless :: (Hashable a) => Bool -> [a] -> [a]
dedupUnless unambiguous
    | unambiguous = id
    | otherwise = HashSet.toList . HashSet.fromList

-- | Apply a function to the child at an index, if it exists.
adjustAt :: ChildIndex -> (a -> a) -> [a] -> [a]
adjustAt (ChildIndex i) f xs
    | i < 0 = xs
    | otherwise = case splitAt i xs of
        (prefix, x : suffix) -> prefix ++ f x : suffix
        _ -> xs

-- | Whether every action succeeds, stopping at the first failure.
andM :: (Monad m) => [m Bool] -> m Bool
andM [] = pure True
andM (action : actions) = action >>= \ok -> if ok then andM actions else pure False

-- | Whether some action succeeds, stopping at the first success.
orM :: (Monad m) => [m Bool] -> m Bool
orM [] = pure False
orM (action : actions) = action >>= \ok -> if ok then pure True else orM actions

{- | Decide whether a key accepts a term, from the outgoing alternatives of each key.

An alternative matches a subterm when its symbol and its number of children
are those of the root of the subterm. The matching alternatives of a key are
tried in order, and the search stops at the first one that accepts. The
children of an alternative are tried from left to right. The check runs only
when all of them accept. This is the order of the direct recursion.

The direct recursion decides a subterm again for each alternative above it
that fails, so its time can be exponential in the depth of the term. This
search keeps a table below each subterm that two or more alternatives match.
In the table, each key at each position of the term is decided once, and a
later visit uses that result and runs no check. Above such a subterm, each
subterm has one visit, and the search keeps no table. Thus each check runs at
most once for each key, alternative, and position, in the order in which the
direct recursion first runs it.
-}
{-# INLINEABLE acceptsBy #-}
acceptsBy ::
    (Monad m, Ord key, Eq symbol) =>
    (key -> [alternative]) ->
    (alternative -> symbol) ->
    (alternative -> [key]) ->
    (key -> alternative -> Tree symbol -> m Bool) ->
    key ->
    Tree symbol ->
    m Bool
acceptsBy outgoing symbolOf childrenOf check = unshared
  where
    matches (Node symbol children) alternative =
        symbolOf alternative == symbol && length (childrenOf alternative) == length children

    -- The alternatives of a row from the first one that matches a subterm.
    fromMatch _ [] = []
    fromMatch term alternatives@(alternative : rest)
        | matches term alternative = alternatives
        | otherwise = fromMatch term rest

    -- No other visit reaches this subterm, so its result needs no table.
    unshared key term@(Node _ children) = case fromMatch term (outgoing key) of
        [] -> pure False
        alternative : rest -> case fromMatch term rest of
            [] ->
                childrenAccept (childrenOf alternative) children >>= \accepted ->
                    if accepted then check key alternative term else pure False
            _ -> State.evalStateT (shared key (positioned term)) Map.empty
    childrenAccept (key : keys) (child : rest) =
        unshared key child >>= \accepted -> if accepted then childrenAccept keys rest else pure False
    childrenAccept _ _ = pure True

    -- This subterm is at or below a subterm that two or more alternatives
    -- match. The table holds the result of each position and key.
    shared key (Node (_, term) children) =
        orM
            [ andM (zipWith visit (childrenOf alternative) children) >>= \accepted ->
                if accepted then lift (check key alternative term) else pure False
            | alternative <- outgoing key
            , matches term alternative
            ]
    visit key node@(Node (position, _) _) = do
        known <- State.gets (Map.lookup (position, key))
        case known of
            Just accepted -> pure accepted
            Nothing -> do
                accepted <- shared key node
                State.modify' (Map.insert (position, key) accepted)
                pure accepted

    -- Each subterm with its position in preorder.
    positioned whole = State.evalState (number whole) (0 :: Int)
      where
        number term@(Node _ children) = do
            position <- State.get
            State.modify' (+ 1)
            Node (position, term) <$> traverse number children
