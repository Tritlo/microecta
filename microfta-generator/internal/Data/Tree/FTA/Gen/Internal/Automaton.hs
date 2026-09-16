{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}

-- | Shared size indexing for ordinary, possibly recursive automata.
module Data.Tree.FTA.Gen.Internal.Automaton (
    automatonIndex,
    tableIndex,
    minimumSizes,
    countRuns,
    ambiguousState,
    foldAt,
) where

import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set

import qualified Data.Tree.FTA as FTA
import Data.Tree.Gen.Internal.Size (
    SizeIndex,
    choiceIndex,
    constantIndex,
    mapIndex,
    productIndex,
    withMinimumMemberSize,
 )
import Data.Tree.Term (Term, pattern Term)

{- | Count accepting runs by their number of tree nodes.

Ranks are size-major. Ambiguous automata can assign several ranks to one term.
Each state shares one index, including recursive references to that index.

This module belongs to the @internal@ sublibrary. It is an integration
interface for the constrained generator packages, and its exports are not
covered by the PVP contract of the main library.
-}
automatonIndex :: (Ord state) => FTA.PlainFTA state symbol -> SizeIndex (Term symbol)
automatonIndex automaton = tableIndex (FTA.initialState automaton) (FTA.transitionTable automaton)

{- | Index ordinary transition rows supplied by a graph adapter.

Missing rows accept nothing. Constraint layers must validate their annotations
before supplying ordinary rows. This worker does not interpret constraints.
-}
tableIndex ::
    (Ord state) => state -> Map.Map state [FTA.Transition state symbol ()] -> SizeIndex (Term symbol)
tableIndex initial rows = indexOf initial
  where
    minima = minimumSizes rows
    table = LazyMap.mapWithKey stateIndex rows
    stateIndex state transitions =
        withMinimumMemberSize
            (Map.lookup state minima)
            (choiceIndex $ map transitionIndex transitions)
    indexOf state
        | Map.member state minima = Map.findWithDefault emptyIndex state table
        | otherwise = emptyIndex
    emptyIndex = choiceIndex []
    transitionIndex transition =
        mapIndex ($ []) $
            foldl'
                consumeChild
                (constantIndex $ Term $ FTA.transitionSymbol transition)
                (map indexOf $ FTA.transitionChildren transition)
    consumeChild built child = productIndex (mapIndex prepend built) child
    prepend build term arguments = build (term : arguments)

{- | Find the least finite term size of each productive state.

Start with no productive states and solve the least fixed point. A cycle with
no finite base remains absent. This keeps an empty recursive index finite.
-}
minimumSizes :: (Ord state) => Map.Map state [FTA.Transition state symbol ()] -> Map.Map state Int
minimumSizes rows = converge Map.empty
  where
    converge current =
        let next = Map.foldrWithKey addMinimum current rows
         in if next == current then current else converge next
    addMinimum state transitions known =
        case mapMaybe (transitionMinimum known) transitions of
            [] -> known
            sizes -> Map.insertWith min state (minimum sizes) known
    transitionMinimum known transition =
        (1 +) . sum <$> traverse (`Map.lookup` known) (FTA.transitionChildren transition)

{- | Count candidate runs of each reachable state in an acyclic graph.

Transition annotations are ignored. A constrained layer must discharge them
before treating these counts as accepted terms. A reachable cycle returns its
state. Empty states retain a zero count.
-}
countRuns :: (Ord state) => FTA.FTA state symbol guard -> Either state (Map.Map state Integer)
countRuns automaton =
    snd <$> countState Set.empty Map.empty (FTA.initialState automaton)
  where
    table = FTA.transitionTable automaton

    countState visiting counts state =
        case Map.lookup state counts of
            Just count -> Right (count, counts)
            Nothing
                | Set.member state visiting -> Left state
                | otherwise -> do
                    (transitionCounts, counted) <-
                        countTransitions
                            (Set.insert state visiting)
                            counts
                            (Map.findWithDefault [] state table)
                    let count = sum transitionCounts
                    pure (count, Map.insert state count counted)

    countTransitions _ counts [] = Right ([], counts)
    countTransitions visiting counts (transition : rest) = do
        (count, withChildren) <- countChildren visiting counts $ FTA.transitionChildren transition
        (restCounts, finished) <- countTransitions visiting withChildren rest
        pure (count : restCounts, finished)

    countChildren _ counts [] = Right (1, counts)
    countChildren visiting counts (state : rest) = do
        (count, withState) <- countState visiting counts state
        (restCount, finished) <- countChildren visiting withState rest
        pure (count * restCount, finished)

{- | Find structural ambiguity in an acyclic graph.

The caller checks acyclicity first. Annotations are ignored. Two alternatives
overlap when their labels match and every child-state pair has a common term.
Each state pair is checked once, including repeated subtrees of a shared graph.
-}
ambiguousState :: (Ord state, Ord symbol) => FTA.FTA state symbol guard -> [state] -> Maybe state
ambiguousState automaton = go Map.empty
  where
    table = FTA.transitionTable automaton
    symbols = Map.map (Set.fromList . map FTA.transitionSymbol) table

    go _ [] = Nothing
    go cache (state : rest) =
        case anyTransitionsOverlap cache $ distinctPairs $ transitions state of
            (True, _) -> Just state
            (False, updated) -> go updated rest

    transitions state = Map.findWithDefault [] state table

    stateLanguagesOverlap cache left right =
        case Map.lookup pair cache of
            Just overlap -> (overlap, cache)
            Nothing ->
                let (overlap, updated) =
                        if Set.disjoint (rootSymbols left) (rootSymbols right)
                            then (False, cache)
                            else
                                anyTransitionsOverlap
                                    cache
                                    [ (leftTransition, rightTransition)
                                    | leftTransition <- transitions left
                                    , rightTransition <- transitions right
                                    ]
                 in (overlap, Map.insert pair overlap updated)
      where
        pair = (min left right, max left right)

    anyTransitionsOverlap cache [] = (False, cache)
    anyTransitionsOverlap cache ((left, right) : rest) =
        case transitionsOverlap cache left right of
            (True, updated) -> (True, updated)
            (False, updated) -> anyTransitionsOverlap updated rest

    transitionsOverlap cache left right
        | FTA.transitionSymbol left == FTA.transitionSymbol right
            && length leftChildren == length rightChildren
            && and
                ( zipWith
                    (\leftChild rightChild -> not $ Set.disjoint (rootSymbols leftChild) (rootSymbols rightChild))
                    leftChildren
                    rightChildren
                ) =
            allChildrenOverlap cache $ zip leftChildren rightChildren
        | otherwise = (False, cache)
      where
        leftChildren = FTA.transitionChildren left
        rightChildren = FTA.transitionChildren right

    allChildrenOverlap cache [] = (True, cache)
    allChildrenOverlap cache ((left, right) : rest) =
        case stateLanguagesOverlap cache left right of
            (False, updated) -> (False, updated)
            (True, updated) -> allChildrenOverlap updated rest

    rootSymbols state = Map.findWithDefault Set.empty state symbols

-- | Every unordered pair of distinct list elements.
distinctPairs :: [a] -> [(a, a)]
distinctPairs [] = []
distinctPairs (value : rest) = map (value,) rest <> distinctPairs rest

{- | Fold the constructor at one valid candidate-run rank directly into a value.

The caller supplies exact counts and a valid rank. No intermediate term is
constructed. Transition and child order define the mixed-radix rank domain.
-}
{-# INLINE foldAt #-}
foldAt :: (Ord state) => (symbol -> [a] -> a) -> FTA.FTA state symbol guard -> Map.Map state Integer -> Integer -> a
foldAt buildValue automaton counts = decode (FTA.initialState automaton)
  where
    table = FTA.transitionTable automaton
    decode state stateRank =
        case selectTransition stateRank $ Map.findWithDefault [] state table of
            Just (transition, transitionRank) ->
                buildValue (FTA.transitionSymbol transition) (decodeChildren transitionRank $ FTA.transitionChildren transition)
            Nothing -> error "foldAt: rank outside a counted automaton state"
    selectTransition _ [] = Nothing
    selectTransition remaining (transition : rest)
        | remaining < count = Just (transition, remaining)
        | otherwise = selectTransition (remaining - count) rest
      where
        count = product [Map.findWithDefault 0 child counts | child <- FTA.transitionChildren transition]
    decodeChildren _ [] = []
    decodeChildren remaining (child : rest) =
        let suffixCount = product [Map.findWithDefault 0 state counts | state <- rest]
            (childRank, restRank) = remaining `quotRem` suffixCount
         in decode child childRank : decodeChildren restRank rest
