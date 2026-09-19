{-# LANGUAGE ScopedTypeVariables #-}

-- | Group counted automaton ranks by finite observations without decoding terms.
module Data.CFTA.Gen.Refinement.Internal.AutomatonSource (
    Observations,
    groupAutomaton,
) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Data.CFTA as FTA
import qualified Data.CFTA.Gen.Refinement.Internal.SourceIndex as Source
import Data.CFTA.Refinement (
    LiquidSymbol (LiquidSymbol),
    Path,
    Symbol,
    path,
    unPath,
 )

-- | Requested positions that exist, with their complete labels and leaf flags.
type Observations = Map.Map Path (LiquidSymbol, Bool)

-- | Constructor arities present in at least one term of a group.
type Alphabet = Map.Map Symbol (Set.Set Int)

-- | Exact observation groups and their subsets of the state's raw rank domain.
type Groups = Map.Map Observations (Alphabet, Source.SourceIndex)

-- | Shared groups for one state and a sorted set of requested positions.
type Cache state = Map.Map (state, [Path]) Groups

{- | Partition the initial state's ranks by the requested observations.

The caller supplies the explicit view of an acyclic, unambiguous automaton
without constraints and its exact accepting-run counts. Each group's index
uses the complete state count as its domain. Transition order and child order
match the automaton's mixed-radix decoder. Empty states and transitions
contribute no groups.

Only requested positions occur in the keys. Missing positions are omitted.
Each group's alphabet includes its unobserved descendants as well. With no
requested positions, one group retains the complete state interval. Equal
state/request pairs share their groups; no accepted tree is constructed.
-}
groupAutomaton ::
    forall state constraint.
    (Ord state) =>
    [Path] ->
    FTA.FTA state LiquidSymbol constraint ->
    Map.Map state Integer ->
    Map.Map Observations (Map.Map Symbol (Set.Set Int), Source.SourceIndex)
groupAutomaton requested automaton counts =
    fst $ groupState (FTA.initialState automaton) requested Map.empty
  where
    table = FTA.transitionTable automaton
    count state = Map.findWithDefault 0 state counts

    groupState :: state -> [Path] -> Cache state -> (Groups, Cache state)
    groupState state targets cache
        | count state <= 0 = (Map.empty, cache)
        | Just groups <- Map.lookup key cache = (groups, cache)
        | otherwise =
            let (_, groups, completed) =
                    foldl'
                        (addTransition (count state) observesRoot childRequests)
                        (0, Map.empty, cache)
                        (Map.findWithDefault [] state table)
             in (groups, Map.insert key groups completed)
      where
        canonical = Set.toAscList $ Set.fromList targets
        key = (state, canonical)
        observesRoot = path [] `elem` canonical
        childRequests =
            Map.fromListWith
                (<>)
                [ (index, [path rest])
                | target <- canonical
                , index : rest <- [unPath target]
                ]

    addTransition bound observesRoot childRequests (offset, groups, cache) transition
        | total == 0 = (offset, groups, cache)
        | otherwise =
            let root =
                    if observesRoot
                        then Map.singleton (path []) (FTA.transitionSymbol transition, null children)
                        else Map.empty
                initial = Map.singleton root (Map.singleton symbol $ Set.singleton $ length children, Source.full 1)
                (variants, completed) =
                    foldl' (addChild childRequests) (initial, cache) $ zip [0 ..] children
                indexed =
                    Map.map
                        (\(alphabet, sources) -> (alphabet, Source.withDomain bound $ Source.shift offset sources))
                        variants
             in (offset + total, Map.unionWith mergeGroup groups indexed, completed)
      where
        children = FTA.transitionChildren transition
        LiquidSymbol symbol _ = FTA.transitionSymbol transition
        total = product $ map count children

    addChild childRequests (prefixes, cache) (index, child) =
        let (groups, completed) =
                groupState child (Map.findWithDefault [] index childRequests) cache
            combined =
                Map.fromListWith
                    mergeGroup
                    [ ( Map.union observations $ prefixObservations index childObservations
                      ,
                          ( Map.unionWith Set.union alphabet childAlphabet
                          , Source.product sources childSources
                          )
                      )
                    | (observations, (alphabet, sources)) <- Map.toList prefixes
                    , (childObservations, (childAlphabet, childSources)) <- Map.toList groups
                    ]
         in (combined, completed)

-- | Move a child's observations to their positions in the parent transition.
prefixObservations :: Int -> Observations -> Observations
prefixObservations index = Map.mapKeys (path . (index :) . unPath)

-- | Combine groups whose disjoint source subsets have the same observations.
mergeGroup :: (Alphabet, Source.SourceIndex) -> (Alphabet, Source.SourceIndex) -> (Alphabet, Source.SourceIndex)
mergeGroup (leftAlphabet, leftSources) (rightAlphabet, rightSources) =
    (Map.unionWith Set.union leftAlphabet rightAlphabet, Source.union leftSources rightSources)
