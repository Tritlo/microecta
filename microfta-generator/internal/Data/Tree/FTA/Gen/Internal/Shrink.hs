{-# LANGUAGE BangPatterns #-}

-- | Structural rank shrinking for acyclic automata without transition constraints.
module Data.Tree.FTA.Gen.Internal.Shrink (automatonShrinkRanks) where

import Data.Containers.ListUtils (nubOrd)
import Data.List (mapAccumL, mapAccumR)
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)

import Data.CFTA (
    PlainFTA,
    initialState,
    transitionChildren,
    transitionTable,
 )

-- | Shared size bounds and ranked alternatives for one live state.
data StatePlan state = StatePlan
    { minimumRun :: !(Integer, Integer)
    -- ^ Minimum node count and its state-local rank.
    , maximumNodes :: !Integer
    -- ^ Largest node count accepted by this state.
    , stateTransitions :: ![TransitionPlan state]
    -- ^ Live transitions in the decoder's order.
    }

-- | One live transition and its child rank strides.
data TransitionPlan state = TransitionPlan
    { rankOffset :: !Integer
    -- ^ First rank occupied by this transition.
    , rankCount :: !Integer
    -- ^ Number of runs accepted by this transition.
    , rankedChildren :: ![(state, Integer)]
    -- ^ Child states and their suffix cardinalities.
    , transitionMinimum :: !(Integer, Integer)
    -- ^ Minimum node count and its rank in the parent state.
    }

{- | Replace selected subtrees with strictly smaller runs of the same state.

The caller supplies exact counts for a finite acyclic automaton with no
transition constraints. Transition order and child order must match its rank decoder.
Each candidate reduces the number of tree nodes. The node counts use Integer
because a small shared graph can represent a tree larger than machine Int.
No term or generated value is constructed.

This module belongs to the @internal@ sublibrary. It is an integration
interface for the constrained generator packages, and its exports are not
covered by the PVP contract of the main library.
-}
automatonShrinkRanks :: (Ord state) => PlainFTA state symbol -> Map.Map state Integer -> Integer -> [Integer]
automatonShrinkRanks automaton counts = shrink
  where
    initial = initialState automaton
    count state = Map.findWithDefault 0 state counts

    -- Lazy values share each state's size bounds across all incoming edges.
    plans = LazyMap.map buildState $ Map.filterWithKey (\state _ -> count state > 0) $ transitionTable automaton
    plan state = plans Map.! state

    buildState transitions =
        StatePlan
            (minimum $ map transitionMinimum live)
            (maximum [1 + sum [maximumNodes $ plan child | (child, _) <- rankedChildren transition] | transition <- live])
            live
      where
        live = catMaybes $ snd $ mapAccumL buildTransition 0 transitions

    buildTransition offset transition =
        (offset + total, if total == 0 then Nothing else Just compiled)
      where
        (total, children) = mapAccumR (\suffix child -> (count child * suffix, (child, suffix))) 1 $ transitionChildren transition
        compiled =
            TransitionPlan
                offset
                total
                children
                ( 1 + sum [fst $ minimumRun $ plan child | (child, _) <- children]
                , offset + sum [snd (minimumRun $ plan child) * stride | (child, stride) <- children]
                )

    shrink rank
        | rank < 0 || rank >= count initial = []
        | fixedSize initial = []
        | otherwise = nubOrd $ lookupShrinks initial rank
      where
        (_, sizes) = measure Map.empty initial rank
        shrinks = LazyMap.mapWithKey (\(state, localRank) nodes -> shrinkRun state localRank nodes) sizes
        lookupShrinks state localRank = Map.findWithDefault [] (state, localRank) shrinks

        shrinkRun state localRank nodes
            | nodes == fst (minimumRun current) = []
            | otherwise =
                [ candidate
                | (candidateNodes, candidate) <- minimumRun current : map transitionMinimum (stateTransitions current)
                , candidateNodes < nodes
                ]
                    <> [ localRank + (candidate - childRank) * stride
                       | (child, childRank, stride) <- selectedChildren localRank $ selectTransition current localRank
                       , candidate <- lookupShrinks child childRank
                       ]
          where
            current = plan state

    fixedSize state = fst (minimumRun current) == maximumNodes current
      where
        current = plan state

    -- Repeated occurrences of the same selected run share one size calculation.
    measure cache state rank
        | fixedSize state = (fst $ minimumRun $ plan state, cache)
        | Just nodes <- Map.lookup (state, rank) cache = (nodes, cache)
        | otherwise =
            let transition = selectTransition (plan state) rank
                (!nodes, updated) = measureChildren cache 1 $ selectedChildren rank transition
             in (nodes, Map.insert (state, rank) nodes updated)

    measureChildren cache !nodes [] = (nodes, cache)
    measureChildren cache !nodes ((child, rank, _) : rest) =
        let (!childNodes, updated) = measure cache child rank
         in measureChildren updated (nodes + childNodes) rest

-- | Find the transition that contains one valid state-local rank.
selectTransition :: StatePlan state -> Integer -> TransitionPlan state
selectTransition state rank = go $ stateTransitions state
  where
    go [] = error "automatonShrinkRanks: rank outside a counted state"
    go (transition : rest)
        | rank < rankOffset transition + rankCount transition = transition
        | otherwise = go rest

-- | Read each selected child rank and its stride in the parent rank.
selectedChildren :: Integer -> TransitionPlan state -> [(state, Integer, Integer)]
selectedChildren rank transition = go (rank - rankOffset transition) $ rankedChildren transition
  where
    go _ [] = []
    go remaining ((child, stride) : rest) =
        let (childRank, suffixRank) = remaining `quotRem` stride
         in (child, childRank, stride) : go suffixRank rest
