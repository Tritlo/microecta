-- | Bound the shared graph, then validate its liquid constraints.
module Data.LTA.Gen.Internal.Bounded (boundAutomaton) where

import qualified Data.Map.Strict as Map

import Data.LTA (Automaton, AutomatonError, State (State), mkAutomaton)
import qualified Data.Tree.FTA as FTA

-- | Retain terms up to the given constructor depth. A leaf has depth zero.
boundAutomaton :: Int -> Automaton -> Either AutomatonError Automaton
boundAutomaton depth automaton = mkAutomaton (FTA.initialState bounded) (Map.toList $ FTA.transitionTable bounded)
  where
    bounded = FTA.mapStates State $ FTA.boundDepth depth automaton
