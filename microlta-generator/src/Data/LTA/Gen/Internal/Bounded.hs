-- | Bound the shared graph, then validate its liquid constraints.
module Data.LTA.Gen.Internal.Bounded (boundAutomaton) where

import qualified Data.Map.Strict as Map

import Data.LTA (Automaton, AutomatonError, State (State), mkAutomaton)
import qualified Data.Tree.FTA as FTA

-- | Retain terms up to the given constructor depth. A leaf has depth zero.
boundAutomaton :: Int -> Automaton -> Either AutomatonError Automaton
boundAutomaton depth automaton =
    mkAutomaton
        (State $ FTA.initialState bounded)
        [(State state, map transition outgoing) | (state, outgoing) <- Map.toList $ FTA.transitionTable bounded]
  where
    bounded = FTA.boundDepth depth automaton
    transition (FTA.Transition symbol children constraint) =
        FTA.Transition symbol (map State children) constraint
