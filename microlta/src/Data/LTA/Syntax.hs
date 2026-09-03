{-# LANGUAGE PatternSynonyms #-}

{- | Handwritten construction syntax parallel to "Data.Tree.FTA.Syntax".

The only LTA-specific additions are the transition refinement and a
'GuardBuilder', so constructor arguments in a liquid constraint receive names
rather than numeric paths.
-}
module Data.LTA.Syntax (
    Row,
    row,
    transition,
    automaton,
    automatonWithFinals,
) where

import Data.LTA (
    Automaton,
    AutomatonError,
    Refinement,
    State,
    Symbol,
    Transition,
    mkAutomaton,
    mkAutomatonWithFinals,
    pattern Transition,
 )
import Data.LTA.Guard (GuardBuilder, buildGuard)

-- | One LTA state and all of its outgoing alternatives.
type Row = (State, [Transition])

-- | Associate a state with its outgoing alternatives.
row :: State -> [Transition] -> Row
row = (,)

-- | Build a refinement-labelled transition from a named constraint expression.
transition ::
    (GuardBuilder guard) =>
    Symbol ->
    Refinement ->
    [State] ->
    guard ->
    Transition
transition symbol refinement children guard =
    Transition symbol refinement children (buildGuard guard)

-- | Validate a handwritten LTA.
automaton :: State -> [Row] -> Either AutomatonError Automaton
automaton = mkAutomaton

-- | Validate an LTA with the paper's arbitrary non-empty final-state set.
automatonWithFinals :: [State] -> [Row] -> Either AutomatonError Automaton
automatonWithFinals = mkAutomatonWithFinals
