{- | Handwritten construction syntax parallel to "Data.Tree.FTA.Syntax".

The only LTA-specific additions are the transition refinement and a
'GuardBuilder', so constructor arguments in a liquid constraint receive names
rather than numeric paths.
-}
module Data.LTA.Syntax (
    Transition,
    Row,
    row,
    transition,
    automaton,
    automatonWithFinals,
) where

import Data.LTA (
    Automaton,
    AutomatonError (GuardArityMismatch),
    Refinement,
    State,
    Symbol,
    mkAutomaton,
    mkAutomatonWithFinals,
 )
import qualified Data.LTA as Core
import Data.LTA.Guard (GuardBuilder, buildGuard, guardArgumentCount)

-- | A named transition whose construction errors are checked by 'automaton'.
type Transition = Either AutomatonError Core.Transition

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
    case guardArgumentCount guard of
        Just supplied
            | supplied /= length children ->
                Left $ GuardArityMismatch symbol (length children) supplied
        _ -> Right $ Core.Transition symbol refinement children (buildGuard guard)

-- | Validate a handwritten LTA.
automaton :: State -> [Row] -> Either AutomatonError Automaton
automaton initial rows = checkedRows rows >>= mkAutomaton initial

-- | Validate an LTA with the paper's arbitrary final-state set.
automatonWithFinals :: [State] -> [Row] -> Either AutomatonError Automaton
automatonWithFinals finals rows = checkedRows rows >>= mkAutomatonWithFinals finals

-- | Resolve named construction errors before validating the automaton graph.
checkedRows :: [Row] -> Either AutomatonError [(State, [Core.Transition])]
checkedRows = traverse $ \(state, transitions) -> (,) state <$> sequence transitions
