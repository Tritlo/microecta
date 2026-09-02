{- | Small construction syntax shared by ordinary FTAs and constrained views.

The graph model remains 'FTA.FTA'. These helpers only remove tuple and unit
noise at handwritten boundaries:

@
FTA.automaton expression
    [ FTA.row expression
        [ FTA.transition "zero" []
        , FTA.transition "add" [expression, expression]
        ]
    ]
@

Use 'guarded' instead of 'transition' for an ECTA equality constraint or any
other annotation theory.
-}
module Data.Tree.FTA.Syntax (
    Row,
    row,
    transition,
    guarded,
    automaton,
) where

import Data.Tree.FTA (FTA, FTAError, Transition (Transition))
import qualified Data.Tree.FTA as FTA

-- | One named state and all of its outgoing alternatives.
type Row state symbol guard = (state, [Transition state symbol guard])

-- | Associate a state with its outgoing alternatives.
row :: state -> [Transition state symbol guard] -> Row state symbol guard
row = (,)

-- | One ordinary, unconstrained FTA transition.
transition :: symbol -> [state] -> Transition state symbol ()
transition symbol children = Transition symbol children ()

-- | One transition carrying a constraint-theory annotation.
guarded :: symbol -> [state] -> guard -> Transition state symbol guard
guarded = Transition

-- | Validate an automaton described with 'row'.
automaton ::
    (Ord state, Ord symbol) =>
    state ->
    [Row state symbol guard] ->
    Either (FTAError state symbol) (FTA state symbol guard)
automaton = FTA.mkFTA
