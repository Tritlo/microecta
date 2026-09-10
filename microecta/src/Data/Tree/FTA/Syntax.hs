{- | Small construction syntax for ordinary FTAs.

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

Constraint theories provide their own syntax modules. In particular,
"Data.ECTA.FTA.Syntax" owns equality-constrained transitions and
"Data.LTA.Syntax" owns liquid transitions.
-}
module Data.Tree.FTA.Syntax (
    Row,
    row,
    transition,
    automaton,
) where

import Data.Tree.FTA (FTA, FTAError, Transition (Transition))
import qualified Data.Tree.FTA as FTA

-- | One named state and all of its outgoing alternatives.
type Row state symbol = (state, [Transition state symbol ()])

-- | Associate a state with its outgoing alternatives.
row :: state -> [Transition state symbol ()] -> Row state symbol
row = (,)

-- | One ordinary, unconstrained FTA transition.
transition :: symbol -> [state] -> Transition state symbol ()
transition symbol children = Transition symbol children ()

-- | Validate an automaton described with 'row'.
automaton ::
    (Ord state, Ord symbol) =>
    state ->
    [Row state symbol] ->
    Either (FTAError state symbol) (FTA state symbol ())
automaton = FTA.mkFTA
