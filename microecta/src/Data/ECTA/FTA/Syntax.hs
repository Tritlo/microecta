{- | Handwritten equality-constrained FTA syntax.

This is the ECTA counterpart of "Data.Tree.FTA.Syntax". The shared graph stays
in "Data.Tree.FTA", while the equality annotation and its constructor live in
the ECTA namespace:

@
ECTA.transition "pair" [atom, atom]
    (mkEqConstraints [[path [0], path [1]]])
@
-}
module Data.ECTA.FTA.Syntax (
    Row,
    row,
    transition,
    automaton,
) where

import Data.ECTA.Paths (EqConstraints)
import Data.Tree.FTA (FTA, FTAError, Transition (Transition))
import qualified Data.Tree.FTA as FTA

-- | One ECTA-view state and all of its equality-constrained alternatives.
type Row state symbol = (state, [Transition state symbol EqConstraints])

-- | Associate a state with its outgoing alternatives.
row :: state -> [Transition state symbol EqConstraints] -> Row state symbol
row = (,)

-- | Build one transition carrying ECTA equality constraints.
transition :: symbol -> [state] -> EqConstraints -> Transition state symbol EqConstraints
transition = Transition

-- | Validate an equality-constrained FTA view described with 'row'.
automaton ::
    (Ord state, Ord symbol) =>
    state ->
    [Row state symbol] ->
    Either (FTAError state symbol) (FTA state symbol EqConstraints)
automaton = FTA.mkFTA
