{-# LANGUAGE OverloadedStrings #-}

-- | Helpers shared by the core specs.
module Data.CFTA.Refinement.TestSupport (
    tableEntailment,
    unusedEntailment,
    declarations,
) where

import Data.CFTA.Refinement (Entailment (Entailment), Verdict (..))
import Data.CFTA.Refinement.Expression (true)
import qualified Language.Fixpoint.Types as Fixpoint

-- | A small decidable implication table that keeps syntax tests independent of Z3.
tableEntailment :: Entailment
tableEntailment = Entailment $ \antecedent consequent ->
    pure $
        if antecedent == consequent || consequent == true
            then Yes
            else No

-- | A solver that must not be consulted.
unusedEntailment :: Entailment
unusedEntailment = Entailment $ \_ _ -> pure Unknown

-- | Integer declarations shared by the pruning and minimization examples.
declarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
declarations =
    [ (Fixpoint.symbol name, Fixpoint.FInt)
    | name <- ["v", "x", "y", "n"] :: [String]
    ]
