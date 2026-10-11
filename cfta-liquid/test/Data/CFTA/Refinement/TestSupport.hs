{-# LANGUAGE OverloadedStrings #-}

-- | Helpers shared by the core specs.
module Data.CFTA.Refinement.TestSupport (
    tableEntailment,
    unusedEntailment,
    declarations,
) where

import Data.String (fromString)

import Data.CFTA.Formula (Name)
import Data.CFTA.Refinement (Entailment (Entailment), Verdict (..))
import Data.CFTA.Refinement.Expression (true)
import Data.CFTA.Symbol (valueName)

-- | A small decidable implication table that keeps syntax tests independent of Z3.
tableEntailment :: Entailment
tableEntailment = Entailment $ \antecedent consequent ->
    pure $
        if antecedent == consequent || consequent == true
            then Yes
            else No

-- | A solver that must not be consulted. A call fails the test.
unusedEntailment :: Entailment
unusedEntailment = Entailment $ \_ _ -> error "unusedEntailment: consulted"

-- | Integer declarations shared by the pruning and minimization examples.
declarations :: [Name]
declarations = [fromString valueName, "x", "y", "n"]
