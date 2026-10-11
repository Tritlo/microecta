{-# LANGUAGE OverloadedStrings #-}

-- | Helpers shared by the specs that run Z3.
module Data.CFTA.Refinement.TestSupport (
    declarations,
) where

import Data.String (fromString)

import Data.CFTA.Formula (Name)
import Data.CFTA.Symbol (valueName)

-- | Integer declarations shared by the pruning and minimization examples.
declarations :: [Name]
declarations = [fromString valueName, "x", "y", "n"]
