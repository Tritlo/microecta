{-# LANGUAGE OverloadedStrings #-}

-- | Helpers shared by the specs that run Z3.
module Data.CFTA.Refinement.TestSupport (
    declarations,
) where

import Data.CFTA.Symbol (valueName)
import qualified Language.Fixpoint.Types as Fixpoint

-- | Integer declarations shared by the pruning and minimization examples.
declarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
declarations =
    [ (Fixpoint.symbol name, Fixpoint.FInt)
    | name <- [valueName, "x", "y", "n"] :: [String]
    ]
