-- | Helpers shared by the example languages.
module Data.CFTA.Gen.Refinement.ExampleSupport (
    nonNegative,
) where

import Data.CFTA.Refinement (Refinement)
import Data.CFTA.Refinement.Expression (value, (.>=.))

-- | The non-negative integer refinement.
nonNegative :: Refinement
nonNegative = value .>=. (0 :: Int)
