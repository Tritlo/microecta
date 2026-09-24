-- | Helpers shared by the example languages.
module Data.CFTA.Gen.Refinement.ExampleSupport (
    nonNegative,
) where

import Data.CFTA.Refinement.Expression (Refinement, (.>=))

-- | The non-negative integer refinement.
nonNegative :: Refinement
nonNegative v = v .>= 0
