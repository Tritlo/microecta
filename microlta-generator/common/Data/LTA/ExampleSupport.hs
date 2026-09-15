-- | Helpers shared by the example languages.
module Data.LTA.ExampleSupport (
    nonNegative,
    oneofOrDie,
) where

import Data.LTA (Refinement)
import qualified Data.LTA.Gen as LTA
import Data.LTA.Refinement (value, (.>=.))

-- | The non-negative integer refinement.
nonNegative :: Refinement
nonNegative = value .>=. (0 :: Int)

-- | Combine alternatives that an example knows to be non-empty.
oneofOrDie :: String -> [LTA.LTAGen a] -> LTA.LTAGen a
oneofOrDie context alternatives =
    case LTA.oneof alternatives of
        Left err -> error $ context <> " is unexpectedly empty: " <> show err
        Right generator -> generator
