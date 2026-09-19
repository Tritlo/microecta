-- | Helpers shared by the generator specs.
module Data.LTA.TestSupport (
    compileOrFail,
    rightOrFail,
    values,
) where

import Test.Hspec (expectationFailure)

import Data.CFTA.Refinement (Entailment)
import qualified Data.LTA.Gen as LTA

-- | Compile a fixture, reporting a compilation error as an Hspec failure.
compileOrFail :: Entailment -> LTA.LTAGen a -> IO (LTA.Compiled a)
compileOrFail solver generator = LTA.compile solver generator >>= rightOrFail

-- | Report a construction or compilation error as an Hspec failure.
rightOrFail :: (Show err) => Either err a -> IO a
rightOrFail result =
    case result of
        Left err -> expectationFailure (show err) >> fail "unreachable"
        Right compiled -> pure compiled

-- | Enumerate one small compiled language in stable rank order.
values :: LTA.Compiled a -> [a]
values compiled =
    [ LTA.generatedValue generated
    | rank <- [0 .. LTA.cardinality compiled - 1]
    , Right generated <- [LTA.unrank compiled rank]
    ]
