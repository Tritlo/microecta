module Data.CFTA.Gen.Refinement.SimilarityMinimizationSpec (spec) where

import Data.String (fromString)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Gen.Refinement.TestSupport (values)
import Data.CFTA.Gen.Refinement.TypedExpressionLanguage (nonNegative, solverDeclarations, value)
import Data.CFTA.Refinement.Expression (true, (./=.), (.>=.))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)

data Candidate = Candidate
    { similarityClass :: !String
    , candidateName :: !String
    }
    deriving (Eq, Show)

compileMinimized :: [LTAGen.Refined Candidate] -> IO [Candidate]
compileMinimized entries =
    withZ3 solverDeclarations $ \solver -> do
        minimized <- LTAGen.minimizePoolBy solver similarityClass entries
        case minimized of
            Left err -> expectationFailure (show err) >> pure []
            Right generator -> do
                compiled <- LTAGen.compile solver generator
                case compiled of
                    Left err -> expectationFailure (show err) >> pure []
                    Right language -> pure $ values language

spec :: Spec
spec =
    describe "LTA similarity minimisation" $ do
        it "retains the subtype and removes its supertype" $ do
            candidates <-
                compileMinimized
                    [ entry "number" "unknown" true
                    , entry "number" "natural" nonNegative
                    ]
            map candidateName candidates `shouldBe` ["natural"]

        it "does not merge values from different declared similarity classes" $ do
            candidates <-
                compileMinimized
                    [ entry "integer" "unknown integer" true
                    , entry "integer" "natural" nonNegative
                    , entry "boolean" "unknown boolean" true
                    ]
            map candidateName candidates
                `shouldBe` ["natural", "unknown boolean"]

        it "retains incomparable semantic representatives" $ do
            candidates <-
                compileMinimized
                    [ entry "number" "natural" (value .>=. (0 :: Int))
                    , entry "number" "non-zero" (value ./=. (0 :: Int))
                    ]
            map candidateName candidates `shouldBe` ["natural", "non-zero"]
  where
    entry className name refinement =
        LTAGen.Refined (Candidate className name) (fromString name) refinement
