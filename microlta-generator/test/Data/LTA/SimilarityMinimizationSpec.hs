module Data.LTA.SimilarityMinimizationSpec (spec) where

import Data.String (fromString)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.LiquidFixpoint (withZ3)
import Data.LTA.Refinement (true, (./=.), (.>=.))
import Data.LTA.TypedExpressionLanguage (nonNegative, solverDeclarations, value)

data Candidate = Candidate
    { similarityClass :: !String
    , candidateName :: !String
    }
    deriving (Eq, Show)

compileMinimized :: [LTA.Refined Candidate] -> IO [Candidate]
compileMinimized entries =
    withZ3 solverDeclarations $ \solver -> do
        minimized <- LTA.minimizePoolBy solver similarityClass entries
        case minimized of
            Left err -> expectationFailure (show err) >> pure []
            Right generator -> do
                compiled <- LTA.compile solver generator
                case compiled of
                    Left err -> expectationFailure (show err) >> pure []
                    Right language ->
                        pure
                            [ LTA.generatedValue generated
                            | rank <- [0 .. LTA.cardinality language - 1]
                            , Right generated <- [LTA.select rank language]
                            ]

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
        LTA.refined (Candidate className name) (fromString name) refinement
