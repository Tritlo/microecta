module Data.CFTA.Gen.Refinement.SimilarityMinimizationSpec (spec) where

import Data.String (fromString)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Gen.Refinement.TestSupport (values)
import Data.CFTA.Gen.Refinement.TypedExpressionLanguage (nonNegative, solverDeclarations)
import Data.CFTA.Refinement.Expression (true, (./=), (.==), (.>), (.>=))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)

data Candidate = Candidate
    { similarityClass :: !String
    , candidateName :: !String
    }
    deriving (Eq, Show)

compileMinimized :: [LTAGen.Refined Candidate] -> IO [Candidate]
compileMinimized entries =
    withZ3 solverDeclarations $ \solver -> do
        minimized <- LTAGen.minimizePoolOn solver similarityClass entries
        case minimized of
            Left err -> expectationFailure (show err) >> pure []
            Right generator -> do
                compiled <- LTAGen.compileWith solver generator
                case compiled of
                    Left err -> expectationFailure (show err) >> pure []
                    Right language -> pure $ values language

spec :: Spec
spec =
    describe "LTA similarity minimisation" $ do
        it "retains the subtype and removes its supertype" $ do
            candidates <-
                compileMinimized
                    [ entry "number" "unknown" (const true)
                    , entry "number" "natural" nonNegative
                    ]
            map candidateName candidates `shouldBe` ["natural"]

        it "does not merge values from different declared similarity classes" $ do
            candidates <-
                compileMinimized
                    [ entry "integer" "unknown integer" (const true)
                    , entry "integer" "natural" nonNegative
                    , entry "boolean" "unknown boolean" (const true)
                    ]
            map candidateName candidates
                `shouldBe` ["natural", "unknown boolean"]

        it "keeps the earlier of equivalent entries in any interning order" $ do
            -- The first pool interns the transition of the second entry, so in
            -- the next pool that transition has the older identity.
            _ <-
                compileMinimized
                    [ entry "number" "unknown" (const true)
                    , entry "number" "above six" (\v -> v .> 6)
                    ]
            candidates <-
                compileMinimized
                    [ entry "number" "at least seven" (\v -> v .>= 7)
                    , entry "number" "above six" (\v -> v .> 6)
                    ]
            map candidateName candidates `shouldBe` ["at least seven"]

        it "keeps the earlier of equivalent entries after index nine" $ do
            -- Pool symbols carry equal-width indices, so the symbol of entry 9
            -- sorts before the symbol of entry 10.
            candidates <-
                compileMinimized $
                    [entry "number" ("exactly " <> show value) (.== fromInteger value) | value <- [0 .. 8]]
                        <> [ entry "number" "at least one hundred" (.>= 100)
                           , entry "number" "above ninety-nine" (.> 99)
                           ]
            map candidateName candidates
                `shouldBe` ["exactly " <> show value | value <- [0 .. 8 :: Integer]] <> ["at least one hundred"]

        it "retains incomparable semantic representatives" $ do
            candidates <-
                compileMinimized
                    [ entry "number" "natural" (\v -> v .>= 0)
                    , entry "number" "non-zero" (\v -> v ./= 0)
                    ]
            map candidateName candidates `shouldBe` ["natural", "non-zero"]
  where
    entry className name refinement =
        LTAGen.Refined (Candidate className name) (fromString name) refinement
