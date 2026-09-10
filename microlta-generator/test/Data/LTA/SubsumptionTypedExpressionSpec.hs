module Data.LTA.SubsumptionTypedExpressionSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldContain)

import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.LiquidFixpoint (withZ3)
import Data.LTA.TypedExpressionLanguage

compileOrFail :: LTA.LTAGen a -> IO (LTA.Compiled a)
compileOrFail generator =
    withZ3 solverDeclarations $ \solver -> do
        result <- LTA.compile solver generator
        case result of
            Left err -> expectationFailure (show err) >> fail "unreachable"
            Right compiled -> pure compiled

values :: LTA.Compiled a -> [a]
values compiled =
    [ LTA.generatedValue generated
    | rank <- [0 .. LTA.cardinality compiled - 1]
    , Right generated <- [LTA.select rank compiled]
    ]

spec :: Spec
spec =
    describe "subsumption in a typed expression language" $ do
        it "keeps every actual/expected pair justified by refinement subtyping" $ do
            compiled <- compileOrFail subtypePairs
            LTA.cardinality compiled `shouldBe` 11

        it "admits an exact natural where a non-negative value is expected" $ do
            compiled <- compileOrFail subtypePairs
            let expressions =
                    [ (expression actual, expression expected)
                    | (actual, expected) <- values compiled
                    ]
            expressions
                `shouldContain` [(Integer 1, Variable "n")]

        it "rejects a merely unknown value where non-negative is expected" $ do
            compiled <- compileOrFail subtypePairs
            let expressions =
                    [ (expression actual, expression expected)
                    | (actual, expected) <- values compiled
                    ]
            (Unknown, Variable "n") `elem` expressions `shouldBe` False

        it "shrinks an exact refinement through its accepted supertype" $ do
            compiled <- compileOrFail nonNegativeExpressions
            let exactOneRank = 1
                shrunkExpressions =
                    map (expression . LTA.generatedValue . snd) $
                        LTA.smallerMembers compiled exactOneRank
            shrunkExpressions `shouldContain` [SquareRoot $ Variable "n"]
