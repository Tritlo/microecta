module Data.CFTA.Gen.Refinement.SubsumptionTypedExpressionSpec (spec) where

import Test.Hspec (Spec, describe, it, shouldBe, shouldContain)

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Gen.Refinement.TestSupport (values)
import qualified Data.CFTA.Gen.Refinement.TestSupport as Support
import Data.CFTA.Gen.Refinement.TypedExpressionLanguage
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)

compileOrFail :: LTAGen.LTAGen a -> IO (LTAGen.LTAGen a)
compileOrFail generator =
    withZ3 solverDeclarations $ \solver ->
        Support.compileOrFail solver generator

spec :: Spec
spec =
    describe "subsumption in a typed expression language" $ do
        it "keeps every actual/expected pair justified by refinement subtyping" $ do
            compiled <- compileOrFail subtypePairs
            LTAGen.cardinality compiled `shouldBe` Right 11

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
