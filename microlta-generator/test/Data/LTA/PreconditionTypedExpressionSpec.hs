module Data.LTA.PreconditionTypedExpressionSpec (spec) where

import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)
import qualified Test.QuickCheck as QC

import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.TestSupport (values)
import qualified Data.LTA.TestSupport as Support
import Data.LTA.TypedExpressionLanguage

compileOrFail :: LTA.LTAGen a -> IO (LTA.Compiled a)
compileOrFail generator =
    withZ3 solverDeclarations $ \solver ->
        Support.compileOrFail solver generator

spec :: Spec
spec =
    describe "refinement preconditions on typed expressions" $ do
        it "keeps exactly the arguments that prove sqrt's precondition" $ do
            compiled <- compileOrFail nonNegativeExpressions
            map expression (values compiled)
                `shouldBe` [ SquareRoot (Integer 0)
                           , SquareRoot (Integer 1)
                           , SquareRoot (Variable "n")
                           ]

        it "does not mistake non-negative for provably non-zero" $ do
            compiled <- compileOrFail divisions
            LTA.cardinality compiled `shouldBe` 10
            values compiled `shouldSatisfy` all denominatorIsProvablyNonZero

        it "samples only programs admitted by the liquid precondition" $ do
            compiled <- compileOrFail divisions
            result <-
                QC.quickCheckWithResult QC.stdArgs{QC.chatty = False, QC.maxSuccess = 200} $
                    LTA.forAll compiled denominatorIsProvablyNonZero
            QC.isSuccess result `shouldBe` True
  where
    denominatorIsProvablyNonZero RefinedExpression{expression = Divide _ denominator} =
        denominator == Integer (-1) || denominator == Integer 1
    denominatorIsProvablyNonZero _ = False
