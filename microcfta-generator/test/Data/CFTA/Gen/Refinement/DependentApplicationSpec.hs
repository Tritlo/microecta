module Data.CFTA.Gen.Refinement.DependentApplicationSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTA
import Data.CFTA.Gen.Refinement.TestSupport (values)
import Data.CFTA.Gen.Refinement.TypedExpressionLanguage
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)

spec :: Spec
spec =
    describe "dependent function application" $ do
        it "matches result refinements after actual-for-formal substitution" $
            withZ3 solverDeclarations $ \solver -> do
                result <- LTA.compile solver dependentApplications
                case result of
                    Left err -> expectationFailure $ show err
                    Right compiled -> do
                        map expression (values compiled)
                            `shouldBe` [ ApplyIncrement (Variable "x")
                                       , ApplyIncrement (Variable "p")
                                       ]

        it "prunes the negative argument before it reaches QuickCheck" $
            withZ3 solverDeclarations $ \solver -> do
                result <- LTA.compile solver dependentApplications
                case result of
                    Left err -> expectationFailure $ show err
                    Right compiled -> do
                        ApplyIncrement (Variable "y") `elem` map expression (values compiled) `shouldBe` False
