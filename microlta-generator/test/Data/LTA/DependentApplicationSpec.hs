module Data.LTA.DependentApplicationSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.LiquidFixpoint (withZ3)
import Data.LTA.TypedExpressionLanguage

spec :: Spec
spec =
    describe "dependent function application" $ do
        it "matches result refinements after actual-for-formal substitution" $
            withZ3 solverDeclarations $ \solver -> do
                result <- LTA.compile solver dependentApplications
                case result of
                    Left err -> expectationFailure $ show err
                    Right compiled -> do
                        let expressions =
                                [ expression $ LTA.generatedValue generated
                                | rank <- [0 .. LTA.cardinality compiled - 1]
                                , Right generated <- [LTA.select rank compiled]
                                ]
                        expressions
                            `shouldBe` [ ApplyIncrement (Variable "x")
                                       , ApplyIncrement (Variable "p")
                                       ]

        it "prunes the negative argument before it reaches QuickCheck" $
            withZ3 solverDeclarations $ \solver -> do
                result <- LTA.compile solver dependentApplications
                case result of
                    Left err -> expectationFailure $ show err
                    Right compiled -> do
                        let expressions =
                                [ expression $ LTA.generatedValue generated
                                | rank <- [0 .. LTA.cardinality compiled - 1]
                                , Right generated <- [LTA.select rank compiled]
                                ]
                        ApplyIncrement (Variable "y") `elem` expressions `shouldBe` False
