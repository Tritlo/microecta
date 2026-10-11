module Data.CFTA.Gen.Refinement.DependentApplicationSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Gen.Refinement.TestSupport (values)
import Data.CFTA.Gen.Refinement.TypedExpressionLanguage
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)

spec :: Spec
spec =
    describe "dependent function application" $ do
        it "keeps the positive arguments x and p and prunes the negative y" $
            withZ3 [] $ \solver -> do
                result <- LTAGen.compileWith solver dependentApplications
                case result of
                    Left err -> expectationFailure $ show err
                    Right compiled -> do
                        map expression (values compiled)
                            `shouldBe` [ ApplyIncrement (Variable "x")
                                       , ApplyIncrement (Variable "p")
                                       ]
