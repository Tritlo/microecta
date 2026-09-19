module Data.CFTA.Gen.Refinement.SizedVectorSpec (spec) where

import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)
import qualified Test.QuickCheck as QC

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTA
import Data.CFTA.Gen.Refinement.SizedVectorLanguage
import Data.CFTA.Gen.Refinement.TestSupport (values)
import qualified Data.CFTA.Gen.Refinement.TestSupport as Support
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)

-- | Compile one sized-vector language or fail the surrounding example.
compileOrFail :: Int -> LTA.LTAGen a -> IO (LTA.Compiled a)
compileOrFail depth generator =
    withZ3 (solverDeclarationsAtDepth depth) $ \solver ->
        Support.compileOrFail solver generator

spec :: Spec
spec =
    describe "sized-vector pipelines" $ do
        it "proves append, take, and zip result lengths" $ do
            compiled <- compileOrFail 1 $ vectorsAtDepth 1
            LTA.cardinality compiled `shouldBe` 20
            values compiled `shouldSatisfy` all vectorLengthIsCorrect

        it "keeps exactly the safe indexes over one operation layer" $ do
            compiled <- compileOrFail 1 $ safeProgramsAtDepth 1
            LTA.cardinality compiled `shouldBe` 44
            values compiled `shouldSatisfy` all programIsSafe

        it "makes the partial interpreter total for generated programs" $ do
            compiled <- compileOrFail 1 $ safeProgramsAtDepth 1
            result <-
                QC.quickCheckWithResult QC.stdArgs{QC.chatty = False, QC.maxSuccess = 200} $
                    LTA.forAll compiled $ \program ->
                        QC.counterexample (show program)
                            $ QC.property
                            $ programIsSafe program && (runProgram program `seq` True)
            QC.isSuccess result `shouldBe` True
