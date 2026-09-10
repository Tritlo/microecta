module Data.LTA.SizedVectorSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import qualified Test.QuickCheck as QC

import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.LiquidFixpoint (withZ3)
import Data.LTA.SizedVectorLanguage

-- | Compile one sized-vector language or fail the surrounding example.
compileOrFail :: Int -> LTA.LTAGen a -> IO (LTA.Compiled a)
compileOrFail depth generator =
    withZ3 (solverDeclarationsAtDepth depth) $ \solver -> do
        result <- LTA.compile solver generator
        case result of
            Left err -> expectationFailure (show err) >> fail "unreachable"
            Right compiled -> pure compiled

-- | Enumerate one small compiled language in stable rank order.
values :: LTA.Compiled a -> [a]
values compiled =
    [ LTA.generatedValue generated
    | rank <- [0 .. LTA.cardinality compiled - 1]
    , Right generated <- [LTA.select rank compiled]
    ]

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
                        QC.counterexample (show program) $
                            QC.property $
                                programIsSafe program && (runProgram program `seq` True)
            QC.isSuccess result `shouldBe` True
