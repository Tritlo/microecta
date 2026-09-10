module Data.LTA.SafeBufferSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import qualified Test.QuickCheck as QC

import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.LiquidFixpoint (withZ3Assuming)
import Data.LTA.SafeBufferLanguage

compileOrFail :: LTA.LTAGen a -> IO (LTA.Compiled a)
compileOrFail generator =
    withZ3Assuming solverDeclarations solverAssumptions $ \solver -> do
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
    describe "solver-checked buffer programs" $ do
        it "keeps exactly the symbolic indexes proved in bounds" $ do
            compiled <- compileOrFail safeReads
            values compiled
                `shouldBe` [ ReadAt (Source "singleton" [10]) 0
                           , ReadAt (Source "triple" [20, 21, 22]) 0
                           , ReadAt (Source "triple" [20, 21, 22]) 1
                           , ReadAt (Source "triple" [20, 21, 22]) 2
                           ]

        it "uses two substitutions to retain one exact append result per pair" $ do
            compiled <- compileOrFail appendedBuffers
            LTA.cardinality compiled `shouldBe` 9
            values compiled `shouldSatisfy` all appendLengthIsCorrect

        it "carries append refinements into a later non-empty precondition" $ do
            compiled <- compileOrFail safeHeads
            LTA.cardinality compiled `shouldBe` 10
            values compiled `shouldSatisfy` all programIsSafe

        it "gives QuickCheck a total property over an otherwise partial interpreter" $ do
            compiled <- compileOrFail safePrograms
            LTA.cardinality compiled `shouldBe` 14
            result <-
                QC.quickCheckWithResult QC.stdArgs{QC.chatty = False, QC.maxSuccess = 200} $
                    LTA.forAll compiled $ \program ->
                        programIsSafe program
                            QC..&&. safeResult program QC.=== Just (runProgram program)
            QC.isSuccess result `shouldBe` True
  where
    appendLengthIsCorrect RefinedBuffer{bufferExpression = Append left right} =
        length (evaluateBuffer $ Append left right)
            == length (evaluateBuffer left) + length (evaluateBuffer right)
    appendLengthIsCorrect _ = False

safeResult :: Program -> Maybe Int
safeResult (ReadAt buffer index) =
    case drop index $ evaluateBuffer buffer of
        element : _ | index >= 0 -> Just element
        _ -> Nothing
safeResult (ReadHead buffer) =
    case evaluateBuffer buffer of
        element : _ -> Just element
        [] -> Nothing
