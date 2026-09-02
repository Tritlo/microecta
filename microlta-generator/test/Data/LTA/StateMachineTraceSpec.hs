module Data.LTA.StateMachineTraceSpec (spec) where

import qualified Data.Set as Set
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import qualified Test.QuickCheck as QC

import Data.LTA (LiquidTerm (liquidRefinement))
import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.LiquidFixpoint (withZ3Assuming)
import Data.LTA.StateMachineTraceLanguage

-- | Compile one trace language with the symbolic model environment.
compileOrFail :: LTA.LTAGen a -> IO (LTA.Compiled a)
compileOrFail generator =
    withZ3Assuming solverDeclarations solverAssumptions $ \solver -> do
        result <- LTA.compile solver generator
        case result of
            Left err -> expectationFailure (show err) >> fail "unreachable"
            Right compiled -> pure compiled

-- | Compile the automaton-level flagship path with the symbolic model.
compileTraceOrFail :: Int -> IO (LTA.Compiled Trace)
compileTraceOrFail traceLength =
    withZ3Assuming solverDeclarations solverAssumptions $ \solver -> do
        result <- compileTracesOfLength solver traceLength
        case result of
            Left err -> expectationFailure (show err) >> fail "unreachable"
            Right compiled -> pure compiled

-- | Enumerate the accepted values in stable rank order.
values :: LTA.Compiled a -> [a]
values compiled =
    [ LTA.generatedValue generated
    | rank <- [0 .. LTA.cardinality compiled - 1]
    , Right generated <- [LTA.select rank compiled]
    ]

spec :: Spec
spec =
    describe "liquid typed stack-machine traces" $ do
        it "matches the independent trace counts through length four" $ do
            compiled <- traverse compileTraceOrFail [1 .. 4]
            map LTA.cardinality compiled
                `shouldBe` [traceCount length_ (StackState []) | length_ <- [1 .. 4]]

        it "counts the deeper benchmark language without enumerating traces" $
            [traceCount length_ (StackState []) | length_ <- [1 .. 10]]
                `shouldBe` [4, 22, 132, 556, 3104, 13760, 73528, 342136, 1783112, 8567224]

        it "retains the dependent command sequences and rejects ill-typed ones" $ do
            compiled <- compileTraceOrFail 3
            LTA.cardinality compiled `shouldBe` 132
            LTA.cardinality compiled `shouldBe` traceCount 3 (StackState [])
            let sequences = Set.fromList $ map (map eventCommand . traceEvents) $ values compiled
            sequences `shouldSatisfy` Set.member [Push (IntValue 0), Push (IntValue 1), Add]
            sequences `shouldSatisfy` Set.member [Push (BoolValue False), Push (BoolValue True), And]
            sequences `shouldSatisfy` Set.member [Push (IntValue 0), Push (IntValue 1), Equal]
            sequences `shouldSatisfy` Set.member [Push (BoolValue False), Not, Pop]
            sequences `shouldSatisfy` not . Set.member [Push (IntValue 0), Not, Pop]
            sequences `shouldSatisfy` not . Set.member [Push (IntValue 0), Push (BoolValue True), Add]

        it "predicts every response and post-state before concrete execution" $ do
            compiled <- compileTraceOrFail 3
            values compiled `shouldSatisfy` all traceIsValid

        it "carries the final stack type as the trace result refinement" $ do
            compiled <- compileTraceOrFail 3
            let generated =
                    [ member
                    | rank <- [0 .. LTA.cardinality compiled - 1]
                    , Right member <- [LTA.select rank compiled]
                    ]
            generated
                `shouldSatisfy` all
                    ( \member ->
                        liquidRefinement (LTA.generatedTerm member)
                            == stateRefinement (traceFinalState $ LTA.generatedValue member)
                    )

        it "shrinks only to shorter traces whose stack preconditions still hold" $ do
            generator <-
                case tracesUpTo 3 of
                    Left err -> expectationFailure (show err) >> fail "unreachable"
                    Right traces -> pure traces
            compiled <- compileOrFail generator
            let ranked =
                    [ (rank, LTA.generatedValue member)
                    | rank <- [0 .. LTA.cardinality compiled - 1]
                    , Right member <- [LTA.select rank compiled]
                    ]
                lengthThreeRanks =
                    [ rank
                    | (rank, trace) <- ranked
                    , length (traceEvents trace) == 3
                    ]
            case lengthThreeRanks of
                source : _ -> do
                    let shrunk =
                            [ LTA.generatedValue member
                            | rank <- LTA.shrinkRank compiled source
                            , Right member <- [LTA.select rank compiled]
                            ]
                    shrunk `shouldSatisfy` any ((< 3) . length . traceEvents)
                    shrunk `shouldSatisfy` all traceIsValid
                [] -> expectationFailure "no accepted three-step trace"

        it "gives QuickCheck a precondition-free property over valid traces" $ do
            generator <-
                case tracesUpTo 3 of
                    Left err -> expectationFailure (show err) >> fail "unreachable"
                    Right traces -> pure traces
            compiled <- compileOrFail generator
            result <-
                QC.quickCheckWithResult QC.stdArgs{QC.chatty = False, QC.maxSuccess = 200} $
                    LTA.forAll compiled $ \trace ->
                        QC.counterexample (show trace) $
                            replayTrace trace QC.=== Just (traceFinalState trace)
            QC.isSuccess result `shouldBe` True

        modifyMaxSuccess (const 300) $
            it "keeps both reference generators in the valid trace language" $
                QC.conjoin
                    [ QC.forAll (generator 4) $ \trace ->
                        QC.counterexample (show trace) $
                            QC.conjoin
                                [ QC.property $ traceIsValid trace
                                , length (traceEvents trace) QC.=== 4
                                ]
                    | generator <- [naiveTraceGen, handwrittenTraceGen]
                    ]
