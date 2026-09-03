{- | Compare six exact-uniform generators and one QSM-style baseline.

The naive generator rejects whole raw command sequences, the bespoke generator
tracks exact suffix counts in Haskell, the QSM-style generator chooses a valid
next command from the current model, the ranked control hand-codes one global
rank decoder, and three LTA rows separate relational qualified-do compilation,
materialized automaton decoding, and fused automaton decoding. Every engine
except QSM-style online generation is exact-uniform; QSM has the same support
but intentionally uses a different distribution.
-}
module Main (main) where

import qualified Test.QuickCheck as QC

import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.LiquidFixpoint (withZ3Assuming)
import Data.LTA.StateMachineTraceLanguage
import GeneratorSpeedHarness (Benchmark (..), benchmarkMain)

main :: IO ()
main = benchmarkMain benchmark

-- | Typed stack-machine trace benchmark configuration.
benchmark :: Benchmark Trace
benchmark =
    Benchmark
        { benchmarkSizeName = "length"
        , benchmarkSizes = [1 .. 10] <> [12, 16, 20, 30, 40]
        , benchmarkEngines =
            [ "naive"
            , "qsm-online"
            , "bespoke"
            , "ranked"
            , "lta-do"
            , "lta-materialized"
            , "lta-fused"
            ]
        , benchmarkSampleCount = 20000
        , benchmarkMembers = \length_ -> traceCount length_ (StackState [])
        , benchmarkPrepare = prepare
        , benchmarkTally = traceScore
        }

-- | Construct one selected exact-length generator.
prepare :: String -> Int -> IO (QC.Gen Trace)
prepare "naive" length_ = pure $ naiveTraceGen length_
prepare "qsm-online" length_ = pure $ qsmTraceGen length_
prepare "bespoke" length_ = pure $ handwrittenTraceGen length_
prepare "ranked" length_ = pure $ rankedTraceGen length_
prepare "lta" length_ = prepare "lta-do" length_
prepare "lta-do" length_ =
    withZ3Assuming solverDeclarations solverAssumptions $ \solver -> do
        result <- compileTracesOfLength solver length_
        case result of
            Left err -> fail $ "could not compile LTA benchmark: " <> show err
            Right compiled -> pure $ LTA.toGen compiled
prepare "lta-materialized" length_ =
    withZ3Assuming solverDeclarations solverAssumptions $ \solver -> do
        result <- compileTraceAutomatonMaterialized solver length_
        case result of
            Left err -> fail $ "could not compile materialized LTA benchmark: " <> show err
            Right compiled -> pure $ LTA.toGen compiled
prepare "lta-fused" length_ =
    withZ3Assuming solverDeclarations solverAssumptions $ \solver -> do
        result <- compileTraceAutomatonFused solver length_
        case result of
            Left err -> fail $ "could not compile fused LTA benchmark: " <> show err
            Right compiled -> pure $ LTA.toGen compiled
prepare engine _ = fail $ "unknown engine: " <> engine

-- | Force every trace field and reduce it to a stable checksum contribution.
traceScore :: Trace -> Int
traceScore Trace{traceEvents, traceFinalState} =
    foldl' (\score event -> score + eventScore event) (encodeState traceFinalState) traceEvents

-- | Force and score one predicted transition.
eventScore :: Event -> Int
eventScore Event{eventBefore, eventCommand, eventResponse, eventAfter} =
    encodeState eventBefore
        + commandScore eventCommand
        + responseScore eventResponse
        + encodeState eventAfter

-- | Give every command constructor and pushed value a distinct score.
commandScore :: Command -> Int
commandScore (Push pushed) = 10 + valueScore pushed
commandScore Add = 20
commandScore And = 21
commandScore Equal = 22
commandScore Not = 23
commandScore Pop = 24

-- | Give each concrete literal a distinct score.
valueScore :: Value -> Int
valueScore (IntValue integer) = 2 * integer
valueScore (BoolValue boolean) = if boolean then 3 else 2

-- | Give each predicted response a distinct score.
responseScore :: Response -> Int
responseScore Accepted = 30
responseScore (Popped TInt) = 31
responseScore (Popped TBool) = 32
