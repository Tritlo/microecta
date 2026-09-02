{- | Compare three exact-uniform generators for typed stack-machine traces.

The naive generator rejects whole raw command sequences, the bespoke generator
tracks the abstract stack in Haskell, and the LTA generator compiles dependent
transition contracts with Z3 before rank-decoding accepted traces.
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
        , benchmarkSizes = [1 .. 4]
        , benchmarkEngines = ["naive", "bespoke", "lta"]
        , benchmarkSampleCount = 100000
        , benchmarkMembers = \length_ -> traceCount length_ (StackState [])
        , benchmarkPrepare = prepare
        , benchmarkTally = traceScore
        }

-- | Construct one selected exact-length generator.
prepare :: String -> Int -> IO (QC.Gen Trace)
prepare "naive" length_ = pure $ naiveTraceGen length_
prepare "bespoke" length_ = pure $ handwrittenTraceGen length_
prepare "lta" length_ =
    withZ3Assuming solverDeclarations solverAssumptions $ \solver -> do
        result <- LTA.compile solver $ tracesOfLength length_
        case result of
            Left err -> fail $ "could not compile LTA benchmark: " <> show err
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
