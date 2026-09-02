{- | Compare three exact-uniform generators for the untyped-expression FTA.

The naive generator builds and recognizes generic terms, the bespoke generator
constructs the example datatype directly, and the FTA generator rank-decodes
the same finite language.
-}
module Main (main) where

import qualified Test.QuickCheck as QC

import qualified Data.Tree.FTA.Gen.QuickCheck as FTA
import Data.Tree.FTA.UntypedExpressionLanguage (
    Expression,
    evaluate,
    expressionCount,
    expressionsAtDepth,
    handwrittenExpressionGen,
    naiveExpressionGen,
 )
import GeneratorSpeedHarness (Benchmark (..), benchmarkMain)

main :: IO ()
main = benchmarkMain benchmark

-- | Untyped-expression benchmark configuration.
benchmark :: Benchmark Expression
benchmark =
    Benchmark
        { benchmarkSizeName = "depth"
        , benchmarkSizes = [1 .. 4]
        , benchmarkEngines = ["naive", "bespoke", "fta"]
        , benchmarkSampleCount = 100000
        , benchmarkMembers = expressionCount
        , benchmarkPrepare = prepare
        , benchmarkTally = evaluate
        }

-- | Construct one selected exact-depth generator.
prepare :: String -> Int -> IO (QC.Gen Expression)
prepare "naive" depth = pure $ naiveExpressionGen depth
prepare "bespoke" depth = pure $ handwrittenExpressionGen depth
prepare "fta" depth = pure $ FTA.toGen $ expressionsAtDepth depth
prepare engine _ = fail $ "unknown engine: " <> engine
