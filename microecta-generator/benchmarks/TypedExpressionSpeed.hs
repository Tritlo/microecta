{- | Compare three exact-uniform generators for the typed-expression language.

The naive generator creates raw applications and rejects ill-typed roots, the
bespoke generator carries the desired result type through handwritten code,
and the ECTA generator compiles the same dependency as path equalities.
-}
module Main (main) where

import qualified Test.QuickCheck as QC

import qualified Data.ECTA.Gen.QuickCheck as ECTA
import Data.ECTA.TypedExpressionLanguage (
    TypedExpression (expressionType),
    allTypes,
    expressionCount,
    expressionGenAtDepth,
    handwrittenExpressionGen,
    naiveExpressionGen,
 )
import GeneratorSpeedHarness (Benchmark (..), benchmarkMain)

main :: IO ()
main = benchmarkMain benchmark

-- | Typed-expression benchmark configuration.
benchmark :: Benchmark TypedExpression
benchmark =
    Benchmark
        { benchmarkSizeName = "depth"
        , benchmarkSizes = [1 .. 4]
        , benchmarkEngines = ["naive", "bespoke", "ecta"]
        , benchmarkSampleCount = 20000
        , benchmarkMembers = \depth -> sum $ map (expressionCount depth) allTypes
        , benchmarkPrepare = prepare
        , benchmarkTally = fromEnum . expressionType
        }

-- | Construct one selected exact-depth generator.
prepare :: String -> Int -> IO (QC.Gen TypedExpression)
prepare "naive" depth = pure $ naiveExpressionGen depth
prepare "bespoke" depth = pure $ handwrittenExpressionGen depth
prepare "ecta" depth = pure $ ECTA.toGen $ expressionGenAtDepth depth
prepare engine _ = fail $ "unknown engine: " <> engine
