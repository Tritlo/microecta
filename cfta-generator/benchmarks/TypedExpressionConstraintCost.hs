{- | Compare ECTA equality constraints with equivalent LTA equality refinements.

Both engines generate the same exact-depth typed-expression language and force
the complete selected expression. The difference is the constraint theory:
structural path equality in the ECTA, versus Z3-pruned integer equality
refinements in the LTA.
-}
module Main (main) where

import qualified Test.QuickCheck as QC

import qualified Data.CFTA.Gen.Equality.QuickCheck as ECTAGen
import Data.CFTA.Gen.Refinement.EqualityTypedExpressionLanguage (
    compileEqualityExpressionsAtDepth,
 )
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Gen.TypedExpressionLanguage (
    TypedExpression,
    allTypes,
    expressionCount,
    expressionGenAtDepth,
    typedExpressionScore,
 )
import Data.CFTA.Index (Cardinality (..))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import GeneratorSpeedHarness (Benchmark (..), benchmarkMain)

main :: IO ()
main = benchmarkMain benchmark

-- | Equality-theory benchmark configuration.
benchmark :: Benchmark TypedExpression
benchmark =
    Benchmark
        { benchmarkSizeName = "depth"
        , benchmarkSizes = [1 .. 4]
        , benchmarkEngines = ["ecta", "lta-eq"]
        , benchmarkSampleCount = 20000
        , benchmarkMembers = expressionTotal
        , benchmarkPrepare = prepare
        , benchmarkTally = typedExpressionScore
        }

-- | Construct one exact-depth generator using the selected constraint engine.
prepare :: String -> Int -> IO (QC.Gen TypedExpression)
prepare "ecta" depth = pure $ ECTAGen.toGen $ expressionGenAtDepth depth
prepare "lta-eq" depth =
    withZ3 [] $ \solver -> do
        result <- compileEqualityExpressionsAtDepth solver depth
        case result of
            Left err -> fail $ "could not compile equality-refined LTA: " <> show err
            Right compiled
                | LTAGen.cardinality compiled == Right (Cardinality $ expressionTotal depth) ->
                    pure $ LTAGen.toGen compiled
                | otherwise ->
                    fail $
                        "LTA cardinality mismatch: expected "
                            <> show (expressionTotal depth)
                            <> ", got "
                            <> show (LTAGen.cardinality compiled)
prepare engine _ = fail $ "unknown engine: " <> engine

-- | Exact number of well-typed expressions across both result types.
expressionTotal :: Int -> Integer
expressionTotal depth = sum $ map (expressionCount depth) allTypes
