{- | Compare ECTA equality constraints with equivalent LTA equality refinements.

Both engines generate the same exact-depth typed-expression language and force
the complete selected expression. The difference is the constraint theory:
structural path equality in the ECTA, versus Z3-pruned integer equality
refinements in the LTA.
-}
module Main (main) where

import qualified Test.QuickCheck as QC

import qualified Data.ECTA.Gen.QuickCheck as ECTA
import Data.ECTA.TypedExpressionLanguage (
    Expression (..),
    TypedExpression (..),
    allTypes,
    expressionCount,
    expressionGenAtDepth,
 )
import Data.LTA.EqualityTypedExpressionLanguage (
    compileEqualityExpressionsAtDepth,
    solverDeclarations,
 )
import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.LiquidFixpoint (withZ3)
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
prepare "ecta" depth = pure $ ECTA.toGen $ expressionGenAtDepth depth
prepare "lta-eq" depth =
    withZ3 solverDeclarations $ \solver -> do
        result <- compileEqualityExpressionsAtDepth solver depth
        case result of
            Left err -> fail $ "could not compile equality-refined LTA: " <> show err
            Right compiled
                | LTA.cardinality compiled == expressionTotal depth ->
                    pure $ LTA.toGen compiled
                | otherwise ->
                    fail $
                        "LTA cardinality mismatch: expected "
                            <> show (expressionTotal depth)
                            <> ", got "
                            <> show (LTA.cardinality compiled)
prepare engine _ = fail $ "unknown engine: " <> engine

-- | Exact number of well-typed expressions across both result types.
expressionTotal :: Int -> Integer
expressionTotal depth = sum $ map (expressionCount depth) allTypes

-- | Force and score every field of one typed expression.
typedExpressionScore :: TypedExpression -> Int
typedExpressionScore TypedExpression{expressionType, expression} =
    fromEnum expressionType + expressionScore expression

-- | Force the complete expression tree and return a stable checksum component.
expressionScore :: Expression -> Int
expressionScore (IntLiteral value) = 2 * value + 1
expressionScore (BoolLiteral value) = if value then 4 else 3
expressionScore (Not argument) = 5 + expressionScore argument
expressionScore (ApplyBinary function_ first second) =
    7 + fromEnum function_ + expressionScore first + expressionScore second
expressionScore (IfExpression condition ifTrue ifFalse) =
    13 + expressionScore condition + expressionScore ifTrue + expressionScore ifFalse
