-- | Draw retained source names and type groups of the typed expression generators.
module Main (main) where

import qualified Data.Text as Text

import qualified Data.CFTA.Gen.Equality as ECTAGen
import Data.CFTA.Gen.TypedExpressionLanguage (
    Type (TInt),
    depthByType,
    expressionGenAtDepth,
    recursiveExpressions,
 )

-- | Print finite and recursive diagnostic graphs.
main :: IO ()
main = do
    putStrLn "Source choices retain names and signatures. Equality witnesses show their type groups."
    putStrLn "State names q0, q1, ... are local to each drawing."
    putStrLn "Locations use @alternative:child/..., with @root for the initial state."
    drawSupport "Exact depth 1: both result types" $ expressionGenAtDepth 1
    drawSupport "Exact depth 1: TInt" $ ECTAGen.atKey TInt $ depthByType 1
    drawSupport "Recursive: TInt" $ ECTAGen.atKey TInt recursiveExpressions

-- | Read retained diagnostic metadata and draw its state and transition labels.
drawSupport :: String -> ECTAGen.ECTAGen value -> IO ()
drawSupport title generator = do
    inspection <- ECTAGen.orFail $ ECTAGen.inspect generator
    putStrLn $ "\n" <> title <> maybe "" (\name -> " [" <> Text.unpack name <> "]") (ECTAGen.inspectionName inspection)
    putStrLn $ ECTAGen.drawInspection inspection
