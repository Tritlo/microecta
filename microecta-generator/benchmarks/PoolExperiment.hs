{-# LANGUAGE QualifiedDo #-}

{- | Experiments for freezing a small native QuickCheck universe as an ECTA.

The examples use the same pool more than once. This is the important case:
the finite universe becomes inspectable, and constraints can correlate choices
from it without rejection.
-}
module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Ratio ((%))
import System.CPUTime (getCPUTime)
import System.Random (splitGen)
import Text.Printf (printf)

import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Gen as QCGen
import qualified Test.QuickCheck.Random as QCRandom

import Data.ECTA.Gen.QuickCheck (ECTAGen, Grouped, On (..))
import qualified Data.ECTA.Gen.QuickCheck as ECTAGen
import Data.ECTA.TypedExpressionLanguage (
    Expression (BoolLiteral, CharLiteral, IntLiteral),
    Type (TBool, TChar, TInt),
    TypedExpression (TypedExpression),
    applicationGen,
 )

-- | Samples per generator in each throughput row.
sampleCount :: Int
sampleCount = 200000

-- | Run the examples and scaling rows.
main :: IO ()
main = do
    collisionExample
    typedExpressionExample
    throughputExperiment

-- | Freeze native draws deterministically for repeatable experiments.
freeze :: Int -> Int -> QC.Gen a -> ECTAGen a
freeze seed sampleCount_ native =
    QCGen.unGen
        (ECTAGen.pool sampleCount_ native)
        (QCRandom.mkQCGen seed)
        30

collisionExample :: IO ()
collisionExample = do
    let integers = freeze 20260818 8 $ QC.chooseInteger (0, 3)
        values = members integers
        equalPairs = ECTAGen.match (id :==: id) integers integers
        accepted = either (const 0) id $ ECTAGen.cardinality equalPairs
        priorPairs = 8 * 8
    putStrLn "\nLarge native source, frozen as one shared finite universe"
    putStrLn $ "pool ranks: " <> show values
    putStrLn $ "exact equal-pair ranks: " <> show accepted <> " of " <> show priorPairs
    putStrLn $ "exact prior collision probability: " <> show (accepted % priorPairs)

typedExpressionExample :: IO ()
typedExpressionExample = do
    let integers = freeze 20260819 8 $ QC.chooseInt (-1000000, 1000000)
        expressionsByType = applicationGen $ pooledAtoms integers
        expressions = ECTAGen.ungroup expressionsByType
    putStrLn "\nTyped expressions with native integer literals"
    putStrLn $ "integer literal pool: " <> show (members integers)
    putStrLn $ "exact one-layer counts by result type: " <> show (ECTAGen.sizes expressionsByType)
    putStrLn $ "exact total one-layer expressions: " <> show (ECTAGen.cardinality expressions)

-- | Add native integers without enumerating them in the source code.
pooledAtoms :: ECTAGen Int -> Grouped Type TypedExpression
pooledAtoms integers =
    ECTAGen.oneofGrouped
        [ ECTAGen.keyed TInt $
            (TypedExpression TInt . IntLiteral) <$> integers
        , ECTAGen.keyed TBool $
            ECTAGen.elements
                [ TypedExpression TBool $ BoolLiteral False
                , TypedExpression TBool $ BoolLiteral True
                ]
        , ECTAGen.keyed TChar $
            ECTAGen.elements
                [ TypedExpression TChar $ CharLiteral 'a'
                , TypedExpression TChar $ CharLiteral 'z'
                ]
        ]

throughputExperiment :: IO ()
throughputExperiment = do
    putStrLn "\nPool scaling"
    printf
        "%6s  %12s  %12s  %12s  %12s  %12s  %8s\n"
        ("pool" :: String)
        ("freeze+count" :: String)
        ("join query" :: String)
        ("ecta/s" :: String)
        ("matched/s" :: String)
        ("native/s" :: String)
        ("ratio" :: String)
    mapM_ throughputRow [1, 5, 20, 100, 1000]

throughputRow :: Int -> IO ()
throughputRow poolSize = do
    startFreeze <- getCPUTime
    let native = QC.chooseInteger (0, 1000000000000)
        integers = freeze (20260818 + poolSize) poolSize native
        counts = ECTAGen.countBy id integers
        countChecksum =
            either
                (const (-1))
                (Map.foldlWithKey' (\total value count -> total + value + count) 0)
                counts
    endFreeze <- countChecksum `seq` getCPUTime

    startJoin <- getCPUTime
    let equalPairs = ECTAGen.match (id :==: id) integers integers
        joined = either (const (-1)) id $ ECTAGen.cardinality equalPairs
    endJoin <- joined `seq` getCPUTime

    (ectaRate, _) <- measureSamples id $ ECTAGen.toGen integers
    (matchedRate, _) <- measureSamples (uncurry (+)) $ ECTAGen.toGen equalPairs
    (nativeRate, _) <- measureSamples id native

    printf
        "%6d  %9.1f us  %9.1f us  %12.0f  %12.0f  %12.0f  %7.2fx\n"
        poolSize
        (picosecondsToMicroseconds $ endFreeze - startFreeze)
        (picosecondsToMicroseconds $ endJoin - startJoin)
        ectaRate
        matchedRate
        nativeRate
        (ectaRate / nativeRate)

-- | Enumerate a small transparent language in stable rank order.
members :: ECTAGen a -> Either ECTAGen.ECTAGenError [a]
members generator = do
    total <- ECTAGen.cardinality generator
    traverse (ECTAGen.unrank generator) [0 .. total - 1]

-- | Draw and force a deterministic sample stream.
measureSamples :: (a -> Integer) -> QC.Gen a -> IO (Double, Integer)
measureSamples tally generator = do
    start <- getCPUTime
    let checksum = fst $ foldl' step (0, QCRandom.mkQCGen 20260818) [1 .. sampleCount]
    end <- checksum `seq` getCPUTime
    let seconds = fromIntegral (end - start) / (1e12 :: Double)
    pure (fromIntegral sampleCount / seconds, checksum)
  where
    step (total, generated) _ =
        let (drawn, next) = splitGen generated
         in (total + tally (QCGen.unGen generator drawn 30), next)

picosecondsToMicroseconds :: Integer -> Double
picosecondsToMicroseconds value = fromIntegral value / 1000000
