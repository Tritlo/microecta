{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}

{- | Process-isolated sampling benchmark shared by the FTA and ECTA examples.

Each cell gets a fresh process so process-global hash-consing tables cannot
make later depths look cheaper. The first-sample column includes generator
construction; the steady-state columns reuse that generator. Each complete
entry has a fixed workload and a 30-second wall-clock limit; entries which
cannot finish are reported as timeouts. Wall-clock time includes external work
such as solver calls.
-}
module GeneratorSpeedHarness (
    Benchmark (..),
    benchmarkMain,
) where

import Control.Monad (forM_)
import Data.List (intercalate, sort)
import GHC.Clock (getMonotonicTimeNSec)
import GHC.Stats (GCDetails (..), RTSStats (..), getRTSStats)
import System.Environment (getArgs, getExecutablePath)
import System.Mem (performMajorGC)
import System.Process (readProcess)
import System.Random (splitGen)
import qualified System.Timeout as Timeout
import qualified Test.QuickCheck.Gen as QCGen
import qualified Test.QuickCheck.Random as QCRandom
import Text.Printf (printf)

-- | One exact-language benchmark family.
data Benchmark a = Benchmark
    { benchmarkSizeName :: !String
    -- ^ Name of the varying boundary, such as depth or length.
    , benchmarkSizes :: ![Int]
    -- ^ Exact boundaries to measure.
    , benchmarkEngines :: ![String]
    -- ^ Child-process engine names in display order.
    , benchmarkSampleCount :: !Int
    -- ^ Fixed number of steady-state samples in every completed entry.
    , benchmarkMembers :: Int -> Integer
    -- ^ Cardinality of the language at one boundary.
    , benchmarkPrepare :: String -> Int -> IO (QCGen.Gen a)
    -- ^ Construct the selected generator.
    , benchmarkTally :: a -> Int
    -- ^ Force one sample and reduce it to a checksum contribution.
    }

-- | Wall-clock limit for one complete benchmark entry.
timeoutSeconds :: Int
timeoutSeconds = 30

-- | Samples drawn for the much cheaper loop-overhead reference rows.
referenceSampleCount :: Int
referenceSampleCount = 1000000

-- | Independent process-cold observations used for each reported median.
repeats :: Int
repeats = 3

-- | Fixed seed, split once per draw as QuickCheck does for a property.
rootSeed :: QCRandom.QCGen
rootSeed = QCRandom.mkQCGen 20260811

-- | Metrics produced by one child process.
data Cell = Cell
    { firstMicroseconds :: !Double
    , samplesPerSecond :: !Double
    , bytesPerSample :: !Double
    , setupBytes :: !Double
    , retainedBytes :: !Double
    , checksum :: !Double
    }

-- | Run a benchmark driver, or one isolated child cell when given arguments.
benchmarkMain :: Benchmark a -> IO ()
benchmarkMain benchmark =
    getArgs >>= \case
        [] -> driver benchmark
        [engine, size] -> child benchmark engine (read size)
        _ -> error "usage: benchmark [engine size]"

-- | Run all cells and print a compact table.
driver :: Benchmark a -> IO ()
driver Benchmark{benchmarkSizeName, benchmarkSizes, benchmarkEngines, benchmarkMembers} = do
    self <- getExecutablePath
    reference "empty generator" $ pure 0
    reference "one chooseInt" $ QCGen.chooseInt (0, 99)
    printf
        "\n%7s  %42s  %-10s  %12s  %12s  %11s  %12s  %14s  %10s\n"
        benchmarkSizeName
        "members"
        "engine"
        "first sample"
        "samples/s"
        "alloc/sample"
        "setup mem"
        "retained"
        "checksum"
    forM_ benchmarkSizes $ \size ->
        forM_ benchmarkEngines $ \engine -> do
            result <- repeatedCells self engine size repeats
            case result of
                Nothing ->
                    printf
                        "%7d  %42s  %-10s  %12s\n"
                        size
                        (show $ benchmarkMembers size)
                        engine
                        ("timeout (30s)" :: String)
                Just cells -> do
                    let cell = median cells
                    printf
                        "%7d  %42s  %-10s  %9.2f ms  %12.0f  %11s  %12s  %14s  %10.0f\n"
                        size
                        (show $ benchmarkMembers size)
                        engine
                        (firstMicroseconds cell / 1000)
                        (samplesPerSecond cell)
                        (humanBytes $ bytesPerSample cell)
                        (humanBytes $ setupBytes cell)
                        (humanBytes $ retainedBytes cell)
                        (checksum cell)
  where
    reference label generator = do
        (elapsed, _) <- timed $ drawMany id generator referenceSampleCount
        printf
            "%-20s %14.0f /s\n"
            (label :: String)
            (fromIntegral referenceSampleCount / elapsed)

-- | Start one isolated cell and parse its CSV metrics.
runCell :: FilePath -> String -> Int -> IO (Maybe Cell)
runCell self engine size = do
    completed <- Timeout.timeout (timeoutSeconds * 1000000) $ readProcess self [engine, show size] ""
    case completed of
        Nothing -> pure Nothing
        Just output -> case traverse readDouble $ splitOn ',' $ takeWhile (/= '\n') output of
            Just [first, rate, perSample, setup, held, sum_] ->
                pure $ Just $ Cell first rate perSample setup held sum_
            _ -> error $ "unreadable cell output: " <> show output

-- | Collect process-cold repetitions, stopping after the first timeout.
repeatedCells :: FilePath -> String -> Int -> Int -> IO (Maybe [Cell])
repeatedCells _ _ _ 0 = pure $ Just []
repeatedCells self engine size remaining = do
    result <- runCell self engine size
    case result of
        Nothing -> pure Nothing
        Just cell -> fmap (cell :) <$> repeatedCells self engine size (remaining - 1)

-- | Measure construction, steady-state sampling, allocation, and residency.
child :: Benchmark a -> String -> Int -> IO ()
child Benchmark{benchmarkPrepare, benchmarkSampleCount, benchmarkTally} engine size = do
    performMajorGC
    baseline <- liveBytes
    (firstElapsed, (generator, firstDraw)) <- timed $ do
        generator <- benchmarkPrepare engine size
        drawn <- drawOne benchmarkTally generator
        pure (generator, drawn)
    performMajorGC
    afterFirst <- liveBytes
    allocatedBefore <- allocatedBytes
    (steadyElapsed, total) <- timed $ drawMany benchmarkTally generator benchmarkSampleCount
    performMajorGC
    allocatedAfter <- allocatedBytes
    retained <- liveBytes
    let finalSeed = firstDraw + total
        lastDraw = benchmarkTally $ QCGen.unGen generator (QCRandom.mkQCGen finalSeed) 30
    putStrLn $
        intercalate "," $
            map
                show
                [ firstElapsed * 1e6
                , fromIntegral benchmarkSampleCount / steadyElapsed
                , (allocatedAfter - allocatedBefore) / fromIntegral benchmarkSampleCount
                , afterFirst - baseline
                , retained - baseline
                , fromIntegral (finalSeed + lastDraw)
                ]

-- | Draw and force one sample.
drawOne :: (a -> Int) -> QCGen.Gen a -> IO Int
drawOne measureOne generator =
    pure $! measureOne $ QCGen.unGen generator rootSeed 30

-- | Draw a strict run of samples and fold it into a checksum.
drawMany :: (a -> Int) -> QCGen.Gen a -> Int -> IO Int
drawMany measureOne generator count =
    pure $! fst $ foldl' step (0, rootSeed) [1 .. count]
  where
    step (!accumulator, generated) _ =
        let (drawn, next) = splitGen generated
         in (accumulator + measureOne (QCGen.unGen generator drawn 30), next)

-- | Wall seconds elapsed while running an action.
timed :: IO a -> IO (Double, a)
timed action = do
    start <- getMonotonicTimeNSec
    value <- action
    end <- getMonotonicTimeNSec
    pure (fromIntegral (end - start) / 1e9, value)

-- | Live bytes reported by the most recent major collection.
liveBytes :: IO Double
liveBytes = fromIntegral . gcdetails_live_bytes . gc <$> getRTSStats

-- | Bytes allocated since process start.
allocatedBytes :: IO Double
allocatedBytes = fromIntegral . allocated_bytes <$> getRTSStats

-- | Take the median of every metric independently.
median :: [Cell] -> Cell
median cells =
    Cell
        (middle firstMicroseconds)
        (middle samplesPerSecond)
        (middle bytesPerSample)
        (middle setupBytes)
        (middle retainedBytes)
        (middle checksum)
  where
    middle field = sort (map field cells) !! (length cells `div` 2)

-- | Render byte counts at a readable scale.
humanBytes :: Double -> String
humanBytes amount
    | amount < 0 = '-' : humanBytes (negate amount)
    | amount >= 1024 * 1024 = printf "%.2f MB" (amount / (1024 * 1024))
    | amount >= 1024 = printf "%.1f KB" (amount / 1024)
    | otherwise = printf "%.0f B" amount

-- | Split on one separator, retaining empty fields.
splitOn :: Char -> String -> [String]
splitOn separator input = case break (== separator) input of
    (field, []) -> [field]
    (field, _ : rest) -> field : splitOn separator rest

-- | Parse one complete floating-point field.
readDouble :: String -> Maybe Double
readDouble input = case reads input of
    [(value, "")] -> Just value
    _ -> Nothing
