{- | Transparent generators against a handwritten QuickCheck baseline, on the
same well-typed expression language.

Both generators draw uniformly from the same exact-depth language, so the
comparison is like for like: the ECTA generator lowers to a compiled rank
decoder and draws once per sample, while the handwritten one walks nested
'QCGen.frequency' choices with the same exact weights and draws once per node.

A steady-state rate on its own flatters the ECTA side, because the decoder has
to be built before it can draw and that cost does not appear in a rate. Four
numbers are reported per cell instead: the time to the first expression, which
is what a single property run pays; the rate once the generator is built; the
allocation per sample; and memory, as what the generator holds once it can draw
and as what it still holds after the whole run. Both memory figures are net of
what the same process holds before the generator is built.

Measuring the second one takes care: a generator that is never used again is
unreachable by the time the reading is taken, and a collected generator reads
as one that retains nothing.

Each cell runs in its own process. It has to: the hash-consing and memo tables
under the ECTA generator are process-global and never evict, so measuring
depth 4 after depth 1 would let it reuse depth 1's interned nodes and report a
setup cost that no first run can reproduce. Each cell is run three times and
the median of every metric reported, because a process-cold measurement of a
few milliseconds is otherwise mostly noise.

The two reference rows come first, because they set what the rest can mean: an
empty generator measures the loop itself, and a single 'QCGen.chooseInt'
measures one QuickCheck draw. A generator costing one draw cannot beat the
second row, so the ECTA-to-handwritten ratio moves with the cost of a draw in
the QuickCheck and random versions in use -- compare the columns across engine
changes on one machine, not against ratios recorded elsewhere.

Each row prints a result-type checksum. It is a smoke check over the sampled
stream, not a proof that the complete language or rank order is unchanged. The
artifact's independent exhaustive verifier checks language equality.
-}
module Main (main) where

import Control.Monad (forM_, replicateM)
import Data.List (intercalate, sort)
import GHC.Stats (GCDetails (..), RTSStats (..), getRTSStats)
import System.CPUTime (getCPUTime)
import System.Environment (getArgs, getExecutablePath)
import System.Mem (performMajorGC)
import System.Process (readProcess)
import System.Random (splitGen)
import Text.Printf (printf)

import qualified Test.QuickCheck.Gen as QCGen
import qualified Test.QuickCheck.Random as QCRandom

import qualified Data.ECTA.Gen.QuickCheck as ECTAGen
import Data.ECTA.TypedExpressionLanguage (
    TypedExpression (expressionType),
    expressionGenAtDepth,
    handwrittenExpressionGen,
 )

-- | Samples drawn per cell, after one untimed warm-up draw.
sampleCount :: Int
sampleCount = 100000

{- | Samples drawn for the two reference rows.

They are an order of magnitude cheaper per draw than any real generator, so
they need a longer run to settle.
-}
referenceSampleCount :: Int
referenceSampleCount = 1000000

-- | Depths compared, one pair of rows each.
depths :: [Int]
depths = [1 .. 4]

-- | Generators compared, by the name a child process is given.
engines :: [String]
engines = ["ecta", "handwritten"]

-- | Times each cell is run before taking the median of every metric.
repeats :: Int
repeats = 3

{- | One fixed root seed, split per draw the way QuickCheck drives a property:
deterministic across runs and cheap next to a draw.
-}
rootSeed :: QCRandom.QCGen
rootSeed = QCRandom.mkQCGen 20260811

-- | Both generators for one depth, selected by the child's argument.
generatorFor :: String -> Int -> QCGen.Gen TypedExpression
generatorFor "ecta" depth = ECTAGen.toGen $ expressionGenAtDepth depth
generatorFor "handwritten" depth = handwrittenExpressionGen depth
generatorFor engine _ = error $ "unknown engine: " <> engine

{- | Force one sample down to a number.

Every field of a sampled expression is strict, so forcing the result type has
already forced the whole tree: this measures generation rather than adding a
second traversal.
-}
tally :: TypedExpression -> Int
tally = fromEnum . expressionType

-- | What one child process measures.
data Cell = Cell
    { firstMicroseconds :: !Double
    -- ^ Building the generator and drawing one expression, from cold.
    , expressionsPerSecond :: !Double
    -- ^ Rate once the generator is built.
    , bytesPerExpression :: !Double
    -- ^ Allocation per sample once the generator is built.
    , setupBytes :: !Double
    -- ^ Live bytes held once the generator can draw, over the empty process.
    , retainedBytes :: !Double
    -- ^ Live bytes still held after 'sampleCount' draws, over the empty process.
    , checksum :: !Double
    -- ^ Folded result types, a smoke check on the sampled stream.
    }

main :: IO ()
main =
    getArgs >>= \case
        [] -> driver
        [engine, depth] -> child engine (read depth)
        _ -> error "usage: typed-expression-speed [engine depth]"

{- | Run every cell in its own process and print the table.

The reference rows are measured here rather than in a child: they build no
generator, so they have nothing to keep out of another cell's process.
-}
driver :: IO ()
driver = do
    self <- getExecutablePath
    reference "empty generator" $ pure 0
    reference "one chooseInt" $ QCGen.chooseInt (0, 99)
    printf
        "\n%5s  %-12s  %12s  %12s  %11s  %12s  %14s  %10s\n"
        "depth"
        "engine"
        "first expr"
        "exprs/s"
        "alloc/expr"
        "setup mem"
        "retained"
        "checksum"
    forM_ depths $ \depth ->
        forM_ engines $ \engine -> do
            cell <- median <$> replicateM repeats (runCell self engine depth)
            printf
                "%5d  %-12s  %9.2f ms  %12.0f  %11s  %12s  %14s  %10.0f\n"
                depth
                engine
                (firstMicroseconds cell / 1000)
                (expressionsPerSecond cell)
                (humanBytes $ bytesPerExpression cell)
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

-- | Run one cell in a fresh process and read back its metrics.
runCell :: FilePath -> String -> Int -> IO Cell
runCell self engine depth = do
    output <- readProcess self [engine, show depth] ""
    case traverse readDouble $ splitOn ',' $ takeWhile (/= '\n') output of
        Just [first, rate, perExpr, setup, held, sum_] ->
            pure $ Cell first rate perExpr setup held sum_
        _ -> error $ "unreadable cell output: " <> show output

{- | Measure one generator at one depth and print the metrics as one CSV line.

The generator is bound lazily and shared, so building it happens inside the
first timed region and the steady-state region reuses it. That is how a
property run uses a generator, and it is what makes the first-expression and
steady-state numbers mean different things.

Every reading of an allocation or residency counter is taken immediately after
a major collection, because the RTS updates those at collections: without the
collection the last nursery block is unaccounted for, which at this sample
count is not a rounding error.
-}
child :: String -> Int -> IO ()
child engine depth = do
    performMajorGC
    baseline <- liveBytes
    let generator = generatorFor engine depth
    (firstElapsed, _) <- timed $ drawOne generator
    performMajorGC
    afterFirst <- liveBytes
    allocatedBefore <- allocatedBytes
    (steadyElapsed, total) <- timed $ drawMany tally generator sampleCount
    performMajorGC
    allocatedAfter <- allocatedBytes
    retained <- liveBytes
    -- One more draw, seeded from the run's own checksum. The dependency on
    -- `total` is what keeps the generator live across the collection above:
    -- without it this is the same expression as the first draw, the compiler
    -- shares the two, and the residency read is of a generator already
    -- collected -- which reads as a generator that retains nothing.
    lastDraw <- pure $! tally $ QCGen.unGen generator (QCRandom.mkQCGen total) 30
    putStrLn $
        intercalate "," $
            map
                show
                [ firstElapsed * 1e6
                , fromIntegral sampleCount / steadyElapsed
                , (allocatedAfter - allocatedBefore) / fromIntegral sampleCount
                , afterFirst - baseline
                , retained - baseline
                , fromIntegral (total + lastDraw)
                ]

-- | Draw one expression and force it.
drawOne :: QCGen.Gen TypedExpression -> IO Int
drawOne generator = pure $! tally $ QCGen.unGen generator rootSeed 30

{- | Draw a run of samples and fold them into a checksum.

The accumulator is strict, so every draw is forced inside the timed region
rather than left as a thunk for whoever reads the result.
-}
drawMany :: (a -> Int) -> QCGen.Gen a -> Int -> IO Int
drawMany measureOne generator count =
    pure $! fst $ foldl' step (0, rootSeed) [1 .. count]
  where
    step (!accumulator, generated) _ =
        let (drawn, next) = splitGen generated
         in (accumulator + measureOne (QCGen.unGen generator drawn 30), next)

-- | CPU seconds an action spent, with whatever it produced.
timed :: IO a -> IO (Double, a)
timed action = do
    start <- getCPUTime
    value <- action
    end <- getCPUTime
    pure (fromIntegral (end - start) / 1e12, value)

-- | Live bytes reported by the most recent collection.
liveBytes :: IO Double
liveBytes = fromIntegral . gcdetails_live_bytes . gc <$> getRTSStats

-- | Bytes allocated since the process started.
allocatedBytes :: IO Double
allocatedBytes = fromIntegral . allocated_bytes <$> getRTSStats

-- | Take the median of every metric independently across repeated runs.
median :: [Cell] -> Cell
median cells =
    Cell
        (middle firstMicroseconds)
        (middle expressionsPerSecond)
        (middle bytesPerExpression)
        (middle setupBytes)
        (middle retainedBytes)
        (middle checksum)
  where
    middle field = sort (map field cells) !! (length cells `div` 2)

-- | Render a byte count at whichever unit keeps it readable.
humanBytes :: Double -> String
humanBytes value
    | value >= 1024 * 1024 = printf "%.2f MB" (value / (1024 * 1024))
    | value >= 1024 = printf "%.1f KB" (value / 1024)
    | otherwise = printf "%.0f B" value

-- | Split on one separator, keeping empty fields.
splitOn :: Char -> String -> [String]
splitOn separator input = case break (== separator) input of
    (field, []) -> [field]
    (field, _ : rest) -> field : splitOn separator rest

-- | Read a double, or nothing if the field is not one.
readDouble :: String -> Maybe Double
readDouble input = case reads input of
    [(value, "")] -> Just value
    _ -> Nothing
