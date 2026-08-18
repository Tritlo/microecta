{- | Sampling throughput of transparent generators against a handwritten
QuickCheck baseline.

Both generators draw uniformly from the same exact-depth well-typed
expression language, so the comparison is like for like: the ECTA generator
lowers to a compiled rank decoder and draws once per sample, while the
handwritten one walks nested 'QC.frequency' choices with the same exact
weights and draws once per node.

Two reference rows come first, because they set what the rest can mean: an
empty generator measures the loop itself, and a single 'QC.chooseInt'
measures one QuickCheck draw. A generator costing one draw cannot beat the
second row, so the ECTA-to-handwritten ratio moves with the cost of a draw
in the QuickCheck and random versions in use — compare the columns across
engine changes on one machine, not against ratios recorded elsewhere.

Each run prints a result-type checksum. It is a smoke check over the sampled
stream, not a proof that the complete language or rank order is unchanged. The
artifact's independent exhaustive verifier checks language equality.
-}
module Main (main) where

import System.CPUTime (getCPUTime)
import System.Random (splitGen)
import Text.Printf (printf)

import qualified Test.QuickCheck.Gen as QC
import qualified Test.QuickCheck.Random as QC

import qualified Data.ECTA.Gen.QuickCheck as ECTAGen
import Data.ECTA.TypedExpressionLanguage (
    TypedExpression (expressionType),
    expressionGenAtDepth,
    handwrittenExpressionGen,
 )

-- | Samples drawn per generator per row.
sampleCount :: Int
sampleCount = 1000000

-- | Depths compared, one row of results each.
depths :: [Int]
depths = [1 .. 4]

main :: IO ()
main = do
    reference "empty generator" $ pure 0
    reference "one chooseInt" $ QC.chooseInt (0, 99)
    printf "\n%5s  %14s  %14s  %8s  %21s\n" "depth" "ecta/s" "handwritten/s" "ratio" "checksum"
    mapM_ row depths
  where
    reference label generator = do
        (rate, _) <- measure id generator
        printf "%-20s %14.0f /s\n" label rate

    row depth = do
        (ectaRate, ectaChecksum) <-
            measure tally $ ECTAGen.toGen $ expressionGenAtDepth depth
        (handRate, handChecksum) <-
            measure tally $ handwrittenExpressionGen depth
        printf
            "%5d  %14.0f  %14.0f  %7.2fx  %10d %10d\n"
            depth
            ectaRate
            handRate
            (ectaRate / handRate)
            ectaChecksum
            handChecksum

    -- Every field of a sampled expression is strict, so forcing the result
    -- type has already forced the whole tree: the fold measures generation
    -- rather than adding a second traversal.
    tally = fromEnum . expressionType

{- | Draw 'sampleCount' values and report samples per second with a checksum.

The checksum folds every sample, so no draw is left unevaluated. The generator
value is supplied once, but first-use lowering or decoder compilation may occur
after the timer starts. One million draws amortize that setup; the benchmark
does not report it separately.
-}
measure :: (a -> Int) -> QC.Gen a -> IO (Double, Int)
measure tally generator = do
    start <- getCPUTime
    let checksum = fst $ foldl' step (0, root) [1 .. sampleCount]
    end <- checksum `seq` getCPUTime
    let seconds = fromIntegral (end - start) / (1e12 :: Double)
    pure (fromIntegral sampleCount / seconds, checksum)
  where
    -- One fixed root seed, split per draw the way QuickCheck drives a
    -- property: deterministic across runs and cheap next to a draw.
    root = QC.mkQCGen 20260811

    step (accumulator, generated) _ =
        let (drawn, next) = splitGen generated
         in (accumulator + tally (QC.unGen generator drawn 30), next)
