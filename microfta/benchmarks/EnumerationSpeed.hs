{- | Measure term enumeration on ordinary automata.

Each row enumerates one language and reports CPU seconds and a checksum of
the term sizes. The naive rows enumerate an acyclic automaton with a plain
per-state product, as a baseline for 'FTA.terms' on finite languages.
-}
module Main (main) where

import Control.Exception (evaluate)
import qualified Data.Map.Strict as Map
import qualified Data.Tree as Tree
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import Text.Printf (printf)

import qualified Data.Tree.FTA as FTA
import qualified Data.Tree.FTA.Interned as Common

data Bench = Bench
    { benchName :: String
    , benchRepeats :: Int
    , benchAction :: IO Int
    }

main :: IO ()
main = do
    multiplier <- parseMultiplier <$> getArgs
    putStrLn "benchmark,cpu_seconds,repeats,checksum"
    mapM_ (runBench multiplier) benchmarks

parseMultiplier :: [String] -> Int
parseMultiplier (x : _) | [(n, "")] <- reads x = max 1 n
parseMultiplier _ = 1

runBench :: Int -> Bench -> IO ()
runBench multiplier Bench{benchName, benchRepeats, benchAction} = do
    start <- getCPUTime
    checksum <- loop totalRepeats 0
    end <- getCPUTime
    let seconds = fromIntegral (end - start) / (10 ^ (12 :: Int) :: Double)
    printf "%s,%.6f,%d,%d\n" benchName seconds totalRepeats checksum
  where
    totalRepeats = benchRepeats * multiplier

    loop 0 !acc = return acc
    loop n !acc = do
        x <- benchAction
        loop (n - 1) (acc + x)

benchmarks :: [Bench]
benchmarks =
    [ Bench "terms/expressions-depth-3" 10 $ sizes $ FTA.terms boundedExpressions
    , Bench "naive/expressions-depth-3" 10 $ sizes $ naiveTerms boundedExpressions
    , Bench "interned/expressions-depth-3" 10 $ sizes $ Common.terms internedBoundedExpressions
    , Bench "terms/expressions-lazy-100k" 10 $ sizes $ take 100000 $ FTA.terms expressions
    , Bench "interned/expressions-lazy-100k" 10 $ sizes $ take 100000 $ Common.terms internedExpressions
    , Bench "interned/shared-pairs-lazy-100k" 10 $ sizes $ take 100000 $ Common.terms sharedPairs
    , Bench "terms/naturals-1000" 10 $ sizes $ take 1000 $ FTA.terms naturals
    ]
  where
    sizes = evaluate . sum . map (length . Tree.flatten)

-- | Enumerate an acyclic automaton with a plain product per state.
naiveTerms :: (Ord state) => FTA.PlainFTA state symbol -> [Tree.Tree symbol]
naiveTerms acyclic = table Map.! FTA.initialState acyclic
  where
    table = fmap fromRow (FTA.transitionTable acyclic)
    fromRow outgoing =
        [ Tree.Node symbol children
        | FTA.Transition symbol childStates () <- outgoing
        , children <- traverse (table Map.!) childStates
        ]

-- | Two literals and two binary constructors: 32,768 terms at depth 3.
expressions :: FTA.PlainFTA Int String
expressions = automaton 0 [(0, [t "zero" [], t "one" [], t "add" [0, 0], t "mul" [0, 0]])]

boundedExpressions :: FTA.PlainFTA Int String
boundedExpressions = FTA.boundDepth 3 expressions

naturals :: FTA.PlainFTA Int String
naturals = automaton 0 [(0, [t "zero" [], t "succ" [0]])]

internedExpressions :: Common.PlainNode String
internedExpressions =
    Common.createMu $ \r -> Common.Node [Common.Edge "zero" [], Common.Edge "one" [], Common.Edge "add" [r, r], Common.Edge "mul" [r, r]]

internedBoundedExpressions :: Common.PlainNode String
internedBoundedExpressions = either (error . show) id $ Common.fromFTA boundedExpressions

-- | Four levels of shared pairs over two leaves: 4,294,967,296 terms on six nodes.
sharedPairs :: Common.PlainNode String
sharedPairs = iterate (\child -> Common.Node [Common.Edge "pair" [child, child]]) leaves !! 4
  where
    leaves = Common.Node [Common.Edge "zero" [], Common.Edge "one" []]

automaton :: Int -> [(Int, [FTA.Transition Int String ()])] -> FTA.PlainFTA Int String
automaton initial rows = either (error . show) id $ FTA.mkFTA initial rows

t :: String -> [Int] -> FTA.Transition Int String ()
t symbol children = FTA.Transition symbol children ()
