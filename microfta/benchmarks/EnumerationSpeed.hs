{- | Measure term enumeration on ordinary automata.

Each row enumerates one language and reports CPU seconds and a checksum of
the term sizes. Every repeat enumerates a separately built automaton, so no
result is shared between repeats; the automata are built before timing. The
naive rows enumerate an acyclic automaton with a plain per-state product, as
a baseline for 'FTA.terms' on finite languages.
-}
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (void)
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
    , benchPrepare :: Int -> IO ()
    -- ^ Build and force the language for one repeat.
    , benchAction :: Int -> IO Int
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
runBench multiplier Bench{benchName, benchRepeats, benchPrepare, benchAction} = do
    mapM_ benchPrepare [1 .. totalRepeats]
    start <- getCPUTime
    checksum <- loop totalRepeats 0
    end <- getCPUTime
    let seconds = fromIntegral (end - start) / (10 ^ (12 :: Int) :: Double)
    printf "%s,%.6f,%d,%d\n" benchName seconds totalRepeats checksum
  where
    totalRepeats = benchRepeats * multiplier

    loop 0 !acc = return acc
    loop n !acc = do
        x <- benchAction n
        loop (n - 1) (acc + x)

benchmarks :: [Bench]
benchmarks =
    [ explicit "terms/expressions-depth-3" boundedExpressions FTA.terms
    , explicit "naive/expressions-depth-3" boundedExpressions naiveTerms
    , interned "interned/expressions-depth-3" internedBoundedExpressions Common.terms
    , explicit "terms/expressions-lazy-100k" expressions $ take 100000 . FTA.terms
    , interned "interned/expressions-lazy-100k" internedExpressions $ take 100000 . Common.terms
    , interned "interned/shared-pairs-lazy-100k" sharedPairs $ take 100000 . Common.terms
    , explicit "terms/naturals-1000" naturals $ take 1000 . FTA.terms
    ]
  where
    explicit name language enumerate =
        Bench name 10 (void . evaluate . length . FTA.states . language) (sizes . enumerate . language)
    interned name language enumerate =
        Bench name 10 (void . evaluate . Common.nodeCount . language) (sizes . enumerate . language)
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

-- Each language takes a salt that is added to its symbols, so repeats use
-- distinct automata.

-- | Two literals and two binary constructors: 32,768 terms at depth 3.
expressions :: Int -> FTA.PlainFTA Int String
expressions salt = automaton 0 [(0, [t (named "zero") [], t (named "one") [], t (named "add") [0, 0], t (named "mul") [0, 0]])]
  where
    named symbol = symbol ++ show salt

boundedExpressions :: Int -> FTA.PlainFTA Int String
boundedExpressions = FTA.boundDepth 3 . expressions

naturals :: Int -> FTA.PlainFTA Int String
naturals salt = automaton 0 [(0, [t ("zero" ++ show salt) [], t ("succ" ++ show salt) [0]])]

internedExpressions :: Int -> Common.PlainNode String
internedExpressions salt =
    Common.createMu $ \r ->
        Common.Node
            [ Common.Edge (named "zero") []
            , Common.Edge (named "one") []
            , Common.Edge (named "add") [r, r]
            , Common.Edge (named "mul") [r, r]
            ]
  where
    named symbol = symbol ++ show salt

internedBoundedExpressions :: Int -> Common.PlainNode String
internedBoundedExpressions = either (error . show) id . Common.fromFTA . boundedExpressions

-- | Four levels of shared pairs over two leaves: 4,294,967,296 terms on six nodes.
sharedPairs :: Int -> Common.PlainNode String
sharedPairs salt = iterate (\child -> Common.Node [Common.Edge ("pair" ++ show salt) [child, child]]) leaves !! 4
  where
    leaves = Common.Node [Common.Edge ("zero" ++ show salt) [], Common.Edge ("one" ++ show salt) []]

automaton :: Int -> [(Int, [FTA.Transition Int String ()])] -> FTA.PlainFTA Int String
automaton initial rows = either (error . show) id $ FTA.mkFTA initial rows

t :: String -> [Int] -> FTA.Transition Int String ()
t symbol children = FTA.Transition symbol children ()
