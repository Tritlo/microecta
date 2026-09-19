{- | Measure term enumeration on ordinary automata.

Each row enumerates one language and reports CPU seconds and a checksum of
the term sizes. Every repeat enumerates a separately built automaton, so no
result is shared between repeats; the automata are built before timing. The
naive rows enumerate an acyclic automaton with a plain per-state product, as
a baseline for 'FTA.terms' on finite languages. Repeat counts keep every row
in the hundreds of milliseconds, above the noise of a shared machine.
-}
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (void)
import Data.Functor.Identity (runIdentity)
import Data.List (elemIndex)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Tree as Tree
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import Text.Printf (printf)

import qualified Data.CFTA as FTA
import qualified Data.CFTA.Enumeration as Enumeration
import qualified Data.CFTA.Interned as Common

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
    [ explicit "terms/expressions-depth-3" 10 boundedExpressions FTA.terms
    , explicit "naive/expressions-depth-3" 10 boundedExpressions naiveTerms
    , interned "interned/expressions-depth-3" 10 internedBoundedExpressions Enumeration.plainTerms
    , explicit "terms/expressions-lazy-500k" 5 expressions $ take 500000 . FTA.terms
    , interned "interned/expressions-lazy-500k" 5 internedExpressions $ take 500000 . Enumeration.plainTerms
    , interned "interned/shared-pairs-lazy-500k" 5 sharedPairs $ take 500000 . Enumeration.plainTerms
    , -- Chains of depth n have n nodes, so this row counts terms instead of nodes.
      Bench "terms/naturals-500k" 5 (void . evaluate . length . FTA.states . naturals) $
        evaluate . length . take 500000 . FTA.terms . naturals
    , explicit "termsUpToM-identity/expressions-depth-3" 10 expressions $ runIdentity . FTA.termsUpToM (\_ _ _ -> pure True) 3
    , Bench "termsUpToM-io/expressions-depth-3" 10 (void . evaluate . length . FTA.states . expressions) $ \i ->
        FTA.termsUpToM (\_ _ _ -> pure True) 3 (expressions i) >>= sizes
    , explicit "termsUpToM-ambiguous-identity/expressions-depth-3" 2 ambiguousExpressions $
        runIdentity . FTA.termsUpToM (\_ _ _ -> pure True) 3
    , Bench
        "termsUpToM-ambiguous-identity-text/expressions-depth-3"
        2
        (void . evaluate . length . FTA.states . textExpressions)
        $ sizes . runIdentity . FTA.termsUpToM (\_ _ _ -> pure True) 3 . textExpressions
    , Bench "termsUpToM-ambiguous-identity-int/expressions-depth-3" 2 (void . evaluate . length . FTA.states . intExpressions) $
        sizes . runIdentity . FTA.termsUpToM (\_ _ _ -> pure True) 3 . intExpressions
    , explicit "terms-ambiguous/expressions-depth-3" 2 (FTA.boundDepth 3 . ambiguousExpressions) FTA.terms
    ]
  where
    explicit name repeats language enumerate =
        Bench name repeats (void . evaluate . length . FTA.states . language) (sizes . enumerate . language)
    interned name repeats language enumerate =
        Bench name repeats (void . evaluate . Common.nodeCount . language) (sizes . enumerate . language)

sizes :: [Tree.Tree a] -> IO Int
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

-- | Two literals, one unary and two binary constructors: 182,710 terms at depth 3.
expressions :: Int -> FTA.PlainFTA Int String
expressions salt = automaton 0 [(0, expressionAlternatives salt 0)]

expressionAlternatives :: Int -> Int -> [FTA.Transition Int String ()]
expressionAlternatives salt state =
    [ t (named salt "zero") []
    , t (named salt "one") []
    , t (named salt "neg") [state]
    , t (named salt "add") [state, state]
    , t (named salt "mul") [state, state]
    ]

boundedExpressions :: Int -> FTA.PlainFTA Int String
boundedExpressions = FTA.boundDepth 3 . expressions

naturals :: Int -> FTA.PlainFTA Int String
naturals salt = automaton 0 [(0, [t (named salt "zero") [], t (named salt "succ") [0]])]

internedExpressions :: Int -> Common.PlainNode String
internedExpressions salt =
    Common.createMu $ \r ->
        Common.Node
            [ Common.Edge (named salt "zero") []
            , Common.Edge (named salt "one") []
            , Common.Edge (named salt "neg") [r]
            , Common.Edge (named salt "add") [r, r]
            , Common.Edge (named salt "mul") [r, r]
            ]

internedBoundedExpressions :: Int -> Common.PlainNode String
internedBoundedExpressions = either (error . show) id . Common.fromFTA . boundedExpressions

-- | Five levels of shared pairs over two leaves: 4,294,967,296 terms on seven nodes.
sharedPairs :: Int -> Common.PlainNode String
sharedPairs salt = iterate (\child -> Common.Node [Common.Edge (named salt "pair") [child, child]]) leaves !! 5
  where
    leaves = Common.Node [Common.Edge (named salt "zero") [], Common.Edge (named salt "one") []]

{- | The expression grammar with a second "add" alternative over a state whose
language is contained in the first, so every level has duplicate candidates
and the enumeration must deduplicate.
-}
ambiguousExpressions :: Int -> FTA.PlainFTA Int String
ambiguousExpressions salt =
    automaton
        0
        [ (0, expressionAlternatives salt 0 ++ [t (named salt "add") [1, 1]])
        , (1, [t (named salt "zero") [], t (named salt "one") []])
        ]

-- | The ambiguous grammar over 'Text' symbols, as the constraint packages use.
textExpressions :: Int -> FTA.PlainFTA Int Text
textExpressions = either (error . show) id . FTA.mapSymbols Text.pack . ambiguousExpressions

-- | The ambiguous grammar over 'Int' symbols, which compare like interned symbols.
intExpressions :: Int -> FTA.PlainFTA Int Int
intExpressions salt = either (error . show) id $ FTA.mapSymbols code (ambiguousExpressions 0)
  where
    code symbol = salt * 8 + fromMaybe 0 (elemIndex (takeWhile (/= '0') symbol) ["zero", "one", "neg", "add", "mul"])

named :: Int -> String -> String
named salt symbol = symbol ++ show salt

automaton :: Int -> [(Int, [FTA.Transition Int String ()])] -> FTA.PlainFTA Int String
automaton initial rows = either (error . show) id $ FTA.mkFTA initial rows

t :: String -> [Int] -> FTA.Transition Int String ()
t symbol children = FTA.Transition symbol children ()
