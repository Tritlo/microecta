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
import Control.Monad ((>=>))
import Data.Functor.Identity (runIdentity)
import Data.List (elemIndex)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import Text.Printf (printf)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, noConstraint)
import qualified Data.CFTA.Enumeration as Enumeration
import qualified Data.CFTA.Interned as Common
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

data Bench = forall language. Bench
    { benchName :: String
    , benchRepeats :: Int
    , benchPrepare :: Int -> IO language
    -- ^ Build and force the language for one repeat.
    , benchAction :: language -> IO Int
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
    languages <- mapM benchPrepare [1 .. totalRepeats]
    start <- getCPUTime
    checksum <- loop languages 0
    end <- getCPUTime
    let seconds = fromIntegral (end - start) / (10 ^ (12 :: Int) :: Double)
    printf "%s,%.6f,%d,%d\n" benchName seconds totalRepeats checksum
  where
    totalRepeats = benchRepeats * multiplier

    loop [] !acc = return acc
    loop (language : rest) !acc = do
        x <- benchAction language
        loop rest (acc + x)

benchmarks :: [Bench]
benchmarks =
    [ explicit "terms/expressions-depth-3" 10 boundedExpressions FTA.terms
    , explicit "naive/expressions-depth-3" 10 boundedExpressions naiveTerms
    , interned "interned/expressions-depth-3" 10 internedBoundedExpressions Enumeration.plainTerms
    , explicit "terms/expressions-lazy-500k" 5 expressions $ take 500000 . FTA.terms
    , interned "interned/expressions-lazy-500k" 5 internedExpressions $ take 500000 . Enumeration.plainTerms
    , interned "interned/shared-pairs-lazy-500k" 5 sharedPairs $ take 500000 . Enumeration.plainTerms
    , -- Chains of depth n have n nodes, so this row counts terms instead of nodes.
      Bench "terms/naturals-500k" 5 (prepared (length . FTA.states) naturals) $
        evaluate . length . take 500000 . FTA.terms
    , explicit "termsUpToM-identity/expressions-depth-3" 10 expressions $ runIdentity . FTA.termsUpToM (\_ _ _ -> pure True) 3
    , Bench "termsUpToM-io/expressions-depth-3" 10 (prepared (length . FTA.states) expressions) $
        FTA.termsUpToM (\_ _ _ -> pure True) 3 >=> sizes
    , explicit "termsUpToM-ambiguous-identity/expressions-depth-3" 2 ambiguousExpressions $
        runIdentity . FTA.termsUpToM (\_ _ _ -> pure True) 3
    , explicit "termsUpToM-ambiguous-identity-text/expressions-depth-3" 2 textExpressions $
        runIdentity . FTA.termsUpToM (\_ _ _ -> pure True) 3
    , explicit "termsUpToM-ambiguous-identity-int/expressions-depth-3" 2 intExpressions $
        runIdentity . FTA.termsUpToM (\_ _ _ -> pure True) 3
    , explicit "terms-ambiguous/expressions-depth-3" 2 (FTA.boundDepth 3 . ambiguousExpressions) FTA.terms
    ]
  where
    explicit name repeats language enumerate =
        Bench name repeats (prepared (length . FTA.states) language) (sizes . enumerate)
    interned name repeats language enumerate =
        Bench name repeats (prepared Common.nodeCount language) (sizes . enumerate)
    prepared force build i = let built = build i in built <$ evaluate (force built)

sizes :: [Term a] -> IO Int
sizes = evaluate . sum . map (length . Term.flatten)

-- | Enumerate an acyclic automaton with a plain product per state.
naiveTerms :: (Ord state) => FTA.PlainFTA state symbol -> [Term symbol]
naiveTerms acyclic = table Map.! FTA.initialState acyclic
  where
    table = fmap fromRow (FTA.transitionTable acyclic)
    fromRow outgoing =
        [ Term.Node symbol children
        | FTA.Transition symbol childStates _ <- outgoing
        , children <- traverse (table Map.!) childStates
        ]

-- Each language takes a salt that is added to its symbols, so repeats use
-- distinct automata.

-- | Two literals, one unary and two binary constructors: 182,712 terms of depth at most 3.
expressions :: Int -> FTA.PlainFTA Int String
expressions salt = automaton 0 [(0, expressionAlternatives salt 0)]

expressionAlternatives :: Int -> Int -> [FTA.Transition Int String Constraint]
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

internedExpressions :: Int -> Common.Node String
internedExpressions salt =
    Common.createMu $ \r ->
        Common.Node
            [ Common.Edge (named salt "zero") []
            , Common.Edge (named salt "one") []
            , Common.Edge (named salt "neg") [r]
            , Common.Edge (named salt "add") [r, r]
            , Common.Edge (named salt "mul") [r, r]
            ]

internedBoundedExpressions :: Int -> Common.Node String
internedBoundedExpressions = Common.fromFTA . boundedExpressions

-- | Five levels of shared pairs over two leaves: 4,294,967,296 terms on six nodes.
sharedPairs :: Int -> Common.Node String
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

automaton :: Int -> [(Int, [FTA.Transition Int String Constraint])] -> FTA.PlainFTA Int String
automaton initial rows = either (error . show) id $ FTA.mkFTA initial rows

t :: String -> [Int] -> FTA.Transition Int String Constraint
t symbol children = FTA.Transition symbol children noConstraint
