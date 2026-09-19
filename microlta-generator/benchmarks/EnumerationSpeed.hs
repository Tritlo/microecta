{- | Compare term enumeration across the automaton layers.

Every row enumerates one language and reports CPU seconds and a checksum of
the term sizes. The FTA rows enumerate the plain explicit-state view of the
same ECTA node, so the rows differ only in the enumerator. The LTA rows
decide their guards without a solver. Each repeat uses a separately built
language, so no result is shared between repeats, and every language is
built before timing. Enumeration through equality constraints is measured by
@microecta:bench:micro-bench@.
-}
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (void)
import qualified Data.Text as Text
import qualified Data.Tree as Tree
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import Text.Printf (printf)

import qualified Data.CFTA as FTA
import Data.CFTA.Equality
import qualified Data.CFTA.Interned as Interned
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.LTA (
    Automaton,
    LiquidSymbol (LiquidSymbol),
    State (State),
    Verdict (Yes),
    denotationAtMost,
    entailmentWithBindings,
    mkAutomaton,
    unconstrainedConstraint,
 )
import Data.LTA.Refinement (true)

-- | One row: every repeat prepares its own language before timing starts.
data Bench = forall language. Bench
    { benchName :: String
    , benchRepeats :: Int
    , benchPrepare :: Int -> IO language
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
    languages <- mapM benchPrepare [1 .. benchRepeats * multiplier]
    start <- getCPUTime
    checksum <- loop languages 0
    end <- getCPUTime
    printf
        "%s,%.6f,%d,%d\n"
        benchName
        (fromIntegral (end - start) / (10 ^ (12 :: Int) :: Double) :: Double)
        (benchRepeats * multiplier)
        checksum
  where
    loop [] !acc = return acc
    loop (language : rest) !acc = do
        x <- benchAction language
        loop rest (acc + x)

sizes :: [Tree.Tree a] -> IO Int
sizes = evaluate . sum . map (length . Tree.flatten)

-- | The plain FTA view of an ECTA with its constraints dropped.
plainView :: Node Symbol EqConstraints -> FTA.PlainFTA Interned.InternedState Symbol
plainView node = either (error . show) void (Interned.toFTA node)

benchmarks :: [Bench]
benchmarks =
    [ fta "fta-terms/expressions-depth-3" 10 boundedExpressions FTA.terms
    , ecta "ecta-getAllTerms/expressions-depth-3" 10 boundedExpressions getAllTerms
    , Bench "lta-denotationAtMost/expressions-depth-3" 5 (\_ -> pure ()) (\() -> ltaTerms 3)
    , fta "fta-terms/expressions-depth-2" 10000 (unfoldBounded 3 . expressionsMu) FTA.terms
    , ecta "ecta-getAllTerms/expressions-depth-2" 10000 (unfoldBounded 3 . expressionsMu) getAllTerms
    , Bench "lta-denotationAtMost/expressions-depth-2" 10000 (\_ -> pure ()) (\() -> ltaTerms 2)
    , fta "fta-terms/finite-choice" 30000 finiteChoiceNode FTA.terms
    , ecta "ecta-getAllTerms/finite-choice" 30000 finiteChoiceNode getAllTerms
    ]
  where
    fta name repeats language = prepared name repeats (plainView . language) (length . FTA.states)
    ecta name repeats language = prepared name repeats language nodeCount
    prepared name repeats build force enumerate =
        Bench name repeats (\i -> let built = build i in built <$ evaluate (force built)) (sizes . enumerate)

expressionsMu :: Int -> Node Symbol EqConstraints
expressionsMu salt = createMu $ \r ->
    Node
        [ Edge (named "zero" salt) []
        , Edge (named "one" salt) []
        , Edge (named "neg" salt) [r]
        , Edge (named "add" salt) [r, r]
        , Edge (named "mul" salt) [r, r]
        ]

boundedExpressions :: Int -> Node Symbol EqConstraints
boundedExpressions = unfoldBounded 4 . expressionsMu

-- | The expression language as an unconstrained LTA; guards are decided without a solver.
ltaExpressions :: Automaton
ltaExpressions =
    either (error . show) id $
        mkAutomaton
            (State 0)
            [
                ( State 0
                ,
                    [ transition "zero" []
                    , transition "one" []
                    , transition "neg" [State 0]
                    , transition "add" [State 0, State 0]
                    , transition "mul" [State 0, State 0]
                    ]
                )
            ]
  where
    transition symbol children = FTA.Transition (LiquidSymbol symbol true) children unconstrainedConstraint

ltaTerms :: Int -> IO Int
ltaTerms depth = do
    result <- denotationAtMost (entailmentWithBindings (\_ _ _ -> pure Yes)) depth ltaExpressions
    either (error . show) sizes result

named :: String -> Int -> Symbol
named prefix salt = Symbol $ Text.pack (prefix ++ show salt)

-- | Two levels of binary choice over two leaves: 128 terms on five nodes.
finiteChoiceNode :: Int -> Node Symbol EqConstraints
finiteChoiceNode salt =
    Node
        [ Edge (named "f" salt) [pairs, pairs]
        , Edge (named "g" salt) [pairs, pairs]
        ]
  where
    pairs =
        Node
            [ Edge (named "c" salt) [choiceAB salt, choiceAB salt]
            , Edge (named "d" salt) [choiceAB salt, choiceAB salt]
            ]

choiceAB :: Int -> Node Symbol EqConstraints
choiceAB salt = Node [Edge (named "a" salt) [], Edge (named "b" salt) []]
