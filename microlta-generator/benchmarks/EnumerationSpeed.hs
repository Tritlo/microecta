{- | Compare term enumeration across the automaton layers.

Every row enumerates one language and reports CPU seconds and a checksum of
the term sizes. The FTA rows enumerate the plain explicit-state view of the
same ECTA node, converted before timing, so the rows differ only in the
enumerator. The LTA row decides its guards without a solver. Each repeat
uses a separately built language, so no result is shared between repeats.
-}
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (void)
import qualified Data.Text as Text
import qualified Data.Tree as Tree
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import Text.Printf (printf)

import Application.TermSearch.Dataset (typeToFta)
import Application.TermSearch.TermSearch (filterType, reduceFully)
import Application.TermSearch.Type (TypeSkeleton (..))
import Application.TermSearch.Utils (arrowType, constFunc, mkDatatype, theArrowNode, typeConst)
import Data.ECTA
import qualified Data.ECTA.FTA as ECTAFTA
import Data.ECTA.Paths
import Data.ECTA.Term (Symbol (Symbol))
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
import qualified Data.Tree.FTA as FTA

data Bench = Bench {benchName :: String, benchRepeats :: Int, benchPrepare :: Int -> IO (), benchAction :: Int -> IO Int}

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
    mapM_ benchPrepare [1 .. benchRepeats * multiplier]
    start <- getCPUTime
    checksum <- loop (benchRepeats * multiplier) 0
    end <- getCPUTime
    printf
        "%s,%.6f,%d,%d\n"
        benchName
        (fromIntegral (end - start) / (10 ^ (12 :: Int) :: Double) :: Double)
        (benchRepeats * multiplier)
        checksum
  where
    loop 0 !acc = return acc
    loop n !acc = do
        x <- benchAction n
        loop (n - 1 :: Int) (acc + x)

sizes :: [Tree.Tree a] -> IO Int
sizes = evaluate . sum . map (length . Tree.flatten)

-- | The plain FTA view of an ECTA with its constraints dropped.
plainView :: Node Symbol -> FTA.PlainFTA ECTAFTA.ECTAState Symbol
plainView node = either (error . show) void (ECTAFTA.toFTA node)

benchmarks :: [Bench]
benchmarks =
    [ fta "fta-terms/expressions-depth-3" 5 boundedExpressions FTA.terms
    , ecta "ecta-getAllTerms/expressions-depth-3" 5 boundedExpressions getAllTerms
    , fta "fta-terms/expressions-depth-2" 20 (unfoldBounded 3 . expressionsMu) FTA.terms
    , ecta "ecta-getAllTerms/expressions-depth-2" 20 (unfoldBounded 3 . expressionsMu) getAllTerms
    , fta "fta-terms/filter-maybe-int-size-2-take-64" 20 reducedFilter (take 64 . FTA.terms)
    , ecta "ecta-getAllTerms/filter-maybe-int-size-2-take-64" 20 reducedFilter (take 64 . getAllTerms)
    , fta "fta-terms/filter-list-int-size-3-all" 5 reducedListFilter FTA.terms
    , ecta "ecta-getAllTerms/filter-list-int-size-3-all" 5 reducedListFilter getAllTerms
    , fta "fta-terms/finite-choice" 200 finiteChoiceNode FTA.terms
    , ecta "ecta-getAllTerms/finite-choice" 200 finiteChoiceNode getAllTerms
    , Bench "lta-denotationAtMost/expressions-depth-2" 20 (\_ -> pure ()) (const $ ltaTerms 2)
    , Bench "lta-denotationAtMost/expressions-depth-3" 2 (\_ -> pure ()) (const $ ltaTerms 3)
    ]
  where
    -- The FTA rows enumerate the plain view of the same ECTA node, converted before timing.
    fta name repeats language enumerate =
        Bench
            name
            repeats
            (\i -> void (evaluate (length (FTA.states (plainView (language i))))))
            (\i -> sizes (enumerate (plainView (language i))))
    ecta name repeats language enumerate =
        Bench name repeats (\i -> void (evaluate (nodeCount (language i)))) (\i -> sizes (enumerate (language i)))

expressionsMu :: Int -> Node Symbol
expressionsMu salt = createMu $ \r ->
    Node
        [ Edge (named "zero" salt) []
        , Edge (named "one" salt) []
        , Edge (named "add" salt) [r, r]
        , Edge (named "mul" salt) [r, r]
        ]

boundedExpressions :: Int -> Node Symbol
boundedExpressions = unfoldBounded 4 . expressionsMu

reducedFilter :: Int -> Node Symbol
reducedFilter = reduceFully . filterMaybeIntSize2

reducedListFilter :: Int -> Node Symbol
reducedListFilter = reduceFully . filterListIntSize3

-- | The expression language as an unconstrained LTA; guards are decided without a solver.
ltaExpressions :: Automaton
ltaExpressions =
    either (error . show) id $
        mkAutomaton
            (State 0)
            [
                ( State 0
                , [transition "zero" [], transition "one" [], transition "add" [State 0, State 0], transition "mul" [State 0, State 0]]
                )
            ]
  where
    transition symbol children = FTA.Transition (LiquidSymbol symbol true) children unconstrainedConstraint

ltaTerms :: Int -> IO Int
ltaTerms depth = do
    result <- denotationAtMost (entailmentWithBindings (\_ _ _ -> pure Yes)) depth ltaExpressions
    either (error . show) sizes result

filterMaybeIntSize2 :: Int -> Node Symbol
filterMaybeIntSize2 i =
    filterType
        (monoTermsOfSize i 2)
        (typeToFta $ TCons "Maybe" [TCons "Int" []])

filterListIntSize3 :: Int -> Node Symbol
filterListIntSize3 i =
    filterType
        (monoTermsOfSize i 3)
        (typeToFta $ TCons "List" [TCons "Int" []])

monoTermsOfSize :: Int -> Int -> Node Symbol
monoTermsOfSize salt size = union (go size)
  where
    go 0 = []
    go 1 = [monoArgumentScope salt, monoFunctionScope salt]
    go n =
        [ appNode (union (go i)) (union (go (n - i)))
        | i <- [1 .. n - 1]
        ]

appNode :: Node Symbol -> Node Symbol -> Node Symbol
appNode f x =
    Node
        [ mkEdge
            "app"
            [getPath (path [0, 2]) f, theArrowNode, f, x]
            ( mkEqConstraints
                [ [path [1], path [2, 0, 0]]
                , [path [3, 0], path [2, 0, 1]]
                , [path [0], path [2, 0, 2]]
                ]
            )
        ]

monoArgumentScope :: Int -> Node Symbol
monoArgumentScope salt =
    Node
        [ constFunc (named "x" salt) (typeConst "Int")
        , constFunc (named "y" salt) (typeConst "Int")
        , constFunc (named "xs" salt) (mkDatatype "List" [typeConst "Int"])
        ]

monoFunctionScope :: Int -> Node Symbol
monoFunctionScope salt =
    Node
        [ constFunc (named "idInt" salt) (arrowType intType intType)
        , constFunc (named "JustInt" salt) (arrowType intType maybeIntType)
        , constFunc (named "headInt" salt) (arrowType listIntType intType)
        , constFunc (named "nilInt" salt) listIntType
        , constFunc (named "consInt" salt) (arrowType intType (arrowType listIntType listIntType))
        ]

named :: String -> Int -> Symbol
named prefix salt = Symbol $ Text.pack (prefix ++ show salt)

intType :: Node Symbol
intType = typeConst "Int"

maybeIntType :: Node Symbol
maybeIntType = mkDatatype "Maybe" [intType]

listIntType :: Node Symbol
listIntType = mkDatatype "List" [intType]

finiteChoiceNode :: Int -> Node Symbol
finiteChoiceNode salt =
    Node
        [ Edge (named "f" salt) [choiceAB salt, choiceAB salt]
        , Edge (named "g" salt) [choiceAB salt, choiceAB salt]
        ]

choiceAB :: Int -> Node Symbol
choiceAB salt = Node [Edge (named "a" salt) [], Edge (named "b" salt) []]
