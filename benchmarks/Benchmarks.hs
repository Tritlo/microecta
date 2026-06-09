{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (evaluate)
import qualified Data.Text as Text
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import Text.Printf (printf)

import Application.TermSearch.Dataset (typeToFta)
import Application.TermSearch.TermSearch (filterType, reduceFully)
import Application.TermSearch.Type (TypeSkeleton (..))
import Application.TermSearch.Utils (
    arrowType,
    constFunc,
    mkDatatype,
    theArrowNode,
    typeConst,
 )
import Data.ECTA
import Data.ECTA.Internal.ECTA.Operations (reduceEqConstraints)
import Data.ECTA.Paths
import Data.ECTA.Term (Symbol (Symbol))

data Bench = Bench
    { benchName :: String
    , benchRepeats :: Int
    , benchAction :: Int -> IO Int
    }

main :: IO ()
main = do
    multiplier <- parseMultiplier <$> getArgs
    putStrLn "benchmark,cpu_seconds,repeats,checksum"
    mapM_ (runBench multiplier) benchmarks

parseMultiplier :: [String] -> Int
parseMultiplier [] = 1
parseMultiplier (x : _) =
    case reads x of
        [(n, "")] -> max 1 n
        _ -> 1

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
        x <- benchAction n
        loop (n - 1) (acc + x)

benchmarks :: [Bench]
benchmarks =
    [ Bench "getPath/type-search-node" 2000 $ \i ->
        forceNode $ getPath (path [2, 0, if i >= 0 then 2 else 1]) typeSearchNode
    , Bench "mkEqConstraints/congruence" 600 $ \i ->
        forceEqConstraints $ mkEqConstraints (congruencePathSets i)
    , Bench "eqConstraintsDescend/wide-sparse" 4000 $ \i ->
        forceEqConstraints $ eqConstraintsDescend wideSparseConstraints (i `rem` 16)
    , Bench "intersect/finite-constrained" 800 $ \i ->
        forceNode $ finiteChoiceNode i `intersect` constrainedChoiceNode i
    , Bench "intersect/recursive-types" 300 $ \i ->
        forceNode $ recursiveTypeA i `intersect` recursiveTypeB i
    , Bench "reduce/recursive-paths" 120 $ \i ->
        forceNodes $ reduceEqConstraints recursivePathConstraints EmptyConstraints (recursivePathNodes i)
    , Bench "reduce/filter-maybe-int-size-2" 80 $ \i ->
        forceNode $ reduceFully (filterMaybeIntSize2 i)
    , Bench "reduce/filter-list-int-size-3" 20 $ \i ->
        forceNode $ reduceFully (filterListIntSize3 i)
    , Bench "enumerate/reduced-filter-maybe-int-size-2" 80 $ \i ->
        forceInt $ length (take 64 (getAllTerms (reduceFully (filterMaybeIntSize2 i))))
    ]

forceNode :: Node -> IO Int
forceNode n = forceInt (nodeCount n + edgeCount n)

forceNodes :: [Node] -> IO Int
forceNodes = forceInt . sum . map (\n -> nodeCount n + edgeCount n)

forceEqConstraints :: EqConstraints -> IO Int
forceEqConstraints =
    forceInt
        . sum
        . map (sum . map (length . unPath) . unPathEClass)
        . unsafeGetEclasses

forceInt :: Int -> IO Int
forceInt = evaluate

typeSearchNode :: Node
typeSearchNode =
    appNode
        (appNode (monoFunctionScope 0) (monoArgumentScope 0))
        (monoTermsOfSize 0 2)

filterMaybeIntSize2 :: Int -> Node
filterMaybeIntSize2 i =
    filterType
        (monoTermsOfSize i 2)
        (typeToFta $ TCons "Maybe" [TCons "Int" []])

filterListIntSize3 :: Int -> Node
filterListIntSize3 i =
    filterType
        (monoTermsOfSize i 3)
        (typeToFta $ TCons "List" [TCons "Int" []])

monoTermsOfSize :: Int -> Int -> Node
monoTermsOfSize salt size = union (go size)
  where
    go 0 = []
    go 1 = [monoArgumentScope salt, monoFunctionScope salt]
    go n =
        [ appNode (union (go i)) (union (go (n - i)))
        | i <- [1 .. n - 1]
        ]

appNode :: Node -> Node -> Node
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

monoArgumentScope :: Int -> Node
monoArgumentScope salt =
    Node
        [ constFunc (named "x" salt) (typeConst "Int")
        , constFunc (named "y" salt) (typeConst "Int")
        , constFunc (named "xs" salt) (mkDatatype "List" [typeConst "Int"])
        ]

monoFunctionScope :: Int -> Node
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

intType :: Node
intType = typeConst "Int"

maybeIntType :: Node
maybeIntType = mkDatatype "Maybe" [intType]

listIntType :: Node
listIntType = mkDatatype "List" [intType]

congruencePathSets :: Int -> [[Path]]
congruencePathSets salt =
    [ [path [i], path [i + 1]]
    | i <- [base .. base + 5]
    ]
        ++ [ [path [i, 0], path [i, 1]]
           | i <- [base .. base + 5]
           ]
  where
    base = salt `rem` 3

wideSparseConstraints :: EqConstraints
wideSparseConstraints =
    mkEqConstraints
        [ [path [i, 0], path [i, 1]]
        | i <- [0 .. 15]
        ]

finiteChoiceNode :: Int -> Node
finiteChoiceNode salt =
    Node
        [ Edge (named "f" salt) [choiceAB salt, choiceAB salt]
        , Edge (named "g" salt) [choiceAB salt, choiceAB salt]
        ]

constrainedChoiceNode :: Int -> Node
constrainedChoiceNode salt =
    Node
        [ mkEdge (named "f" salt) [choiceAB salt, choiceAB salt] (mkEqConstraints [[path [0], path [1]]])
        , Edge (named "g" salt) [choiceAB salt, choiceAB salt]
        ]

choiceAB :: Int -> Node
choiceAB salt = Node [Edge (named "a" salt) [], Edge (named "b" salt) []]

recursivePathConstraints :: EqConstraints
recursivePathConstraints = mkEqConstraints [[path [0, 0, 0, 0], path [1, 0, 0]]]

recursivePathNodes :: Int -> [Node]
recursivePathNodes salt = [infiniteFNode salt, infiniteFNode salt]

infiniteFNode :: Int -> Node
infiniteFNode salt = createMu $ \r -> Node [Edge (named "f" salt) [r]]

recursiveTypeA :: Int -> Node
recursiveTypeA salt =
    createMu $ \r ->
        Node
            [ Edge (named "baseType" salt) []
            , Edge "->" [theArrowNode, r, r]
            , Edge "Maybe" [r]
            , Edge "List" [r]
            ]

recursiveTypeB :: Int -> Node
recursiveTypeB salt =
    createMu $ \r ->
        Node
            [ Edge (named "baseType" salt) []
            , Edge "->" [theArrowNode, mkDatatype "List" [r], r]
            , Edge "List" [r]
            ]
