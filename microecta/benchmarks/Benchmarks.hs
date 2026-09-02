{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (evaluate)
import Data.Function (on)
import Data.List (sortBy)
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
import Data.ECTA.Internal.Paths (PathTrie (..))
import Data.ECTA.Paths
import Data.ECTA.Term (Symbol (Symbol))

data Bench = Bench
    { benchName :: String
    , benchRepeats :: Int
    , benchAction :: Int -> IO Int
    }

main :: IO ()
main = do
    preparePathOrderInputs
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
    , Bench "sort/path-eclasses/legacy-trie/small" 120 $ \i ->
        forcePathEClasses $
            sortBy (legacyComparePathTrie `on` getPathTrie) (selectPathOrderInput smallPathOrderInputs i)
    , Bench "sort/path-eclasses/trie/small" 120 $ \i ->
        forcePathEClasses $
            sortBy (compare `on` getPathTrie) (selectPathOrderInput smallPathOrderInputs i)
    , Bench "sort/path-eclasses/cached/small" 120 $ \i ->
        forcePathEClasses $
            sortBy compare (selectPathOrderInput smallPathOrderInputs i)
    , Bench "sort/path-eclasses/legacy-trie/shared-prefix" 40 $ \i ->
        forcePathEClasses $
            sortBy (legacyComparePathTrie `on` getPathTrie) (selectPathOrderInput sharedPrefixPathOrderInputs i)
    , Bench "sort/path-eclasses/trie/shared-prefix" 40 $ \i ->
        forcePathEClasses $
            sortBy (compare `on` getPathTrie) (selectPathOrderInput sharedPrefixPathOrderInputs i)
    , Bench "sort/path-eclasses/cached/shared-prefix" 40 $ \i ->
        forcePathEClasses $
            sortBy compare (selectPathOrderInput sharedPrefixPathOrderInputs i)
    , Bench "sort/path-eclasses/legacy-trie/divergent-branch" 120 $ \i ->
        forcePathEClasses $
            sortBy (legacyComparePathTrie `on` getPathTrie) (selectPathOrderInput divergentBranchPathOrderInputs i)
    , Bench "sort/path-eclasses/trie/divergent-branch" 120 $ \i ->
        forcePathEClasses $
            sortBy (compare `on` getPathTrie) (selectPathOrderInput divergentBranchPathOrderInputs i)
    , Bench "sort/path-eclasses/cached/divergent-branch" 120 $ \i ->
        forcePathEClasses $
            sortBy compare (selectPathOrderInput divergentBranchPathOrderInputs i)
    ]

forceNode :: Node Symbol -> IO Int
forceNode n = forceInt (nodeCount n + edgeCount n)

forceNodes :: [Node Symbol] -> IO Int
forceNodes = forceInt . sum . map (\n -> nodeCount n + edgeCount n)

forceEqConstraints :: EqConstraints -> IO Int
forceEqConstraints =
    forceInt
        . sum
        . map (sum . map (length . unPath) . unPathEClass)
        . unsafeGetEclasses

-- | Force a sorted equality-class result through its cached path lists.
forcePathEClasses :: [PathEClass] -> IO Int
forcePathEClasses =
    forceInt
        . foldl' (\acc pec -> acc * 33 + pathEClassFingerprint (unPathEClass pec)) 5381
  where
    pathEClassFingerprint =
        foldl' (\acc p -> acc * 33 + foldl' (\n i -> n * 33 + i) 5381 (unPath p)) 5381

forceInt :: Int -> IO Int
forceInt = evaluate

-- | Force both views before timing so the benchmark measures comparison.
preparePathOrderInputs :: IO ()
preparePathOrderInputs = do
    mapM_ forcePathEClasses allInputs
    mapM_ forcePathTries allInputs
  where
    allInputs =
        smallPathOrderInputs
            ++ sharedPrefixPathOrderInputs
            ++ divergentBranchPathOrderInputs

    forcePathTries =
        forceInt
            . sum
            . map (sum . map (sum . unPath) . fromPathTrie . getPathTrie)

-- | Select one of several deterministic input permutations.
selectPathOrderInput :: [[PathEClass]] -> Int -> [PathEClass]
selectPathOrderInput inputs salt = inputs !! (salt `rem` length inputs)

-- | Small equality classes with one common leading path.
smallPathOrderInputs :: [[PathEClass]]
smallPathOrderInputs = pathOrderInputs smallPathSets
  where
    smallPathSets =
        [ [ path [0, 0, 0]
          , path [1, n `div` 32, n `rem` 32]
          , path [2, n `rem` 17, n `div` 17]
          ]
        | n <- [0 .. 255]
        ]

-- | Larger equality classes whose comparisons share sixteen paths.
sharedPrefixPathOrderInputs :: [[PathEClass]]
sharedPrefixPathOrderInputs = pathOrderInputs sharedPrefixPathSets
  where
    sharedPrefixPathSets =
        [ [path [0, k, 0, 0] | k <- [0 .. 15]]
            ++ [path [1, n `div` 16, n `rem` 16, 0]]
        | n <- [0 .. 127]
        ]

-- | Equality classes containing the branching shape misordered by the legacy comparator.
divergentBranchPathOrderInputs :: [[PathEClass]]
divergentBranchPathOrderInputs = pathOrderInputs divergentBranchPathSets
  where
    divergentBranchPathSets =
        concat
            [ [ [path [0, k], path [0, k + 1]]
              , [path [0, k], path [1, k]]
              ]
            | k <- [1, 3 .. 255]
            ]

-- | Build and deterministically permute equality classes outside timed work.
pathOrderInputs :: [[Path]] -> [[PathEClass]]
pathOrderInputs pathSets =
    [ map snd $
        sortBy (compare `on` fst) $
            [ ((index * 73 + salt * 37) `rem` 257, pec)
            | (index, pec) <- zip [(0 :: Int) ..] corpus
            ]
    | salt <- [0 .. 7]
    ]
  where
    corpus = concatMap (unsafeGetEclasses . mkEqConstraints . (: [])) pathSets

-- | The direct trie comparator used before 12c32b2. It is intentionally wrong.
legacyComparePathTrie :: PathTrie -> PathTrie -> Ordering
legacyComparePathTrie EmptyPathTrie EmptyPathTrie = EQ
legacyComparePathTrie EmptyPathTrie _ = LT
legacyComparePathTrie _ EmptyPathTrie = GT
legacyComparePathTrie TerminalPathTrie TerminalPathTrie = EQ
legacyComparePathTrie TerminalPathTrie _ = LT
legacyComparePathTrie _ TerminalPathTrie = GT
legacyComparePathTrie (PathTrieSingleChild i1 pt1) (PathTrieSingleChild i2 pt2) =
    case compare i1 i2 of
        EQ -> legacyComparePathTrie pt1 pt2
        result -> result
legacyComparePathTrie (PathTrieSingleChild i1 pt1) (PathTrie ((i2, pt2) : _)) =
    case compare i1 i2 of
        EQ -> case legacyComparePathTrie pt1 pt2 of
            EQ -> LT
            result -> result
        result -> result
legacyComparePathTrie (PathTrieSingleChild _ _) (PathTrie []) =
    error "legacyComparePathTrie: invalid empty PathTrie children"
legacyComparePathTrie left@(PathTrie _) right@(PathTrieSingleChild _ _) =
    flipOrdering $ legacyComparePathTrie right left
legacyComparePathTrie (PathTrie children1) (PathTrie children2) =
    legacyComparePathTrieChildren children1 children2

legacyComparePathTrieChildren :: [(Int, PathTrie)] -> [(Int, PathTrie)] -> Ordering
legacyComparePathTrieChildren [] [] = EQ
legacyComparePathTrieChildren [] _ = LT
legacyComparePathTrieChildren _ [] = GT
legacyComparePathTrieChildren ((i1, pt1) : rest1) ((i2, pt2) : rest2) =
    case compare i1 i2 of
        LT -> LT
        GT -> GT
        EQ -> case legacyComparePathTrie pt1 pt2 of
            EQ -> legacyComparePathTrieChildren rest1 rest2
            result -> result

flipOrdering :: Ordering -> Ordering
flipOrdering LT = GT
flipOrdering EQ = EQ
flipOrdering GT = LT

typeSearchNode :: Node Symbol
typeSearchNode =
    appNode
        (appNode (monoFunctionScope 0) (monoArgumentScope 0))
        (monoTermsOfSize 0 2)

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

finiteChoiceNode :: Int -> Node Symbol
finiteChoiceNode salt =
    Node
        [ Edge (named "f" salt) [choiceAB salt, choiceAB salt]
        , Edge (named "g" salt) [choiceAB salt, choiceAB salt]
        ]

constrainedChoiceNode :: Int -> Node Symbol
constrainedChoiceNode salt =
    Node
        [ mkEdge (named "f" salt) [choiceAB salt, choiceAB salt] (mkEqConstraints [[path [0], path [1]]])
        , Edge (named "g" salt) [choiceAB salt, choiceAB salt]
        ]

choiceAB :: Int -> Node Symbol
choiceAB salt = Node [Edge (named "a" salt) [], Edge (named "b" salt) []]

recursivePathConstraints :: EqConstraints
recursivePathConstraints = mkEqConstraints [[path [0, 0, 0, 0], path [1, 0, 0]]]

recursivePathNodes :: Int -> [Node Symbol]
recursivePathNodes salt = [infiniteFNode salt, infiniteFNode salt]

infiniteFNode :: Int -> Node Symbol
infiniteFNode salt = createMu $ \r -> Node [Edge (named "f" salt) [r]]

recursiveTypeA :: Int -> Node Symbol
recursiveTypeA salt =
    createMu $ \r ->
        Node
            [ Edge (named "baseType" salt) []
            , Edge "->" [theArrowNode, r, r]
            , Edge "Maybe" [r]
            , Edge "List" [r]
            ]

recursiveTypeB :: Int -> Node Symbol
recursiveTypeB salt =
    createMu $ \r ->
        Node
            [ Edge (named "baseType" salt) []
            , Edge "->" [theArrowNode, mkDatatype "List" [r], r]
            , Edge "List" [r]
            ]
