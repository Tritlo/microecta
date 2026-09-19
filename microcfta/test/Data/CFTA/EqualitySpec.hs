{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.EqualitySpec (spec) where

import Control.Exception (evaluate)
import qualified Data.HashSet as HashSet
import Data.Hashable (Hashable)
import Data.IORef (modifyIORef, newIORef, readIORef)
import qualified Data.IntMap.Strict as IntMap
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Tree as Tree
import GHC.Generics (Generic)

import System.IO.Unsafe (unsafePerformIO)

import Test.Hspec
import Test.QuickCheck

import Data.CFTA.Equality
import Data.CFTA.Internal.UnionFind (intToUVar)
import Data.CFTA.Symbol

import Test.Generators.Equality ()

-----------------------------------------------------------------

data ArithmeticSymbol = Zero | Succ | Recursion
    deriving (Eq, Generic, Ord, Read, Show)

instance Hashable ArithmeticSymbol

constTerms :: [Symbol] -> Node Symbol EqConstraints
constTerms ss = Node (map (`Edge` []) ss)

ex1 :: Node Symbol EqConstraints
ex1 =
    Node
        [ mkEdge "f" [constTerms ["1", "2"], Node [Edge "g" [constTerms ["1", "2"]]]] (mkEqConstraints [[path [0], path [1, 0]]])
        ]

ex2 :: Node Symbol EqConstraints
ex2 =
    Node
        [ mkEdge
            "f"
            [constTerms ["1", "2", "3"], Node [Edge "g" [constTerms ["1", "2", "4"]]]]
            (mkEqConstraints [[path [0], path [1, 0]]])
        ]

ex3 :: Node Symbol EqConstraints
ex3 = Node [Edge "f" [Node [Edge "g" [constTerms ["1", "2"]]]], Edge "h" [Node [Edge "i" [constTerms ["3", "4"]]]]]

ex3_root_doubled :: Node Symbol EqConstraints
ex3_root_doubled = Node [Edge "ff" [Node [Edge "g" [constTerms ["1", "2"]]]], Edge "hh" [Node [Edge "i" [constTerms ["3", "4"]]]]]

ex3_doubled :: Node Symbol EqConstraints
ex3_doubled = Node [Edge "f" [Node [Edge "g" [constTerms ["11", "22"]]]], Edge "h" [Node [Edge "i" [constTerms ["33", "44"]]]]]

doubleNodeSymbols :: Node Symbol EqConstraints -> Node Symbol EqConstraints
doubleNodeSymbols (Node es) = Node $ map doubleEdgeSymbol es
  where
    doubleEdgeSymbol :: Edge Symbol EqConstraints -> Edge Symbol EqConstraints
    doubleEdgeSymbol (Edge (Symbol s) ns) = Edge (Symbol (Text.append s s)) ns
doubleNodeSymbols n = error $ "doubleNodeSymbols: unexpected " <> show n

testBigNode :: Node Symbol EqConstraints
testBigNode = ex3

{- FOURMOLU_DISABLE -}
-- One regression value on one line: formatted, it is 1,500 lines.
bug062721NonIdempotentEqConstraintReduction :: (EqConstraints, [Node Symbol EqConstraints])
bug062721NonIdempotentEqConstraintReduction =
    ( (EqConstraints [PathEClass [Path [0], Path [2, 0, 2]], PathEClass [Path [1], Path [2, 0, 0]], PathEClass [Path [2, 0, 1], Path [3, 0]]])
    , [(Node [(Edge "baseType" [])]), (Node [(Edge "(->)" [])]), (Node [(mkEdge "app" [(Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))]), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])]), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "(->)" [])]), (Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "baseType" [])]), (Node [(Edge "baseType" [])])])])]), (Edge "x" [(Node [(Edge "baseType" [])])]), (Edge "n" [(Node [(Edge "Int" [])])]), (Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 1]], PathEClass [Path [1, 2], Path [2, 2]]]))])]), (Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "Int" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [2, 1], Path [2, 2, 0]]]))])]), (Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 2, 1, 0]], PathEClass [Path [1, 2, 1], Path [1, 2, 2], Path [2, 1], Path [2, 2, 2]]]))])])]), (Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "baseType" [])]), (Node [(Edge "baseType" [])])])])]), (Edge "x" [(Node [(Edge "baseType" [])])]), (Edge "n" [(Node [(Edge "Int" [])])]), (Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 1]], PathEClass [Path [1, 2], Path [2, 2]]]))])]), (Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "Int" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [2, 1], Path [2, 2, 0]]]))])]), (Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 2, 1, 0]], PathEClass [Path [1, 2, 1], Path [1, 2, 2], Path [2, 1], Path [2, 2, 2]]]))])])])] (EqConstraints [PathEClass [Path [0], Path [2, 0, 2]], PathEClass [Path [1], Path [2, 0, 0]], PathEClass [Path [2, 0, 1], Path [3, 0]]]))]), (Node [(mkEdge "app" [(Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))]), (Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))]), (Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))]), (Edge "Maybe" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "(->)" [])]), (Node [(mkEdge "app" [(Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))]), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])]), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "(->)" [])]), (Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "baseType" [])]), (Node [(Edge "baseType" [])])])])]), (Edge "x" [(Node [(Edge "baseType" [])])]), (Edge "n" [(Node [(Edge "Int" [])])]), (Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 1]], PathEClass [Path [1, 2], Path [2, 2]]]))])]), (Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "Int" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [2, 1], Path [2, 2, 0]]]))])]), (Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 2, 1, 0]], PathEClass [Path [1, 2, 1], Path [1, 2, 2], Path [2, 1], Path [2, 2, 2]]]))])])]), (Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "baseType" [])]), (Node [(Edge "baseType" [])])])])]), (Edge "x" [(Node [(Edge "baseType" [])])]), (Edge "n" [(Node [(Edge "Int" [])])]), (Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 1]], PathEClass [Path [1, 2], Path [2, 2]]]))])]), (Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "Int" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [2, 1], Path [2, 2, 0]]]))])]), (Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 2, 1, 0]], PathEClass [Path [1, 2, 1], Path [1, 2, 2], Path [2, 1], Path [2, 2, 2]]]))])])])] (EqConstraints [PathEClass [Path [0], Path [2, 0, 2]], PathEClass [Path [1], Path [2, 0, 0]], PathEClass [Path [2, 0, 1], Path [3, 0]]]))]), (Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "baseType" [])]), (Node [(Edge "baseType" [])])])])]), (Edge "x" [(Node [(Edge "baseType" [])])]), (Edge "n" [(Node [(Edge "Int" [])])]), (Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 1]], PathEClass [Path [1, 2], Path [2, 2]]]))])]), (Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "Int" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [2, 1], Path [2, 2, 0]]]))])]), (Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 2, 1, 0]], PathEClass [Path [1, 2, 1], Path [1, 2, 2], Path [2, 1], Path [2, 2, 2]]]))])])])] (EqConstraints [PathEClass [Path [0], Path [2, 0, 2]], PathEClass [Path [1], Path [2, 0, 0]], PathEClass [Path [2, 0, 1], Path [3, 0]]])), (mkEdge "app" [(Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))]), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])]), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "(->)" [])]), (Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "baseType" [])]), (Node [(Edge "baseType" [])])])])]), (Edge "x" [(Node [(Edge "baseType" [])])]), (Edge "n" [(Node [(Edge "Int" [])])]), (Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 1]], PathEClass [Path [1, 2], Path [2, 2]]]))])]), (Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "Int" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [2, 1], Path [2, 2, 0]]]))])]), (Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 2, 1, 0]], PathEClass [Path [1, 2, 1], Path [1, 2, 2], Path [2, 1], Path [2, 2, 2]]]))])])]), (Node [(mkEdge "app" [(Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))]), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])]), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "(->)" [])]), (Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "baseType" [])]), (Node [(Edge "baseType" [])])])])]), (Edge "x" [(Node [(Edge "baseType" [])])]), (Edge "n" [(Node [(Edge "Int" [])])]), (Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 1]], PathEClass [Path [1, 2], Path [2, 2]]]))])]), (Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "Int" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [2, 1], Path [2, 2, 0]]]))])]), (Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 2, 1, 0]], PathEClass [Path [1, 2, 1], Path [1, 2, 2], Path [2, 1], Path [2, 2, 2]]]))])])]), (Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "baseType" [])]), (Node [(Edge "baseType" [])])])])]), (Edge "x" [(Node [(Edge "baseType" [])])]), (Edge "n" [(Node [(Edge "Int" [])])]), (Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 1]], PathEClass [Path [1, 2], Path [2, 2]]]))])]), (Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "Int" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [2, 1], Path [2, 2, 0]]]))])]), (Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 2, 1, 0]], PathEClass [Path [1, 2, 1], Path [1, 2, 2], Path [2, 1], Path [2, 2, 2]]]))])])])] (EqConstraints [PathEClass [Path [0], Path [2, 0, 2]], PathEClass [Path [1], Path [2, 0, 0]], PathEClass [Path [2, 0, 1], Path [3, 0]]]))])] (EqConstraints [PathEClass [Path [0], Path [2, 0, 2]], PathEClass [Path [1], Path [2, 0, 0]], PathEClass [Path [2, 0, 1], Path [3, 0]]]))])]
    )
{- FOURMOLU_ENABLE -}

infiniteFNode :: Node Symbol EqConstraints
infiniteFNode = createMu (\x -> (Node [Edge "f" [x]]))

--------------------------------------------------------------
----------------------------- Main ---------------------------
--------------------------------------------------------------

spec :: Spec
spec = do
    describe "Pathable" $ do
        it "Node.getPath root" $
            getPath (path []) testBigNode `shouldBe` testBigNode

        it "Node.getPath one-level" $
            getPath (path [0]) ex1 `shouldBe` (constTerms ["1", "2"])

        it "Node.getPath merges multiple branches" $
            getPath (path [0, 0]) ex3 `shouldBe` (constTerms ["1", "2", "3", "4"])

        it "Node.modifyAtPath modifies at root" $
            modifyAtPath doubleNodeSymbols (path []) ex3 `shouldBe` ex3_root_doubled

        it "Node.modifyAtPath modifies at path" $
            modifyAtPath doubleNodeSymbols (path [0, 0]) ex3 `shouldBe` ex3_doubled

    describe "hash-consing" $ do
        it "similar mu-nodes created independently are equal / have equal ids" $
            (createMu (\x -> Node [Edge "f" [x]]) :: Node Symbol EqConstraints) `shouldBe` createMu (\x -> Node [Edge "f" [x]])

        it "keeps identities from different symbol alphabets distinct" $ do
            let typed = Node [Edge Zero []] :: Node ArithmeticSymbol EqConstraints
                textual = Node [Edge "Zero" []] :: Node Symbol EqConstraints
            nodeIdentity typed `shouldNotBe` nodeIdentity textual

    describe "ECTA-nodes" $ do
        it "equality constraints constrain" $
            terms ex1 `shouldSatisfy` ((== 2) . length)

        it "reduces paths constrained by equality constraints" $
            reducePartially ex2 `shouldBe` reducePartially ex1

        it "nodeRepresents requires exact term arity" $ do
            let n = Node [Edge "f" [constTerms ["a"], constTerms ["b"]]]
            nodeRepresents n (Tree.Node "f" [Tree.Node "a" [], Tree.Node "b" []]) `shouldBe` True
            nodeRepresents n (Tree.Node "f" [Tree.Node "a" []]) `shouldBe` False
            nodeRepresents n (Tree.Node "f" [Tree.Node "a" [], Tree.Node "b" [], Tree.Node "c" []]) `shouldBe` False

    describe "templates" $ do
        it "restricts a constrained language and lets equality narrow a hole" $ do
            let values = Node [Edge "a" [], Edge "b" []] :: Node Symbol EqConstraints
                pairs =
                    Node
                        [ mkEdge
                            "pair"
                            [values, values]
                            (mkEqConstraints [[path [0], path [1]]])
                        ]
                rightIsA = TemplateNode "pair" [Hole, TemplateNode "a" []]
            terms (termsMatching rightIsA pairs)
                `shouldBe` [Tree.Node "pair" [Tree.Node "a" [], Tree.Node "a" []]]

        it "distinguishes exact arity from an explicit prefix" $ do
            let call = Tree.Node "call" [Tree.Node "f" [], Tree.Node "x" []] :: Tree.Tree Symbol
            matchesTemplate (TemplateNode "call" [Hole]) call `shouldBe` False
            matchesTemplate (TemplatePrefix "call" [TemplateNode "f" []]) call `shouldBe` True

        it "treats <v> as an ordinary symbol" $ do
            matchesTemplate (TemplateNode "<v>" []) (Tree.Node "<v>" [] :: Tree.Tree Symbol) `shouldBe` True
            matchesTemplate (TemplateNode "<v>" []) (Tree.Node "other" [] :: Tree.Tree Symbol) `shouldBe` False

        it "uses a typed alphabet without an IsString instance" $ do
            let zero = Node [Edge Zero []] :: Node ArithmeticSymbol EqConstraints
                naturals = Node [Edge Zero [], Edge Succ [zero]]
                successors = termsMatching (TemplateNode Succ [Hole]) naturals
                materialize = \case
                    ConcreteSymbol symbol -> symbol
                    UVarHole _ -> Recursion
                    TruncatedRecursion -> Recursion
            termsWith Recursion successors
                `shouldBe` [Tree.Node Succ [Tree.Node Zero []]]
            truncatedTerms successors
                `shouldBe` [Tree.Node (ConcreteSymbol Succ) [Tree.Node (ConcreteSymbol Zero) []]]
            map (fmap materialize) (truncatedTerms successors)
                `shouldBe` [Tree.Node Succ [Tree.Node Zero []]]

        it "restricting a finite ECTA agrees with filtering its terms" $
            property $
                mapSize (min 3) $ \(template :: Template Symbol) (node :: Node Symbol EqConstraints) ->
                    HashSet.fromList (terms $ termsMatching template node)
                        `shouldBe` HashSet.fromList (filter (matchesTemplate template) $ terms node)

    describe "intersection" $ do
        it "intersection commutes with terms" $
            property $
                mapSize (min 3) $ \(n1 :: Node Symbol EqConstraints) (n2 :: Node Symbol EqConstraints) ->
                    HashSet.fromList (terms $ intersect n1 n2)
                        `shouldBe` HashSet.intersection
                            (HashSet.fromList $ terms n1)
                            (HashSet.fromList $ terms n2)

        it "intersect is associative" $
            property $
                \(n1 :: Node Symbol EqConstraints) n2 n3 -> ((n1 `intersect` n2) `intersect` n3) == (n1 `intersect` (n2 `intersect` n3))

        it "intersect is commutative" $
            property $
                \(n1 :: Node Symbol EqConstraints) n2 -> intersect n1 n2 == intersect n2 n1

        it "intersect distributes over union" $
            property $
                \(n1 :: Node Symbol EqConstraints) n2 n3 -> intersect n1 (union [n2, n3]) == union [n1 `intersect` n2, n1 `intersect` n3]

        it "intersect is idempotent" $
            property $
                \(n1 :: Node Symbol EqConstraints) -> intersect n1 n1 == n1

    describe "intersection examples" $ do
        -- Intersection examples without Mu nodes
        --
        -- Note: Intersection between 1 and 3 is not well-defined: must be same-sorted.

        it "remove leaf choice" $
            intersect intTest1 intTest2 `shouldBe` intTest1

        it "remove non-leaf choice" $
            intersect intTest3 intTest4 `shouldBe` intTest3

        -- This test is a bit indirect: the intersection results in a term with what I /think/ is an inaccessible branch.
        -- Not sure if there is a clean-up pass we can do.
        it "add constraints" $
            terms (intTest5 `intersect` intTest6) `shouldBe` [Tree.Node "g" [Tree.Node "a" [], Tree.Node "b" []]]

        -- Intersection examples with Mu nodes

        it "intersect (one-step loop) with (its own unfolding: step, one-step)" $
            intersect intTest7 intTest8 `shouldBe` intTest8

        it "intersect (one-step loop) with (two-step loop)" $
            intersect intTest7 intTest9 `shouldBe` intTest9

        it "intersect (one-step loop) with (one step, two-step loop)" $
            intersect intTest7 intTest10 `shouldBe` intTest10

        it "intersect (one step, one-step loop) with (two-step loop)" $
            intersect intTest8 intTest9 `shouldBe` intTest10

        it "intersect (one step, one-step loop) with (one step, two-step loop)" $
            intersect intTest8 intTest10 `shouldBe` intTest10

        it "intersect (two-step loop) with (one step, two-step loop)" $
            intersect intTest9 intTest10 `shouldBe` intTest8

        it "intersect with nested Mus" $ do
            intersect intTest11 intTest12 `shouldBe` Node [Edge "f" [createMu $ \r -> Node [Edge "f" [r]]]]

    describe "reduction" $ do
        it "reduction preserves terms" $
            property $
                mapSize (min 3) $
                    \(n :: Node Symbol EqConstraints) -> HashSet.fromList (terms n) `shouldBe` HashSet.fromList (terms $ reducePartially n)

        it "reducing child domains preserves constrained terms" $
            property $
                mapSize (min 3) $ \(e :: Edge Symbol EqConstraints) ->
                    let ns = edgeChildren e
                        ecs = edgeConstraint e
                        ns' = reduceEqConstraints ecs EmptyConstraints ns
                        reduced = mkEdge (edgeSymbol e) ns' ecs
                     in HashSet.fromList (terms $ Node [reduced])
                            `shouldBe` HashSet.fromList (terms $ Node [e])

        it "reducing intersected child domains preserves constrained terms" $
            let intersectingEdge :: Gen (Edge Symbol EqConstraints)
                intersectingEdge =
                    resize 3 arbitrary `suchThatMap` uncurry intersectEdge
             in forAll intersectingEdge $ \e' ->
                    let ns = edgeChildren e'
                        ecs = edgeConstraint e'
                        ns' = reduceEqConstraints ecs EmptyConstraints ns
                        reduced = mkEdge (edgeSymbol e') ns' ecs
                     in HashSet.fromList (terms $ Node [reduced])
                            `shouldBe` HashSet.fromList (terms $ Node [e'])

        it "reducing a constraint is idempotent: buggy input 6/27/21" $ do
            pendingWith
                "Known non-idempotent reduction, open since 2021-06-29. The \
                \fixture below reproduces it; processing the eclasses in the \
                \reverse order makes no difference."
            let (ecs, ns) = bug062721NonIdempotentEqConstraintReduction
                ns' = reduceEqConstraints ecs EmptyConstraints ns
            ns' `shouldBe` reduceEqConstraints ecs EmptyConstraints ns'

        -- One reduction pass does not establish this: a nested constrained
        -- edge can narrow a child after the outer pass has read it. The
        -- fixpoint does, so the fixture is reduced until it stops changing.
        it "saturated reduction means, for everything at a path, there is something matching at the other paths" $
            let liveConstrainedEdge :: Gen (Edge Symbol EqConstraints)
                liveConstrainedEdge =
                    arbitrary `suchThatMap` \edge ->
                        let reduced = fixUnbounded (reduceEdgeIntersection EmptyConstraints) edge
                         in if reduced /= emptyEdge (edgeSymbol reduced) && edgeConstraint reduced /= EmptyConstraints
                                then Just reduced
                                else Nothing
             in forAll liveConstrainedEdge $ \edge ->
                    let ns = edgeChildren edge
                     in and
                            [ intersect n1 n2 /= EmptyNode
                            | ec <- unsafeGetEclasses (edgeConstraint edge)
                            , p1 <- unPathEClass ec
                            , p2 <- unPathEClass ec
                            , let n2 = getPath p2 ns
                            , n1 <- getAllAtPath p1 ns
                            ]

    describe "(un)folding" $ do
        it "unfolding a mu node once unfolds it once" $
            unfoldOuterRec infiniteFNode `shouldBe` (Node [Edge "f" [infiniteFNode]])

        it "recursive terms are unrolled to the depth of the constraints and no more" $
            let ecs = (mkEqConstraints [[path [0, 0, 0, 0], path [1, 0, 0]]])
                ns = [infiniteFNode, infiniteFNode]
                ns' = reduceEqConstraints ecs EmptyConstraints ns
                ns'' = reduceEqConstraints ecs EmptyConstraints ns'
                f n = Node [Edge "f" [n]]
             in (ns' == ns'') && ns' == [f $ f $ f $ f infiniteFNode, f $ f $ f infiniteFNode] `shouldBe` True

        it "refold folds the simplest unrolled input" $
            refold (Node [Edge "f" [infiniteFNode]]) `shouldBe` infiniteFNode

    describe "traversals" $ do
        it "mapNodes hits each node exactly once" $
            -- Note: If the Arbitrary Node instance is changed to return empty or mu nodes, this will need to change
            -- Note: If the Arbitrary Node instance is changed to return empty or mu nodes, this will need to change

            -- Note: If the Arbitrary Node instance is changed to return empty or mu nodes, this will need to change
            property $ \(n :: Node Symbol EqConstraints) -> unsafePerformIO $ do
                v <- newIORef 0
                let n' = mapNodes (\m -> unsafePerformIO (modifyIORef v (+ 1) >> pure m)) n
                let k = nodeCount n'
                numInvocations <- k `seq` readIORef v
                return $ k == numInvocations

        it "nodeCount works on a trivial recursive node" $
            nodeCount infiniteFNode `shouldBe` 1

    describe "enumeration" $ do
        it "reduction preserves enumeration on nodes without mu" $
            property $
                mapSize (min 3) $
                    \(n :: Node Symbol EqConstraints) -> HashSet.fromList (terms n) `shouldBe` HashSet.fromList (terms $ reducePartially n)

    describe "degenerate inputs" $ do
        it "maxIndegree of a node with nothing to count is zero" $ do
            maxIndegree EmptyNode `shouldBe` 0
            maxIndegree (Node [Edge "a" []] :: Node Symbol EqConstraints) `shouldBe` 1
            maxIndegree ex3 `shouldBe` 2

        it "a non-positive unfold bound terminates" $ do
            terms (unfoldBounded 0 intTest7) `shouldBe` []
            terms (unfoldBounded (-1) intTest7) `shouldBe` []
            terms (unfoldBounded (-100) intTest7) `shouldBe` []

    describe "enumerating recursive automata" $ do
        -- A root Mu is never expanded, so before this was fixed terms
        -- reported the empty language and truncatedTerms raised.
        it "a bare Mu truncates instead of reporting an empty language" $ do
            terms intTest7 `shouldBe` [Tree.Node "Mu" []]
            truncatedTerms intTest7
                `shouldBe` [Tree.Node TruncatedRecursion []]

        it "a Mu under an edge truncates the same way" $
            terms (Node [Edge "wrap" [intTest7]])
                `shouldBe` [Tree.Node "wrap" [Tree.Node "Mu" []]]

        it "unfolding first enumerates past the recursion" $
            terms (unfoldBounded 2 intTest7)
                `shouldMatchList` [Tree.Node "a" [], Tree.Node "f" [Tree.Node "a" []]]

        it "a recursion with no base case unfolds to nothing" $
            terms (unfoldBounded 2 infiniteFNode) `shouldBe` []

    describe "dropping constraints" $ do
        it "an edge keeps its symbol and children" $ do
            let dropped = dropEdgeConstraints constrainedPair
            edgeSymbol dropped `shouldBe` edgeSymbol constrainedPair
            edgeChildren dropped `shouldBe` edgeChildren constrainedPair
            edgeConstraint dropped `shouldBe` EmptyConstraints

        it "the language grows to every combination of children" $ do
            let constrained = Node [constrainedPair]
            length (terms constrained) `shouldBe` 2
            length (terms $ dropConstraints constrained) `shouldBe` 4

        it "the original language is retained" $ do
            let constrained = Node [constrainedPair]
                relaxed = HashSet.fromList $ terms $ dropConstraints constrained
            terms constrained `shouldSatisfy` all (`HashSet.member` relaxed)

    describe "pruning" $ do
        it "an oracle that never prunes enumerates the whole language" $
            HashSet.fromList (termsPrune () keepEverything searchNode)
                `shouldBe` HashSet.fromList (terms searchNode)

        it "rejecting the node before expansion drops the whole branch" $
            termsPrune () rejectEveryNode searchNode `shouldBe` []

        it "rejecting a produced fragment drops only that branch" $ do
            let oracle state _ (Left frag) = do
                    partial <- expandPartialTermFrag frag
                    return (partial == partialTerm (applied "f" "x"), state)
                oracle state _ (Right _) = return (False, state)
            HashSet.fromList (termsPrune () oracle searchNode)
                `shouldBe` HashSet.fromList
                    [applied "f" "y", applied "g" "x", applied "g" "y"]

        -- The pattern the pruning docs prescribe now that the library holds no
        -- pending-check state of its own: the oracle parks a check under the
        -- hole's representative and settles it when that hole is expanded.
        it "an oracle can suspend a check on a hole and settle it later" $ do
            let forbidden = partialTerm $ Tree.Node "f" [Tree.Node "T" []]

                oracle parkedChecks uv (Left frag) = do
                    rep <- uvarToInt <$> getUVarRepresentative uv
                    partial <- expandPartialTermFrag frag
                    case IntMap.lookup rep parkedChecks of
                        -- Settling a parked check: this hole is now concrete.
                        Just parked ->
                            return
                                ( partial `elem` parked
                                , IntMap.delete rep parkedChecks
                                )
                        Nothing -> do
                            holes <- mapM (fmap uvarToInt . getUVarRepresentative) (holesOf frag)
                            return
                                ( False
                                , foldr (\hole -> IntMap.insertWith (<>) hole [forbidden]) parkedChecks holes
                                )
                oracle parkedChecks _ (Right _) = return (False, parkedChecks)

                shared symbol = Tree.Node "filter" [wrapped symbol, wrapped symbol]
                wrapped symbol = Tree.Node symbol [Tree.Node "T" []]
            termsPrune IntMap.empty oracle sharedFilterNode `shouldBe` [shared "g"]

        it "an expansion order steers which hole is expanded first" $ do
            -- Rejects a branch whose first hole to become concrete is "x"-rooted.
            let oracle seen _ (Left frag) = do
                    partial <- expandPartialTermFrag frag
                    case (seen, partial) of
                        (Nothing, Tree.Node (ConcreteSymbol symbol) _)
                            | symbol `elem` holeSymbols ->
                                return (symbol == "x", Just symbol)
                        _ -> return (False, seen)
                oracle seen _ (Right _) = return (False, seen)
                holeSymbols = ["f", "g", "x", "y"] :: [Symbol]
                preferLast _ candidates = case reverse candidates of
                    uv : _ -> Just uv
                    [] -> Nothing
            -- The enumerator reaches the left hole first, which is never "x".
            length (termsPruneWith "Mu" Nothing noExpansionPreference oracle twoHoleNode)
                `shouldBe` 4
            -- Steering to the last candidate reaches the right hole first.
            length (termsPruneWith "Mu" Nothing preferLast oracle twoHoleNode)
                `shouldBe` 2

        it "a preference outside the candidates is ignored" $ do
            let preferAbsent _ _ = Just (intToUVar 9999)
            termsPruneWith "Mu" () preferAbsent keepEverything twoHoleNode
                `shouldBe` terms twoHoleNode

    describe "counted nested Mu" $ do
        it "no Mu" $
            numNestedMu (Node [Edge "a" []] :: Node Symbol EqConstraints) `shouldBe` 0
        it "single Mu" $
            numNestedMu (Mu (\x -> Node [Edge "f" [x]]) :: Node Symbol EqConstraints) `shouldBe` 1
        it "two parallel Mus" $
            numNestedMu
                (Node [Edge "h" [Mu $ \x -> Node [Edge "g" [x]], Mu $ \x -> Node [Edge "h" [x]]]] :: Node Symbol EqConstraints)
                `shouldBe` 1
        it "nested" $
            numNestedMu (Mu (\x -> Node [Edge "f" [x], Edge "g" [Mu $ \y -> Node [Edge "g" [y]]]]) :: Node Symbol EqConstraints)
                `shouldBe` 2

    describe "redundant Mu" $ do
        it "redundant inner Mu is skipped even when its shape is already interned" $ do
            _ <- evaluate infiniteFNode
            let actual = Mu (\r1 -> Mu $ \_r2 -> Node [Edge "f" [r1]]) :: Node Symbol EqConstraints
                expected = Mu (\r1 -> Node [Edge "f" [r1]]) :: Node Symbol EqConstraints
            actual `shouldBe` expected

        it "redundant outer Mu is skipped" $
            (Mu (\_r1 -> Mu $ \r2 -> Node [Edge "f" [r2]]) :: Node Symbol EqConstraints)
                `shouldBe` Mu (\r1 -> Node [Edge "f" [r1]])

        it "two redundant Mus are both skipped" $
            (Mu (\_r1 -> Mu $ \_r2 -> Node [Edge "f" []]) :: Node Symbol EqConstraints)
                `shouldBe` Node [Edge "f" []]

        it "a used outer Mu is kept" $
            numNestedMu (Mu (\r1 -> Mu $ \_r2 -> Node [Edge "f" [r1]]) :: Node Symbol EqConstraints) `shouldBe` 1

        it "a used inner Mu is kept, and is not the same as reusing the outer one" $ do
            let nested = Mu (\r1 -> Mu $ \r2 -> Node [Edge "f" [r1], Edge "g" [r2]]) :: Node Symbol EqConstraints
                shared = Mu (\r1 -> Node [Edge "f" [r1], Edge "g" [r1]]) :: Node Symbol EqConstraints
            numNestedMu nested `shouldBe` 2
            nested `shouldNotBe` shared

        it "keeping a redundant Mu is what createMuDontCleanup is for" $
            numNestedMu (createMuDontCleanup (\_r -> Node [Edge "f" []]) :: Node Symbol EqConstraints) `shouldBe` 1

    describe "nested Mu" $
        it "references to different Mu nodes are not confused" $
            property $ do
                -- Two nodes with very similar structure
                -- We are precise about evaluation order here: what we are testing is that after the first term have been
                -- interned, we do /NOT/ reuse that term when interning the second. (If we /did/ confuse different references
                -- to 'Mu' nodes, @m@ looks precisely like the inner @Mu@ node of @n@.)
                n <- evaluate (Mu (\r1 -> Mu $ \r2 -> Node [Edge "f" [r1], Edge "g" [r2], Edge "a" []]) :: Node Symbol EqConstraints)
                m <- evaluate (Mu (\r -> Node [Edge "f" [r], Edge "g" [r], Edge "a" []]) :: Node Symbol EqConstraints)

                -- This is a low-level test; crush doesn't work, because we don't see what 'InternedMu' caches.
                let collectAllIds :: Node Symbol EqConstraints -> Set Int
                    collectAllIds EmptyNode = Set.empty
                    collectAllIds (InternedNode node) =
                        Set.unions
                            [ Set.singleton (internedNodeId node)
                            , Set.unions $ concatMap (map collectAllIds . edgeChildren) (internedNodeEdges node)
                            ]
                    collectAllIds (InternedMu mu) =
                        Set.unions
                            [ Set.singleton (internedMuId mu)
                            , Set.union (collectAllIds (internedMuBody mu)) (collectAllIds (internedMuShape mu))
                            ]
                    collectAllIds (Rec _) = Set.empty

                Set.intersection (collectAllIds n) (collectAllIds m) `shouldBe` Set.empty

-------------------------------------
--- Example inputs for the intersection tests
-------------------------------------

-- | Single zero-argument term
intTest1 :: Node Symbol EqConstraints
intTest1 = Node [Edge "f" []]

-- | Two zero-argument terms
intTest2 :: Node Symbol EqConstraints
intTest2 = Node [Edge "f" [], Edge "g" []]

-- | Single one-argument term, two possible arguments
intTest3 :: Node Symbol EqConstraints
intTest3 = Node [Edge "f" [Node [Edge "a" [], Edge "b" []]]]

-- | Two one-argument terms, each two possible arguments (chosen from the same set)
intTest4 :: Node Symbol EqConstraints
intTest4 = Node [Edge "f" args, Edge "g" args]
  where
    args :: [Node Symbol EqConstraints]
    args = [arg]

    arg :: Node Symbol EqConstraints
    arg = Node [Edge "a" [], Edge "b" []]

-- | Two two-argument terms, no choice for arguments
intTest5 :: Node Symbol EqConstraints
intTest5 = Node [Edge "f" args, Edge "g" args]
  where
    args :: [Node Symbol EqConstraints]
    args = [argA, argB]

    argA, argB :: Node Symbol EqConstraints
    argA = Node [Edge "a" []]
    argB = Node [Edge "b" []]

-- | Two two-argument terms, same choice for arguments, but constrain the two arguments to be the same if choosing f
intTest6 :: Node Symbol EqConstraints
intTest6 = Node [mkEdge "f" args cs, Edge "g" args]
  where
    args :: [Node Symbol EqConstraints]
    args = [arg, arg]

    arg :: Node Symbol EqConstraints
    arg = Node [Edge "a" [], Edge "b" []]

    cs :: EqConstraints
    cs = mkEqConstraints [[path [0], path [1]]]

-- | f (f (f (... a)))
intTest7 :: Node Symbol EqConstraints
intTest7 = createMu $ \r -> Node [Edge "f" [r], Edge "a" []]

{- | A pair whose two children are forced equal.

Dropping that constraint admits every combination of them instead.
-}
constrainedPair :: Edge Symbol EqConstraints
constrainedPair =
    mkEdge
        "pair"
        [constTerms ["1", "2"], constTerms ["1", "2"]]
        (mkEqConstraints [[path [0], path [1]]])

{- | A node in the term-search encoding the pruning matcher reads.

An @app@ edge carries two leading type children followed by the function and
argument positions, and each term symbol carries its type.
-}
searchNode :: Node Symbol EqConstraints
searchNode = Node [Edge "app" [anyType, anyType, functions, arguments]]
  where
    functions = Node [Edge "f" [anyType], Edge "g" [anyType]]
    arguments = Node [Edge "x" [anyType], Edge "y" [anyType]]

anyType :: Node Symbol EqConstraints
anyType = Node [Edge "T" []]

-- | One accepted term of 'searchNode'.
applied :: Symbol -> Symbol -> Tree.Tree Symbol
applied functionSymbol argumentSymbol =
    Tree.Node
        "app"
        [ Tree.Node "T" []
        , Tree.Node "T" []
        , Tree.Node functionSymbol [Tree.Node "T" []]
        , Tree.Node argumentSymbol [Tree.Node "T" []]
        ]

-- | Lift a concrete term into the alphabet used by partial enumeration.
partialTerm :: Tree.Tree symbol -> Tree.Tree (PartialSymbol symbol)
partialTerm = fmap ConcreteSymbol

{- | A node with two independent holes, one per equality class.

Both are expandable at once after the root, so the order they are taken in is
observable.
-}
twoHoleNode :: Node Symbol EqConstraints
twoHoleNode =
    Node
        [ mkEdge
            "pair"
            [leftTerms, leftTerms, rightTerms, rightTerms]
            (mkEqConstraints [[path [0], path [1]], [path [2], path [3]]])
        ]
  where
    leftTerms = Node [Edge "f" [anyType], Edge "g" [anyType]]
    rightTerms = Node [Edge "x" [anyType], Edge "y" [anyType]]

{- | A @filter@ node whose two children are one shared hole.

Enumerating it produces a fragment holding an unexpanded UVar, which is the
shape an oracle has to suspend on.
-}
sharedFilterNode :: Node Symbol EqConstraints
sharedFilterNode =
    Node
        [ mkEdge
            "filter"
            [alternatives, alternatives]
            (mkEqConstraints [[path [0], path [1]]])
        ]
  where
    alternatives = Node [Edge "f" [anyType], Edge "g" [anyType]]

-- | The holes of a fragment.
holesOf :: TermFragment Symbol -> [UVar]
holesOf (TermFragmentNode _ children) = concatMap holesOf children
holesOf (TermFragmentUVar uv) = [uv]

-- | An oracle that keeps every branch.
keepEverything ::
    () -> UVar -> Either (TermFragment Symbol) (Node Symbol EqConstraints) -> EnumerateM Symbol EqConstraints (Bool, ())
keepEverything state _ _ = return (False, state)

-- | An oracle that rejects every node before it is expanded.
rejectEveryNode ::
    () -> UVar -> Either (TermFragment Symbol) (Node Symbol EqConstraints) -> EnumerateM Symbol EqConstraints (Bool, ())
rejectEveryNode state _ (Right _) = return (True, state)
rejectEveryNode state _ (Left _) = return (False, state)

-- | intTest7, once unrolled
intTest8 :: Node Symbol EqConstraints
intTest8 = unfoldOuterRec intTest7

-- | Like intTest7, but with an 'inner' unrolling: two f edges before recursing
intTest9 :: Node Symbol EqConstraints
intTest9 = createMu $ \r -> Node [Edge "f" [Node [Edge "f" [r], Edge "a" []]], Edge "a" []]

-- | Like intTest9, but with a single additional node on top (not an unrolling: this would result in /two/ additional nodes)
intTest10 :: Node Symbol EqConstraints
intTest10 = Node [Edge "f" [intTest9], Edge "a" []]

-- | Example with nested Mu: refer to outer Mu
intTest11 :: Node Symbol EqConstraints
intTest11 = createMuDontCleanup $ \r -> createMuDontCleanup $ \_r' -> Node [Edge "f" [r]]

{- | Example with nested Mu: refer to inner Mu

Both examples hold one redundant binder, which 'createMu' would drop, so they are built with
'createMuDontCleanup' to keep the nesting these cases are about.
-}
intTest12 :: Node Symbol EqConstraints
intTest12 = createMuDontCleanup $ \_r -> createMuDontCleanup $ \r' -> Node [Edge "f" [r']]
