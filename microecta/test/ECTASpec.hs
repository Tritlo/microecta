{-# LANGUAGE OverloadedStrings #-}

module ECTASpec (spec) where

import Control.Exception (evaluate)
import qualified Data.HashSet as HashSet
import Data.Hashable (Hashable)
import Data.IORef (modifyIORef, newIORef, readIORef)
import qualified Data.IntMap.Strict as IntMap
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import GHC.Generics (Generic)

import System.IO.Unsafe (unsafePerformIO)

import Test.Hspec
import Test.QuickCheck

import Data.ECTA
import Data.ECTA.Internal.ECTA.Operations
import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Internal.Paths
import Data.ECTA.Term
import Data.Persistent.UnionFind (intToUVar)

import Test.Generators.ECTA ()

-----------------------------------------------------------------

data ArithmeticSymbol = Zero | Succ | Recursion
    deriving (Eq, Generic, Ord, Read, Show)

instance Hashable ArithmeticSymbol

constTerms :: [Symbol] -> Node Symbol
constTerms ss = Node (map (\s -> Edge s []) ss)

ex1 :: Node Symbol
ex1 = Node [mkEdge "f" [constTerms ["1", "2"], Node [Edge "g" [constTerms ["1", "2"]]]] (mkEqConstraints [[path [0], path [1, 0]]])]

ex2 :: Node Symbol
ex2 = Node [mkEdge "f" [constTerms ["1", "2", "3"], Node [Edge "g" [constTerms ["1", "2", "4"]]]] (mkEqConstraints [[path [0], path [1, 0]]])]

ex3 :: Node Symbol
ex3 = Node [Edge "f" [Node [Edge "g" [constTerms ["1", "2"]]]], Edge "h" [Node [Edge "i" [constTerms ["3", "4"]]]]]

ex3_root_doubled :: Node Symbol
ex3_root_doubled = Node [Edge "ff" [Node [Edge "g" [constTerms ["1", "2"]]]], Edge "hh" [Node [Edge "i" [constTerms ["3", "4"]]]]]

ex3_doubled :: Node Symbol
ex3_doubled = Node [Edge "f" [Node [Edge "g" [constTerms ["11", "22"]]]], Edge "h" [Node [Edge "i" [constTerms ["33", "44"]]]]]

doubleNodeSymbols :: Node Symbol -> Node Symbol
doubleNodeSymbols (Node es) = Node $ map doubleEdgeSymbol es
  where
    doubleEdgeSymbol :: Edge Symbol -> Edge Symbol
    doubleEdgeSymbol (Edge (Symbol s) ns) = Edge (Symbol (Text.append s s)) ns
doubleNodeSymbols n = error $ "doubleNodeSymbols: unexpected " <> show n

testBigNode :: Node Symbol
testBigNode = ex3

bug062721NonIdempotentEqConstraintReduction :: (EqConstraints, [Node Symbol])
bug062721NonIdempotentEqConstraintReduction =
    ( (EqConstraints [PathEClass [Path [0], Path [2, 0, 2]], PathEClass [Path [1], Path [2, 0, 0]], PathEClass [Path [2, 0, 1], Path [3, 0]]])
    , [(Node [(Edge "baseType" [])]), (Node [(Edge "(->)" [])]), (Node [(mkEdge "app" [(Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))]), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])]), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "(->)" [])]), (Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "baseType" [])]), (Node [(Edge "baseType" [])])])])]), (Edge "x" [(Node [(Edge "baseType" [])])]), (Edge "n" [(Node [(Edge "Int" [])])]), (Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 1]], PathEClass [Path [1, 2], Path [2, 2]]]))])]), (Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "Int" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [2, 1], Path [2, 2, 0]]]))])]), (Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 2, 1, 0]], PathEClass [Path [1, 2, 1], Path [1, 2, 2], Path [2, 1], Path [2, 2, 2]]]))])])]), (Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "baseType" [])]), (Node [(Edge "baseType" [])])])])]), (Edge "x" [(Node [(Edge "baseType" [])])]), (Edge "n" [(Node [(Edge "Int" [])])]), (Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 1]], PathEClass [Path [1, 2], Path [2, 2]]]))])]), (Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "Int" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [2, 1], Path [2, 2, 0]]]))])]), (Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 2, 1, 0]], PathEClass [Path [1, 2, 1], Path [1, 2, 2], Path [2, 1], Path [2, 2, 2]]]))])])])] (EqConstraints [PathEClass [Path [0], Path [2, 0, 2]], PathEClass [Path [1], Path [2, 0, 0]], PathEClass [Path [2, 0, 1], Path [3, 0]]]))]), (Node [(mkEdge "app" [(Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))]), (Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))]), (Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))]), (Edge "Maybe" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "(->)" [])]), (Node [(mkEdge "app" [(Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))]), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])]), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "(->)" [])]), (Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "baseType" [])]), (Node [(Edge "baseType" [])])])])]), (Edge "x" [(Node [(Edge "baseType" [])])]), (Edge "n" [(Node [(Edge "Int" [])])]), (Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 1]], PathEClass [Path [1, 2], Path [2, 2]]]))])]), (Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "Int" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [2, 1], Path [2, 2, 0]]]))])]), (Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 2, 1, 0]], PathEClass [Path [1, 2, 1], Path [1, 2, 2], Path [2, 1], Path [2, 2, 2]]]))])])]), (Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "baseType" [])]), (Node [(Edge "baseType" [])])])])]), (Edge "x" [(Node [(Edge "baseType" [])])]), (Edge "n" [(Node [(Edge "Int" [])])]), (Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 1]], PathEClass [Path [1, 2], Path [2, 2]]]))])]), (Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "Int" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [2, 1], Path [2, 2, 0]]]))])]), (Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 2, 1, 0]], PathEClass [Path [1, 2, 1], Path [1, 2, 2], Path [2, 1], Path [2, 2, 2]]]))])])])] (EqConstraints [PathEClass [Path [0], Path [2, 0, 2]], PathEClass [Path [1], Path [2, 0, 0]], PathEClass [Path [2, 0, 1], Path [3, 0]]]))]), (Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "baseType" [])]), (Node [(Edge "baseType" [])])])])]), (Edge "x" [(Node [(Edge "baseType" [])])]), (Edge "n" [(Node [(Edge "Int" [])])]), (Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 1]], PathEClass [Path [1, 2], Path [2, 2]]]))])]), (Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "Int" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [2, 1], Path [2, 2, 0]]]))])]), (Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 2, 1, 0]], PathEClass [Path [1, 2, 1], Path [1, 2, 2], Path [2, 1], Path [2, 2, 2]]]))])])])] (EqConstraints [PathEClass [Path [0], Path [2, 0, 2]], PathEClass [Path [1], Path [2, 0, 0]], PathEClass [Path [2, 0, 1], Path [3, 0]]])), (mkEdge "app" [(Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))]), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])]), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "(->)" [])]), (Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "baseType" [])]), (Node [(Edge "baseType" [])])])])]), (Edge "x" [(Node [(Edge "baseType" [])])]), (Edge "n" [(Node [(Edge "Int" [])])]), (Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 1]], PathEClass [Path [1, 2], Path [2, 2]]]))])]), (Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "Int" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [2, 1], Path [2, 2, 0]]]))])]), (Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 2, 1, 0]], PathEClass [Path [1, 2, 1], Path [1, 2, 2], Path [2, 1], Path [2, 2, 2]]]))])])]), (Node [(mkEdge "app" [(Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))]), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])]), (Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "(->)" [])]), (Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "baseType" [])]), (Node [(Edge "baseType" [])])])])]), (Edge "x" [(Node [(Edge "baseType" [])])]), (Edge "n" [(Node [(Edge "Int" [])])]), (Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 1]], PathEClass [Path [1, 2], Path [2, 2]]]))])]), (Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "Int" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [2, 1], Path [2, 2, 0]]]))])]), (Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 2, 1, 0]], PathEClass [Path [1, 2, 1], Path [1, 2, 2], Path [2, 1], Path [2, 2, 2]]]))])])]), (Node [(Edge "g" [(Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "baseType" [])]), (Node [(Edge "baseType" [])])])])]), (Edge "x" [(Node [(Edge "baseType" [])])]), (Edge "n" [(Node [(Edge "Int" [])])]), (Edge "$" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 1]], PathEClass [Path [1, 2], Path [2, 2]]]))])]), (Edge "replicate" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "Int" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [2, 1], Path [2, 2, 0]]]))])]), (Edge "foldr" [(Node [(mkEdge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])]), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])])), (Node [(Edge "->" [(Node [(Edge "(->)" [])]), (Node [(Edge "List" [(createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])]), (createMu $ \x -> (Node [(Edge "baseType" []), (Edge "->" [(Node [(Edge "(->)" [])]), x, x]), (Edge "Maybe" [x]), (Edge "List" [x])]))])])])])] (EqConstraints [PathEClass [Path [1, 1], Path [2, 2, 1, 0]], PathEClass [Path [1, 2, 1], Path [1, 2, 2], Path [2, 1], Path [2, 2, 2]]]))])])])] (EqConstraints [PathEClass [Path [0], Path [2, 0, 2]], PathEClass [Path [1], Path [2, 0, 0]], PathEClass [Path [2, 0, 1], Path [3, 0]]]))])] (EqConstraints [PathEClass [Path [0], Path [2, 0, 2]], PathEClass [Path [1], Path [2, 0, 0]], PathEClass [Path [2, 0, 1], Path [3, 0]]]))])]
    )

infiniteFNode :: Node Symbol
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
            (createMu (\x -> Node [Edge "f" [x]]) :: Node Symbol) `shouldBe` createMu (\x -> Node [Edge "f" [x]])

        it "keeps identities from different symbol alphabets distinct" $ do
            let typed = Node [Edge Zero []]
                textual = Node [Edge "Zero" []] :: Node Symbol
            nodeIdentity typed `shouldNotBe` nodeIdentity textual

    describe "ECTA-nodes" $ do
        it "equality constraints constrain" $
            getAllTerms ex1 `shouldSatisfy` ((== 2) . length)

        it "reduces paths constrained by equality constraints" $
            reducePartially ex2 `shouldBe` reducePartially ex1

        it "nodeRepresents requires exact term arity" $ do
            let n = Node [Edge "f" [constTerms ["a"], constTerms ["b"]]]
            nodeRepresents n (Term "f" [Term "a" [], Term "b" []]) `shouldBe` True
            nodeRepresents n (Term "f" [Term "a" []]) `shouldBe` False
            nodeRepresents n (Term "f" [Term "a" [], Term "b" [], Term "c" []]) `shouldBe` False

    describe "templates" $ do
        it "restricts a constrained language and lets equality narrow a hole" $ do
            let values = Node [Edge "a" [], Edge "b" []] :: Node Symbol
                pairs =
                    Node
                        [ mkEdge
                            "pair"
                            [values, values]
                            (mkEqConstraints [[path [0], path [1]]])
                        ]
                rightIsA = TemplateNode "pair" [Hole, TemplateNode "a" []]
            getAllTerms (termsMatching rightIsA pairs)
                `shouldBe` [Term "pair" [Term "a" [], Term "a" []]]

        it "distinguishes exact arity from an explicit prefix" $ do
            let call = Term "call" [Term "f" [], Term "x" []] :: Term Symbol
            matchesTemplate (TemplateNode "call" [Hole]) call `shouldBe` False
            matchesTemplate (TemplatePrefix "call" [TemplateNode "f" []]) call `shouldBe` True

        it "treats <v> as an ordinary symbol" $ do
            matchesTemplate (TemplateNode "<v>" []) (Term "<v>" [] :: Term Symbol) `shouldBe` True
            matchesTemplate (TemplateNode "<v>" []) (Term "other" [] :: Term Symbol) `shouldBe` False

        it "uses a typed alphabet without an IsString instance" $ do
            let zero = Node [Edge Zero []]
                naturals = Node [Edge Zero [], Edge Succ [zero]]
                successors = termsMatching (TemplateNode Succ [Hole]) naturals
                materialize = \case
                    ConcreteSymbol symbol -> symbol
                    UVarHole _ -> Recursion
                    TruncatedRecursion -> Recursion
            getAllTermsWith Recursion successors
                `shouldBe` [Term Succ [Term Zero []]]
            getAllTruncatedTerms successors
                `shouldBe` [Term (ConcreteSymbol Succ) [Term (ConcreteSymbol Zero) []]]
            map (fmap materialize) (getAllTruncatedTerms successors)
                `shouldBe` [Term Succ [Term Zero []]]

        it "restricting a finite ECTA agrees with filtering its terms" $
            property $
                mapSize (min 3) $ \(template :: Template Symbol) (node :: Node Symbol) ->
                    HashSet.fromList (getAllTerms $ termsMatching template node)
                        `shouldBe` HashSet.fromList (filter (matchesTemplate template) $ getAllTerms node)

    describe "intersection" $ do
        it "intersection commutes with getAllTerms" $
            property $
                mapSize (min 3) $ \(n1 :: Node Symbol) (n2 :: Node Symbol) ->
                    HashSet.fromList (getAllTerms $ intersect n1 n2)
                        `shouldBe` HashSet.intersection
                            (HashSet.fromList $ getAllTerms n1)
                            (HashSet.fromList $ getAllTerms n2)

        it "intersect is associative" $
            property $
                \(n1 :: Node Symbol) n2 n3 -> ((n1 `intersect` n2) `intersect` n3) == (n1 `intersect` (n2 `intersect` n3))

        it "intersect is commutative" $
            property $
                \(n1 :: Node Symbol) n2 -> intersect n1 n2 == intersect n2 n1

        it "intersect distributes over union" $
            property $
                \(n1 :: Node Symbol) n2 n3 -> intersect n1 (union [n2, n3]) == union [intersect n1 n2, intersect n1 n3]

        it "intersect is idempotent" $
            property $
                \(n1 :: Node Symbol) -> intersect n1 n1 == n1

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
            getAllTerms (intersect intTest5 intTest6) `shouldBe` [Term "g" [Term "a" [], Term "b" []]]

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
        it "reduction preserves getAllTerms" $
            property $
                mapSize (min 3) $
                    \(n :: Node Symbol) -> HashSet.fromList (getAllTerms n) `shouldBe` HashSet.fromList (getAllTerms $ reducePartially n)

        it "reducing a single constraint is idempotent 1" $
            property $ \(e :: Edge Symbol) ->
                let ns = edgeChildren e
                    ecs = edgeEcs e
                    ns' = reduceEqConstraints ecs EmptyConstraints ns
                 in ns' == reduceEqConstraints ecs EmptyConstraints ns'

        it "reducing a single constraint is idempotent 2" $
            let intersectingEdge :: Gen (Edge Symbol)
                intersectingEdge =
                    arbitrary `suchThatMap` \(e1, e2) -> intersectEdge e1 e2
             in forAll intersectingEdge $ \e' ->
                    let ns = edgeChildren e'
                        ecs = edgeEcs e'
                        ns' = reduceEqConstraints ecs EmptyConstraints ns
                     in ns' == reduceEqConstraints ecs EmptyConstraints ns'

        it "reducing a constraint is idempotent: buggy input 6/27/21" $ do
            pendingWith
                "Known non-idempotent reduction, open since 2021-06-29. The \
                \fixture below reproduces it; processing the eclasses in the \
                \reverse order makes no difference."
            let (ecs, ns) = bug062721NonIdempotentEqConstraintReduction
                ns' = reduceEqConstraints ecs EmptyConstraints ns
            ns' `shouldBe` reduceEqConstraints ecs EmptyConstraints ns'

        -- This is not obviously doable in one pass, but the test passes.
        it "leaf reduction means, for everything at a path, there is something matching at the other paths" $
            let liveConstrainedEdge :: Gen (Edge Symbol)
                liveConstrainedEdge =
                    arbitrary `suchThatMap` \edge ->
                        let reduced = reduceEdgeIntersection EmptyConstraints edge
                         in if reduced /= emptyEdge (edgeSymbol reduced) && edgeEcs reduced /= EmptyConstraints
                                then Just reduced
                                else Nothing
             in forAll liveConstrainedEdge $ \edge ->
                    let ns = edgeChildren edge
                     in and
                            [ intersect n1 n2 /= EmptyNode
                            | ec <- unsafeGetEclasses (edgeEcs edge)
                            , p1 <- unPathEClass ec
                            , p2 <- unPathEClass ec
                            , n1 <- getAllAtPath p1 ns
                            , let n2 = getPath p2 ns
                            ]

    describe "(un)folding" $ do
        it "unfolding a mu node once unfolds it once" $
            unfoldOuterRec infiniteFNode `shouldBe` (Node [Edge "f" [infiniteFNode]])

        it "recursive terms are unrolled to the depth of the constraints and no more" $
            let ecs = (mkEqConstraints [[path [0, 0, 0, 0], path [1, 0, 0]]])
                ns = [infiniteFNode, infiniteFNode]
                ns' = reduceEqConstraints ecs EmptyConstraints ns
                ns'' = reduceEqConstraints ecs EmptyConstraints ns'
                f = \n -> Node [Edge "f" [n]]
             in (ns' == ns'') && ns' == [f $ f $ f $ f infiniteFNode, f $ f $ f $ infiniteFNode] `shouldBe` True

        it "refold folds the simplest unrolled input" $
            refold (Node [Edge "f" [infiniteFNode]]) `shouldBe` infiniteFNode

    describe "traversals" $ do
        it "mapNodes hits each node exactly once" $
            -- Note: If the Arbitrary Node instance is changed to return empty or mu nodes, this will need to change
            property $ \(n :: Node Symbol) -> unsafePerformIO $ do
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
                    \(n :: Node Symbol) -> HashSet.fromList (getAllTerms n) `shouldBe` HashSet.fromList (getAllTerms $ reducePartially n)

    describe "degenerate inputs" $ do
        it "maxIndegree of a node with nothing to count is zero" $ do
            maxIndegree EmptyNode `shouldBe` 0
            maxIndegree (Node [Edge "a" []] :: Node Symbol) `shouldBe` 1
            maxIndegree ex3 `shouldBe` 2

        it "a non-positive unfold bound terminates" $ do
            getAllTerms (unfoldBounded 0 intTest7) `shouldBe` []
            getAllTerms (unfoldBounded (-1) intTest7) `shouldBe` []
            getAllTerms (unfoldBounded (-100) intTest7) `shouldBe` []

    describe "enumerating recursive automata" $ do
        -- A root Mu is never expanded, so before this was fixed getAllTerms
        -- reported the empty language and getAllTruncatedTerms raised.
        it "a bare Mu truncates instead of reporting an empty language" $ do
            getAllTerms intTest7 `shouldBe` [Term "Mu" []]
            getAllTruncatedTerms intTest7
                `shouldBe` [Term TruncatedRecursion []]

        it "a Mu under an edge truncates the same way" $
            getAllTerms (Node [Edge "wrap" [intTest7]])
                `shouldBe` [Term "wrap" [Term "Mu" []]]

        it "unfolding first enumerates past the recursion" $
            getAllTerms (unfoldBounded 2 intTest7)
                `shouldMatchList` [Term "a" [], Term "f" [Term "a" []]]

        it "a recursion with no base case unfolds to nothing" $
            getAllTerms (unfoldBounded 2 infiniteFNode) `shouldBe` []

    describe "dropping constraints" $ do
        it "an edge keeps its symbol and children" $ do
            let dropped = dropEdgeConstraints constrainedPair
            edgeSymbol dropped `shouldBe` edgeSymbol constrainedPair
            edgeChildren dropped `shouldBe` edgeChildren constrainedPair
            edgeEcs dropped `shouldBe` EmptyConstraints

        it "the language grows to every combination of children" $ do
            let constrained = Node [constrainedPair]
            length (getAllTerms constrained) `shouldBe` 2
            length (getAllTerms $ dropConstraints constrained) `shouldBe` 4

        it "the original language is retained" $ do
            let constrained = Node [constrainedPair]
                relaxed = HashSet.fromList $ getAllTerms $ dropConstraints constrained
            getAllTerms constrained `shouldSatisfy` all (`HashSet.member` relaxed)

    describe "pruning" $ do
        it "an oracle that never prunes enumerates the whole language" $
            HashSet.fromList (getAllTermsPrune () keepEverything searchNode)
                `shouldBe` HashSet.fromList (getAllTerms searchNode)

        it "rejecting the node before expansion drops the whole branch" $
            getAllTermsPrune () rejectEveryNode searchNode `shouldBe` []

        it "rejecting a produced fragment drops only that branch" $ do
            let oracle state _ (Left frag) = do
                    partial <- expandPartialTermFrag frag
                    return (partial == partialTerm (applied "f" "x"), state)
                oracle state _ (Right _) = return (False, state)
            HashSet.fromList (getAllTermsPrune () oracle searchNode)
                `shouldBe` HashSet.fromList
                    [applied "f" "y", applied "g" "x", applied "g" "y"]

        -- The pattern the pruning docs prescribe now that the library holds no
        -- pending-check state of its own: the oracle parks a check under the
        -- hole's representative and settles it when that hole is expanded.
        it "an oracle can suspend a check on a hole and settle it later" $ do
            let forbidden = partialTerm $ Term "f" [Term "T" []]

                oracle parkedChecks uv (Left frag) = do
                    rep <- uvarToInt <$> getUVarRepresentative uv
                    partial <- expandPartialTermFrag frag
                    case IntMap.lookup rep parkedChecks of
                        -- Settling a parked check: this hole is now concrete.
                        Just parked ->
                            return
                                ( any (== partial) parked
                                , IntMap.delete rep parkedChecks
                                )
                        Nothing -> do
                            holes <- mapM (fmap uvarToInt . getUVarRepresentative) (holesOf frag)
                            return
                                ( False
                                , foldr (\hole -> IntMap.insertWith (<>) hole [forbidden]) parkedChecks holes
                                )
                oracle parkedChecks _ (Right _) = return (False, parkedChecks)

                shared symbol = Term "filter" [wrapped symbol, wrapped symbol]
                wrapped symbol = Term symbol [Term "T" []]
            getAllTermsPrune IntMap.empty oracle sharedFilterNode `shouldBe` [shared "g"]

        it "an expansion order steers which hole is expanded first" $ do
            -- Rejects a branch whose first hole to become concrete is "x"-rooted.
            let oracle seen _ (Left frag) = do
                    partial <- expandPartialTermFrag frag
                    case (seen, partial) of
                        (Nothing, Term (ConcreteSymbol symbol) _)
                            | symbol `elem` holeSymbols ->
                                return (symbol == "x", Just symbol)
                        _ -> return (False, seen)
                oracle seen _ (Right _) = return (False, seen)
                holeSymbols = ["f", "g", "x", "y"] :: [Symbol]
                preferLast _ candidates = case reverse candidates of
                    uv : _ -> Just uv
                    [] -> Nothing
            -- The enumerator reaches the left hole first, which is never "x".
            length (getAllTermsPruneWith Nothing noExpansionPreference oracle twoHoleNode)
                `shouldBe` 4
            -- Steering to the last candidate reaches the right hole first.
            length (getAllTermsPruneWith Nothing preferLast oracle twoHoleNode)
                `shouldBe` 2

        it "a preference outside the candidates is ignored" $ do
            let preferAbsent _ _ = Just (intToUVar 9999)
            getAllTermsPruneWith () preferAbsent keepEverything twoHoleNode
                `shouldBe` getAllTerms twoHoleNode

    describe "counted nested Mu" $ do
        it "no Mu" $
            numNestedMu (Node [Edge "a" []] :: Node Symbol) `shouldBe` 0
        it "single Mu" $
            numNestedMu (Mu (\x -> Node [Edge "f" [x]]) :: Node Symbol) `shouldBe` 1
        it "two parallel Mus" $
            numNestedMu (Node [Edge "h" [Mu $ \x -> Node [Edge "g" [x]], Mu $ \x -> Node [Edge "h" [x]]]] :: Node Symbol) `shouldBe` 1
        it "nested" $
            numNestedMu (Mu (\x -> Node [Edge "f" [x], Edge "g" [Mu $ \y -> Node [Edge "g" [y]]]]) :: Node Symbol) `shouldBe` 2

    describe "redundant Mu" $ do
        it "redundant inner Mu is skipped even when its shape is already interned" $ do
            _ <- evaluate infiniteFNode
            let actual = Mu (\r1 -> Mu $ \_r2 -> Node [Edge "f" [r1]]) :: Node Symbol
                expected = Mu (\r1 -> Node [Edge "f" [r1]]) :: Node Symbol
            actual `shouldBe` expected

        it "redundant outer Mu is skipped" $
            (Mu (\_r1 -> Mu $ \r2 -> Node [Edge "f" [r2]]) :: Node Symbol)
                `shouldBe` (Mu $ \r1 -> Node [Edge "f" [r1]])

        it "two redundant Mus are both skipped" $
            (Mu (\_r1 -> Mu $ \_r2 -> Node [Edge "f" []]) :: Node Symbol)
                `shouldBe` Node [Edge "f" []]

        it "a used outer Mu is kept" $
            numNestedMu (Mu (\r1 -> Mu $ \_r2 -> Node [Edge "f" [r1]]) :: Node Symbol) `shouldBe` 1

        it "a used inner Mu is kept, and is not the same as reusing the outer one" $ do
            let nested = Mu (\r1 -> Mu $ \r2 -> Node [Edge "f" [r1], Edge "g" [r2]]) :: Node Symbol
                shared = Mu (\r1 -> Node [Edge "f" [r1], Edge "g" [r1]]) :: Node Symbol
            numNestedMu nested `shouldBe` 2
            nested `shouldNotBe` shared

        it "keeping a redundant Mu is what createMuDontCleanup is for" $
            numNestedMu (createMuDontCleanup (\_r -> Node [Edge "f" []]) :: Node Symbol) `shouldBe` 1

    describe "nested Mu" $
        it "references to different Mu nodes are not confused" $
            property $ do
                -- Two nodes with very similar structure
                -- We are precise about evaluation order here: what we are testing is that after the first term have been
                -- interned, we do /NOT/ reuse that term when interning the second. (If we /did/ confuse different references
                -- to 'Mu' nodes, @m@ looks precisely like the inner @Mu@ node of @n@.)
                n <- evaluate (Mu (\r1 -> Mu $ \r2 -> Node [Edge "f" [r1], Edge "g" [r2], Edge "a" []]) :: Node Symbol)
                m <- evaluate (Mu (\r -> Node [Edge "f" [r], Edge "g" [r], Edge "a" []]) :: Node Symbol)

                -- This is a low-level test; crush doesn't work, because we don't see what 'InternedMu' caches.
                let collectAllIds :: Node Symbol -> Set Int
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
intTest1 :: Node Symbol
intTest1 = Node [Edge "f" []]

-- | Two zero-argument terms
intTest2 :: Node Symbol
intTest2 = Node [Edge "f" [], Edge "g" []]

-- | Single one-argument term, two possible arguments
intTest3 :: Node Symbol
intTest3 = Node [Edge "f" [Node [Edge "a" [], Edge "b" []]]]

-- | Two one-argument terms, each two possible arguments (chosen from the same set)
intTest4 :: Node Symbol
intTest4 = Node [Edge "f" args, Edge "g" args]
  where
    args :: [Node Symbol]
    args = [arg]

    arg :: Node Symbol
    arg = Node [Edge "a" [], Edge "b" []]

-- | Two two-argument terms, no choice for arguments
intTest5 :: Node Symbol
intTest5 = Node [Edge "f" args, Edge "g" args]
  where
    args :: [Node Symbol]
    args = [argA, argB]

    argA, argB :: Node Symbol
    argA = Node [Edge "a" []]
    argB = Node [Edge "b" []]

-- | Two two-argument terms, same choice for arguments, but constrain the two arguments to be the same if choosing f
intTest6 :: Node Symbol
intTest6 = Node [mkEdge "f" args cs, Edge "g" args]
  where
    args :: [Node Symbol]
    args = [arg, arg]

    arg :: Node Symbol
    arg = Node [Edge "a" [], Edge "b" []]

    cs :: EqConstraints
    cs = mkEqConstraints [[path [0], path [1]]]

-- | f (f (f (... a)))
intTest7 :: Node Symbol
intTest7 = createMu $ \r -> Node [Edge "f" [r], Edge "a" []]

{- | A pair whose two children are forced equal.

Dropping that constraint admits every combination of them instead.
-}
constrainedPair :: Edge Symbol
constrainedPair =
    mkEdge
        "pair"
        [constTerms ["1", "2"], constTerms ["1", "2"]]
        (mkEqConstraints [[path [0], path [1]]])

{- | A node in the term-search encoding the pruning matcher reads.

An @app@ edge carries two leading type children followed by the function and
argument positions, and each term symbol carries its type.
-}
searchNode :: Node Symbol
searchNode = Node [Edge "app" [anyType, anyType, functions, arguments]]
  where
    functions = Node [Edge "f" [anyType], Edge "g" [anyType]]
    arguments = Node [Edge "x" [anyType], Edge "y" [anyType]]

anyType :: Node Symbol
anyType = Node [Edge "T" []]

-- | One accepted term of 'searchNode'.
applied :: Symbol -> Symbol -> Term Symbol
applied functionSymbol argumentSymbol =
    Term
        "app"
        [ Term "T" []
        , Term "T" []
        , Term functionSymbol [Term "T" []]
        , Term argumentSymbol [Term "T" []]
        ]

-- | Lift a concrete term into the alphabet used by partial enumeration.
partialTerm :: Term symbol -> Term (PartialSymbol symbol)
partialTerm (Term symbol children) =
    Term (ConcreteSymbol symbol) (map partialTerm children)

{- | A node with two independent holes, one per equality class.

Both are expandable at once after the root, so the order they are taken in is
observable.
-}
twoHoleNode :: Node Symbol
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
sharedFilterNode :: Node Symbol
sharedFilterNode =
    Node
        [ mkEdge
            "filter"
            [terms, terms]
            (mkEqConstraints [[path [0], path [1]]])
        ]
  where
    terms = Node [Edge "f" [anyType], Edge "g" [anyType]]

-- | The holes of a fragment.
holesOf :: TermFragment Symbol -> [UVar]
holesOf (TermFragmentNode _ children) = concatMap holesOf children
holesOf (TermFragmentUVar uv) = [uv]

-- | An oracle that keeps every branch.
keepEverything :: () -> UVar -> Either (TermFragment Symbol) (Node Symbol) -> EnumerateM Symbol (Bool, ())
keepEverything state _ _ = return (False, state)

-- | An oracle that rejects every node before it is expanded.
rejectEveryNode :: () -> UVar -> Either (TermFragment Symbol) (Node Symbol) -> EnumerateM Symbol (Bool, ())
rejectEveryNode state _ (Right _) = return (True, state)
rejectEveryNode state _ (Left _) = return (False, state)

-- | intTest7, once unrolled
intTest8 :: Node Symbol
intTest8 = unfoldOuterRec intTest7

-- | Like intTest7, but with an 'inner' unrolling: two f edges before recursing
intTest9 :: Node Symbol
intTest9 = createMu $ \r -> Node [Edge "f" [Node [Edge "f" [r], Edge "a" []]], Edge "a" []]

-- | Like intTest9, but with a single additional node on top (not an unrolling: this would result in /two/ additional nodes)
intTest10 :: Node Symbol
intTest10 = Node [Edge "f" [intTest9], Edge "a" []]

-- | Example with nested Mu: refer to outer Mu
intTest11 :: Node Symbol
intTest11 = createMuDontCleanup $ \r -> createMuDontCleanup $ \_r' -> Node [Edge "f" [r]]

{- | Example with nested Mu: refer to inner Mu

Both examples hold one redundant binder, which 'createMu' would drop, so they are built with
'createMuDontCleanup' to keep the nesting these cases are about.
-}
intTest12 :: Node Symbol
intTest12 = createMuDontCleanup $ \_r -> createMuDontCleanup $ \r' -> Node [Edge "f" [r']]
