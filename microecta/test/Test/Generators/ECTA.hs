{-# LANGUAGE OverloadedStrings #-}

module Test.Generators.ECTA () where

import Prelude hiding (max)

import Control.Monad (replicateM)
import Data.List (subsequences, (\\))

import Test.QuickCheck

import Data.ECTA
import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Paths
import Data.ECTA.Term

-----------------------------------------------------------------------------------------------

{- | Depth cap for generated nodes.

Enumerating every denotation of a node is exponential in its depth, so
properties that do that should @mapSize (min 3)@ on top of this.
-}
maxNodeDepth :: Int
maxNodeDepth = 5

capSize :: Int -> Gen a -> Gen a
capSize cap g = sized $ \n ->
    if n > cap
        then
            resize cap g
        else
            g

{- | Arbitrary nodes are non-recursive.

Nothing here produces a 'Mu', so no property below says anything about
recursive automata. That gap is why a root 'Mu' enumerating to the empty
language went unnoticed; those cases are covered by explicit examples in
"ECTASpec" instead.
-}
instance Arbitrary (Node Symbol) where
    arbitrary = capSize maxNodeDepth $ sized $ \_n -> do
        -- Edge arity, not the size parameter: the size drives depth, and the
        -- branching factor is kept small so denotation counts stay tractable.
        k <- chooseInt (1, 3)
        Node <$> replicateM k arbitrary

    shrink EmptyNode = []
    shrink (Node es) = [Node es' | s <- subsequences es \\ [es], es' <- mapM shrink s] ++ concatMap (\e -> edgeChildren e) es
    shrink (Mu _) = []
    shrink (Rec _) = []

testEdgeTypes :: [(Symbol, Int)]
testEdgeTypes =
    [ ("f", 1)
    , ("g", 2)
    , ("h", 1)
    , ("w", 3)
    , ("a", 0)
    , ("b", 0)
    , ("c", 0)
    ]

testConstants :: [Symbol]
testConstants = map fst $ filter ((== 0) . snd) testEdgeTypes

randPathPair :: [Node Symbol] -> Gen [Path]
randPathPair ns = do
    p1 <- randPath ns
    p2 <- randPath ns
    return [p1, p2]

randPath :: [Node Symbol] -> Gen Path
randPath [] = return EmptyPath
randPath ns = do
    i <- chooseInt (0, length ns - 1)
    case ns !! i of
        Node es -> do
            ns' <- edgeChildren <$> elements es
            b <- arbitrary
            if b then return (path [i]) else ConsPath i <$> randPath ns'
        _ -> error "randPath: generated child is not an ordinary node"

instance Arbitrary (Edge Symbol) where
    arbitrary =
        sized $ \n -> case n of
            0 -> Edge <$> elements testConstants <*> pure []
            _ -> do
                (sym, arity) <- elements testEdgeTypes
                ns <- replicateM arity (resize (n - 1) (arbitrary `suchThat` (/= EmptyNode)))
                numConstraintPairs <- elements [0, 0, 1, 1, 2, 3]
                ps <- replicateM numConstraintPairs (randPathPair ns)
                return $ mkEdge sym ns (mkEqConstraints ps)

    shrink e = mkEdge (edgeSymbol e) <$> (mapM shrink (edgeChildren e)) <*> pure (edgeEcs e)

instance Arbitrary (Template Symbol) where
    arbitrary = capSize maxNodeDepth $ sized $ \n ->
        if n == 0
            then elements [Hole, AnyNode [], AnyPrefix []]
            else do
                symbol <- fst <$> elements testEdgeTypes
                arity <- chooseInt (0, 3)
                children <- replicateM arity (resize (n - 1) arbitrary)
                elements
                    [ Hole
                    , AnyNode children
                    , TemplateNode symbol children
                    , AnyPrefix children
                    , TemplatePrefix symbol children
                    ]
