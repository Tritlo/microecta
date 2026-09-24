{-# LANGUAGE TypeApplications #-}

-- | Construct, replay, and sample a finite ordinary tree language.
module Main (main) where

import Control.Monad (unless)
import qualified Data.Tree as Tree
import qualified Test.QuickCheck as QC

import qualified Data.CFTA.Gen.QuickCheck as FTAGen
import Data.CFTA.Generic (deriveFTAWith, domain)
import qualified Data.CFTA.Interned as Common
import Data.CFTA.Symbol (Symbol)

-- | All four ordered pairs of the leaf choices.
pairs :: FTAGen.FTAGen Symbol (Int, Int)
pairs =
    case deriveFTAWith @(Int, Int) $ domain @Int [0, 1] of
        Left err -> error $ show err
        Right datatype -> FTAGen.fromDatatypeUpToDepth 1 datatype

-- | Check all ranks, then check the sampled values.
main :: IO ()
main = do
    unless (FTAGen.cardinality pairs == Right 4) $ fail "wrong FTA count"
    let replayed = FTAGen.values pairs
    unless (replayed == Right [(0, 0), (0, 1), (1, 0), (1, 1)]) $
        fail "wrong FTA replay order"
    print replayed
    let leaf = Common.Node [Common.Edge "zero" [], Common.Edge "one" []] :: Common.PlainNode String
        graph = Common.Node [Common.Edge "pair" [leaf, leaf]]
        imported = FTAGen.fromAutomaton graph
    unless (FTAGen.cardinality imported == Right 4) $ fail "wrong interned FTA count"
    unless (FTAGen.unrank imported 3 == Right (Tree.Node "pair" [Tree.Node "one" [], Tree.Node "one" []])) $
        fail "wrong interned FTA replay"

    result <- QC.quickCheckResult $ FTAGen.forAll pairs $ \(left, right) ->
        left `elem` [0, 1] && right `elem` [0, 1]
    unless (QC.isSuccess result) $ fail "FTA property failed"
