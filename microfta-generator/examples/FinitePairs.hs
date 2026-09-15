{-# LANGUAGE TypeApplications #-}

-- | Construct, replay, and sample a finite ordinary tree language.
module Main (main) where

import Control.Monad (unless)
import qualified Test.QuickCheck as QC

import qualified Data.Tree.FTA.Gen.QuickCheck as FTA
import Data.Tree.FTA.Generic (Constructor, deriveFTAWith, domain)
import qualified Data.Tree.FTA.Interned as Common
import qualified Data.Tree.Gen as Ranked
import Data.Tree.Term (Term (Term))

-- | All four ordered pairs of the leaf choices.
pairs :: FTA.FTAGen Constructor (Int, Int)
pairs =
    case deriveFTAWith @(Int, Int) $ domain @Int [0, 1] of
        Left err -> error $ show err
        Right datatype -> either (error . show) id $ FTA.fromDatatypeUpToDepth 1 datatype

-- | Check all ranks, then check the sampled values.
main :: IO ()
main = do
    unless (FTA.cardinality pairs == 4) $ fail "wrong FTA count"
    let replayed = traverse (FTA.unrank pairs) [0 .. 3]
    unless (replayed == Right [(0, 0), (0, 1), (1, 0), (1, 1)]) $
        fail "wrong FTA replay order"
    print replayed
    let leaf = Common.Node [Common.Edge "zero" [], Common.Edge "one" []] :: Common.PlainNode String
        graph = Common.Node [Common.Edge "pair" [leaf, leaf]]
    view <- either (fail . show) pure (Common.toFTA graph)
    imported <- either (fail . show) pure (FTA.fromFTA view)
    unless (Ranked.cardinality imported == 4) $ fail "wrong interned FTA count"
    unless (Ranked.unrank imported 3 == Right (Term "pair" [Term "one" [], Term "one" []])) $
        fail "wrong interned FTA replay"

    result <- QC.quickCheckResult $ FTA.forAll pairs $ \(left, right) ->
        left `elem` [0, 1] && right `elem` [0, 1]
    unless (QC.isSuccess result) $ fail "FTA property failed"
