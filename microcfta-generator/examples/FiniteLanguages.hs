{-# LANGUAGE TypeApplications #-}

-- | Build finite FTA and ECTA generators, then check their ranks.
module Main (main) where

import Control.Monad (unless)
import qualified Test.QuickCheck as QC

import Data.CFTA.Equality.Constraint (EqConstraints (EmptyConstraints), mkEqConstraints)
import qualified Data.CFTA.Gen.Equality.QuickCheck as ECTAGen
import qualified Data.CFTA.Gen.QuickCheck as FTAGen
import Data.CFTA.Generic (TypedFTA, annotateDatatype, constructorFields, deriveFTAWith, domain)
import Data.CFTA.Path (path)
import Data.CFTA.Symbol (Symbol)

-- | One structural definition shared by ordinary and equality generation.
pairGrammar :: TypedFTA () (Int, Int)
pairGrammar = either (error . show) id $ deriveFTAWith @(Int, Int) $ domain @Int [0, 1]

-- | All four pairs in the derived datatype grammar.
pairs :: FTAGen.FTAGen Symbol (Int, Int)
pairs = FTAGen.fromDatatypeUpToDepth 1 pairGrammar

-- | Add equality at the tuple constructor while retaining its structure.
equalPairs :: ECTAGen.ECTAGen (Int, Int)
equalPairs = ECTAGen.fromDatatypeUpToDepth 1 $ annotateDatatype annotate pairGrammar
  where
    annotate constructor
        | length (constructorFields constructor) == 2 = mkEqConstraints [[path [0], path [1]]]
        | otherwise = EmptyConstraints

-- | Keep the pairs whose parity keys are equal.
sameParity :: ECTAGen.ECTAGen (Int, Int)
sameParity =
    ECTAGen.match
        (even ECTAGen.:==: even)
        (ECTAGen.elements [0 .. 3])
        (ECTAGen.elements [10 .. 13])

-- | Check all ranks, then use each compiled language in a property.
main :: IO ()
main = do
    unless (FTAGen.cardinality pairs == Right 4) $ fail "wrong FTA count"
    let replayed = FTAGen.values pairs
    unless (replayed == Right [(0, 0), (0, 1), (1, 0), (1, 1)]) $
        fail "wrong FTA replay order"
    unless (ECTAGen.cardinality equalPairs == Right 2) $ fail "wrong annotated ECTA count"
    unless (ECTAGen.cardinality sameParity == Right 8) $ fail "wrong ECTA count"
    print replayed
    print $ ECTAGen.unrank sameParity 0
    first <- QC.quickCheckResult $ QC.forAll (FTAGen.toGen pairs) $ \(left, right) ->
        left `elem` [0, 1] && right `elem` [0, 1]
    second <- QC.quickCheckResult $ ECTAGen.forAll sameParity $ \(left, right) ->
        even left == even right
    third <- QC.quickCheckResult $ ECTAGen.forAll equalPairs $ uncurry (==)
    unless (QC.isSuccess first && QC.isSuccess second && QC.isSuccess third) $ fail "property failed"
