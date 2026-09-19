{-# LANGUAGE TypeApplications #-}

-- | Build finite FTA and ECTA generators, then check their ranks.
module Main (main) where

import Control.Monad (unless)
import qualified Test.QuickCheck as QC

import Data.CFTA.Constraint.Equality (EqConstraints (EmptyConstraints), mkEqConstraints)
import qualified Data.CFTA.Gen.Equality.QuickCheck as ECTA
import qualified Data.CFTA.Gen.QuickCheck as FTA
import Data.CFTA.Generic (Constructor, TypedFTA, annotateDatatype, constructorFields, deriveFTAWith, domain)
import Data.CFTA.Path (path)

-- | One structural definition shared by ordinary and equality generation.
pairGrammar :: TypedFTA () (Int, Int)
pairGrammar = either (error . show) id $ deriveFTAWith @(Int, Int) $ domain @Int [0, 1]

-- | All four pairs in the derived datatype grammar.
pairs :: FTA.FTAGen Constructor (Int, Int)
pairs = either (error . show) id $ FTA.fromDatatypeUpToDepth 1 pairGrammar

-- | Add equality at the tuple constructor while retaining its structure.
equalPairs :: ECTA.ECTAGen (Int, Int)
equalPairs = ECTA.fromDatatypeUpToDepth 1 $ annotateDatatype annotate pairGrammar
  where
    annotate constructor
        | length (constructorFields constructor) == 2 = mkEqConstraints [[path [0], path [1]]]
        | otherwise = EmptyConstraints

-- | Keep the pairs whose parity keys are equal.
sameParity :: ECTA.ECTAGen (Int, Int)
sameParity =
    ECTA.match
        (even ECTA.:==: even)
        (ECTA.elements [0 .. 3])
        (ECTA.elements [10 .. 13])

-- | Check all ranks, then use each compiled language in a property.
main :: IO ()
main = do
    unless (FTA.cardinality pairs == 4) $ fail "wrong FTA count"
    let replayed = traverse (FTA.unrank pairs) [0 .. 3]
    unless (replayed == Right [(0, 0), (0, 1), (1, 0), (1, 1)]) $
        fail "wrong FTA replay order"
    unless (ECTA.cardinality equalPairs == Right 2) $ fail "wrong annotated ECTA count"
    unless (ECTA.cardinality sameParity == Right 8) $ fail "wrong ECTA count"
    print replayed
    print $ ECTA.unrank sameParity 0
    first <- QC.quickCheckResult $ QC.forAll (FTA.toGen pairs) $ \(left, right) ->
        left `elem` [0, 1] && right `elem` [0, 1]
    second <- QC.quickCheckResult $ ECTA.forAll sameParity $ \(left, right) ->
        even left == even right
    third <- QC.quickCheckResult $ ECTA.forAll equalPairs $ uncurry (==)
    unless (QC.isSuccess first && QC.isSuccess second && QC.isSuccess third) $ fail "property failed"
