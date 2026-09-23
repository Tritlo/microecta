{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.RefinementRelationSpec (spec) where

import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Refinement (
    RefinementRelation (..),
    SemanticIntersection (..),
    refinementRelation,
    semanticIntersection,
 )
import Data.CFTA.Refinement.Expression (refinementFormula, (./=), (.==), (.>=))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import qualified Language.Fixpoint.Types as Fixpoint

spec :: Spec
spec =
    describe "semantic refinement comparison" $ do
        it "recognises strict subtyping" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver ->
                refinementRelation solver (refinementFormula (\v -> v .== 0)) (refinementFormula (\v -> v .>= 0))
                    >>= (`shouldBe` StrictSubtype)

        it "recognises logical equivalence" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver ->
                refinementRelation solver (refinementFormula (\v -> v .>= 0)) (refinementFormula (\v -> v .>= 0))
                    >>= (`shouldBe` Equivalent)

        it "does not merge incomparable refinements" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver ->
                refinementRelation solver (refinementFormula (\v -> v .>= 0)) (refinementFormula (\v -> v ./= 0))
                    >>= (`shouldBe` Incomparable)

        it "retains the antecedent when semantic intersection succeeds" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver -> do
                let exactZero = refinementFormula (\v -> v .== 0)
                semanticIntersection solver exactZero (refinementFormula (\v -> v .>= 0))
                    >>= (`shouldBe` RetainedAntecedent exactZero)

        it "does not reverse a directional semantic intersection" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver -> do
                let exactZero = refinementFormula (\v -> v .== 0)
                semanticIntersection solver (refinementFormula (\v -> v .>= 0)) exactZero
                    >>= (`shouldBe` BottomIntersection)

        it "reduces incomparable semantic transitions to bottom" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver ->
                semanticIntersection solver (refinementFormula (\v -> v .>= 0)) (refinementFormula (\v -> v ./= 0))
                    >>= (`shouldBe` BottomIntersection)
