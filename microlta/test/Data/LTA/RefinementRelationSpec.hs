module Data.LTA.RefinementRelationSpec (spec) where

import Test.Hspec (Spec, describe, it, shouldBe)

import Data.LTA (
    RefinementRelation (..),
    SemanticIntersection (..),
    refinementRelation,
    semanticIntersection,
 )
import Data.LTA.LiquidFixpoint (withZ3)
import Data.LTA.Refinement (value, (./=.), (.==.), (.>=.))
import qualified Language.Fixpoint.Types as Fixpoint

spec :: Spec
spec =
    describe "semantic refinement comparison" $ do
        it "recognises strict subtyping" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver ->
                refinementRelation solver (value .==. (0 :: Int)) (value .>=. (0 :: Int))
                    >>= (`shouldBe` StrictSubtype)

        it "recognises logical equivalence" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver ->
                refinementRelation solver (value .>=. (0 :: Int)) (value .>=. (0 :: Int))
                    >>= (`shouldBe` Equivalent)

        it "does not merge incomparable refinements" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver ->
                refinementRelation solver (value .>=. (0 :: Int)) (value ./=. (0 :: Int))
                    >>= (`shouldBe` Incomparable)

        it "retains the antecedent when semantic intersection succeeds" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver -> do
                let exactZero = value .==. (0 :: Int)
                semanticIntersection solver exactZero (value .>=. (0 :: Int))
                    >>= (`shouldBe` RetainedAntecedent exactZero)

        it "does not reverse a directional semantic intersection" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver -> do
                let exactZero = value .==. (0 :: Int)
                semanticIntersection solver (value .>=. (0 :: Int)) exactZero
                    >>= (`shouldBe` BottomIntersection)

        it "reduces incomparable semantic transitions to bottom" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver ->
                semanticIntersection solver (value .>=. (0 :: Int)) (value ./=. (0 :: Int))
                    >>= (`shouldBe` BottomIntersection)
