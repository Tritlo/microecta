{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.RefinementRelationSpec (spec) where

import Control.Exception (IOException, try)
import Data.Either (isLeft)
import qualified Data.Tree as Tree
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import Data.CFTA.Refinement (
    Entailment (entails),
    RefinementRelation (..),
    SemanticIntersection (..),
    Symbol (RefinedSymbol),
    Verdict (..),
    evaluateConstraint,
    refinementRelation,
    semanticIntersection,
 )
import Data.CFTA.Refinement.Expression (refinementFormula, true, variable, (.&&), (./=), (.<), (.==), (.>), (.>=))
import Data.CFTA.Refinement.Guard (argument, contract, notGuard, withActualFor)
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

        it "answers each query after Z3 rejects one" $
            withZ3 [] $ \solver -> do
                let applied = Fixpoint.EApp (Fixpoint.EVar "f") (Fixpoint.EVar "v")
                rejected <-
                    try $
                        entails
                            solver
                            (Fixpoint.PAtom Fixpoint.Eq applied (Fixpoint.ECon (Fixpoint.I 1)))
                            (Fixpoint.PAtom Fixpoint.Gt applied (Fixpoint.ECon (Fixpoint.I 0)))
                (rejected :: Either IOException Verdict) `shouldSatisfy` isLeft
                entails solver (refinementFormula (.== 0)) (refinementFormula (.>= 0)) >>= (`shouldBe` Yes)
                entails solver (refinementFormula (.== 0)) (refinementFormula (.== 1)) >>= (`shouldBe` No)

        it "holds a negated contract only when the refinements refute it" $
            withZ3 [] $ \solver -> do
                let v = variable "v"
                    n = variable "n"
                    leaf name refinement = Tree.Node (RefinedSymbol name refinement) []
                    -- Only a knows that n is at least zero, and the contract names only b.
                    pair = Tree.Node (RefinedSymbol "pair" true) [leaf "a" (v .== n .&& n .>= 0), leaf "b" (v .== n + 1)]
                    positive = contract (\_ b -> b .> 0)
                evaluateConstraint solver positive pair >>= (`shouldBe` No)
                evaluateConstraint solver (notGuard positive) pair >>= (`shouldBe` No)
                evaluateConstraint solver (notGuard $ contract (\a _ -> a .< 0)) pair >>= (`shouldBe` Yes)
                -- The same contract after n replaces m in the refinement of b.
                let quad =
                        Tree.Node
                            (RefinedSymbol "quad" true)
                            [leaf "a" (v .== n .&& n .>= 0), leaf "b" (v .== variable "m" + 1), leaf "m" true, leaf "n" true]
                    scoped = withActualFor (argument 3) (argument 2) $ contract (\_ b _ _ -> b .> 0)
                evaluateConstraint solver scoped quad >>= (`shouldBe` No)
                evaluateConstraint solver (notGuard scoped) quad >>= (`shouldBe` No)

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
