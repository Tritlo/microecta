{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.RefinementRelationSpec (spec) where

import Control.Exception (IOException, try)
import Data.Either (isLeft)
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
import Data.CFTA.Refinement.Expression (
    Formula,
    false,
    lnot,
    refinementFormula,
    true,
    variable,
    (.&&),
    (./=),
    (.<),
    (.<=),
    (.==),
    (.>),
    (.>=),
    (.||),
 )
import Data.CFTA.Refinement.Guard (argument, contract, notGuard, withActualFor)
import Data.CFTA.Refinement.Lattice (latticeEntailment)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Symbol (valueName)
import qualified Data.CFTA.Term as Term
import qualified Language.Fixpoint.Types as Fixpoint

spec :: Spec
spec = do
    describe "semantic refinement comparison" $ do
        it "recognises strict subtyping" $
            withZ3 [(Fixpoint.symbol valueName, Fixpoint.FInt)] $ \solver ->
                refinementRelation solver (refinementFormula (\v -> v .== 0)) (refinementFormula (\v -> v .>= 0))
                    >>= (`shouldBe` StrictSubtype)

        it "recognises logical equivalence" $
            withZ3 [(Fixpoint.symbol valueName, Fixpoint.FInt)] $ \solver ->
                refinementRelation solver (refinementFormula (\v -> v .>= 0)) (refinementFormula (\v -> v .>= 0))
                    >>= (`shouldBe` Equivalent)

        it "does not merge incomparable refinements" $
            withZ3 [(Fixpoint.symbol valueName, Fixpoint.FInt)] $ \solver ->
                refinementRelation solver (refinementFormula (\v -> v .>= 0)) (refinementFormula (\v -> v ./= 0))
                    >>= (`shouldBe` Incomparable)

        it "answers each query after Z3 rejects one" $
            withZ3 [] $ \solver -> do
                let applied = Fixpoint.EApp (Fixpoint.EVar "f") (Fixpoint.EVar (Fixpoint.symbol valueName))
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
                let v = variable valueName
                    n = variable "n"
                    leaf name refinement = Term.Node (RefinedSymbol name refinement) []
                    -- Only a knows that n is at least zero, and the contract names only b.
                    pair = Term.Node (RefinedSymbol "pair" true) [leaf "a" (v .== n .&& n .>= 0), leaf "b" (v .== n + 1)]
                    positive = contract (\_ b -> b .> 0)
                evaluateConstraint solver positive pair >>= (`shouldBe` No)
                evaluateConstraint solver (notGuard positive) pair >>= (`shouldBe` No)
                evaluateConstraint solver (notGuard $ contract (\a _ -> a .< 0)) pair >>= (`shouldBe` Yes)
                -- The same contract after n replaces m in the refinement of b.
                let quad =
                        Term.Node
                            (RefinedSymbol "quad" true)
                            [leaf "a" (v .== n .&& n .>= 0), leaf "b" (v .== variable "m" + 1), leaf "m" true, leaf "n" true]
                    scoped = withActualFor (argument 3) (argument 2) $ contract (\_ b _ _ -> b .> 0)
                evaluateConstraint solver scoped quad >>= (`shouldBe` No)
                evaluateConstraint solver (notGuard scoped) quad >>= (`shouldBe` No)

        it "retains the antecedent when semantic intersection succeeds" $
            withZ3 [(Fixpoint.symbol valueName, Fixpoint.FInt)] $ \solver -> do
                let exactZero = refinementFormula (\v -> v .== 0)
                semanticIntersection solver exactZero (refinementFormula (\v -> v .>= 0))
                    >>= (`shouldBe` RetainedAntecedent exactZero)

        it "does not reverse a directional semantic intersection" $
            withZ3 [(Fixpoint.symbol valueName, Fixpoint.FInt)] $ \solver -> do
                let exactZero = refinementFormula (\v -> v .== 0)
                semanticIntersection solver (refinementFormula (\v -> v .>= 0)) exactZero
                    >>= (`shouldBe` BottomIntersection)

        it "reduces incomparable semantic transitions to bottom" $
            withZ3 [(Fixpoint.symbol valueName, Fixpoint.FInt)] $ \solver ->
                semanticIntersection solver (refinementFormula (\v -> v .>= 0)) (refinementFormula (\v -> v ./= 0))
                    >>= (`shouldBe` BottomIntersection)

    describe "lattice entailment" $ do
        it "decides each implication between two point cases as a search of every point and Z3 do" $
            withZ3 [(Fixpoint.symbol name, Fixpoint.FInt) | name <- ["x", "y" :: String]] $ \solver -> do
                let pairs = [(antecedent, consequent) | antecedent <- pointCases, consequent <- pointCases]
                    searched (_, antecedent) (_, consequent) =
                        if and [consequent a b | a <- [-3 .. 3], b <- [-3 .. 3], antecedent a b] then Yes else No
                    decide entailment = traverse (\((antecedent, _), (consequent, _)) -> entails entailment antecedent consequent) pairs
                counted <- decide latticeEntailment
                counted `shouldBe` map (uncurry searched) pairs
                decide solver >>= (`shouldBe` counted)

-- | Formulas over x and y in [-3, 3], each with the same test on integers.
pointCases :: [(Formula, Integer -> Integer -> Bool)]
pointCases =
    [ (box $ x ./= y, (/=))
    , (box $ lnot (x .< y), (>=))
    , (box $ Fixpoint.PImp (x .> 0) (y .> x), \a b -> a <= 0 || b > a)
    , (box $ Fixpoint.PIff (x .>= 0) (y .<= 1), \a b -> (a >= 0) == (b <= 1))
    , (box $ x .< -1 .|| y .== x + 1, \a b -> a < -1 || b == a + 1)
    , (box $ lnot (x .== 1 .|| y ./= 0), \a b -> not (a == 1 || b /= 0))
    , (box $ lnot (Fixpoint.PImp (x + y .<= 2) (x ./= 0)), \a b -> a + b <= 2 && a == 0)
    , (lnot (x .< -3 .|| x .> 3 .|| y .< -3 .|| y .> 3) .&& x ./= y, (/=))
    , (Fixpoint.PIff (x .>= -3) (x .<= 3) .&& Fixpoint.PImp (y .< -3 .|| y .> 3) false .&& x + y .> 0, \a b -> a + b > 0)
    ]
  where
    x = variable "x"
    y = variable "y"
    box formula = x .>= -3 .&& x .<= 3 .&& y .>= -3 .&& y .<= 3 .&& formula
