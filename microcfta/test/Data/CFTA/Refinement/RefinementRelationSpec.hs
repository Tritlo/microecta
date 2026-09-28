{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.RefinementRelationSpec (spec) where

import Control.Exception (IOException, try)
import Data.Either (isLeft)
import Data.List (elemIndex)
import qualified Data.Tree as Tree
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import Data.CFTA.Index (Cardinality (..), Rank (..), everyRank)
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
import Data.CFTA.Refinement.Lattice (latticeEntailment, pointAt, pointCount, pointRank, points)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import qualified Language.Fixpoint.Types as Fixpoint

spec :: Spec
spec = do
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

    describe "integer points" $ do
        it "counts and decodes each formula as a search of every point does" $
            [(formula, decoded ["x", "y"] formula) | (formula, _) <- pointCases]
                `shouldBe` [ (formula, Right [[a, b] | a <- [-3 .. 3], b <- [-3 .. 3], holds a b])
                           | (formula, holds) <- pointCases
                           ]

        it "ranks each point that a formula admits, and no other point" $
            [(formula, ranked formula) | (formula, _) <- pointCases]
                `shouldBe` [ (formula, Right [Rank . toInteger <$> elemIndex (a, b) (members holds) | a <- [-4 .. 4], b <- [-4 .. 4]])
                           | (formula, holds) <- pointCases
                           ]

        it "decodes points beyond 2^256 by count, first rank, and last rank" $ do
            let big = 2 ^ (300 :: Int) :: Integer
                ends formula = do
                    found <- points ["x"] formula
                    let Cardinality count = pointCount found
                    pure (count, pointAt found 0, pointAt found $ Rank $ count - 1)
            ends (lnot (x .< fromInteger big) .&& x .<= fromInteger (big + 5)) `shouldBe` Right (6, [big], [big + 5])
            ends (fromInteger (negate big) .<= x .&& x .<= fromInteger big) `shouldBe` Right (2 * big + 1, [negate big], [big])

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

        it "decides an implication whatever the names of its variables" $ do
            -- One order of a and b sums out the variable with coefficient two
            -- first and cannot count; the other order can.
            let a = variable "a"
                b = variable "b"
            forward <- entails latticeEntailment (0 .<= a .&& a .<= 5 .&& 0 .<= b .&& 2 * a + b .<= 10) (b .<= 5)
            swapped <- entails latticeEntailment (0 .<= b .&& b .<= 5 .&& 0 .<= a .&& 2 * b + a .<= 10) (a .<= 5)
            (forward, swapped) `shouldBe` (No, No)

        it "answers Unknown where a variable has no bound or a term is not linear" $ do
            let y = variable "y"
            verdicts <-
                traverse
                    (uncurry $ entails latticeEntailment)
                    [ (true, x .>= 0)
                    , (x .>= 0, x .>= -1)
                    , (x .>= 0 .&& x .<= 2 .&& y .>= 0 .&& y .<= 2, x * y .>= 0)
                    , (1 .< 2, 2 .< 3)
                    ]
            -- The second one is decided: x >= 0 and x < -1 bound x from both sides.
            verdicts `shouldBe` [Unknown, Yes, Unknown, Yes]
  where
    x = variable "x"
    decoded names formula = do
        found <- points names formula
        pure [pointAt found rank | rank <- everyRank $ pointCount found]
    ranked formula = do
        found <- points ["x", "y"] formula
        pure [pointRank found [a, b] | a <- [-4 .. 4], b <- [-4 .. 4]]
    members holds = [(a, b) | a <- [-3 .. 3], b <- [-3 .. 3], holds a b]

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
