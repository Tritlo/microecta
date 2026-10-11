{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.RefinementRelationSpec (spec) where

import Data.List (elemIndex)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Index (Cardinality (..), Rank (..), everyRank)
import Data.CFTA.Refinement (
    Entailment (entails),
    Verdict (..),
 )
import Data.CFTA.Refinement.Expression (
    Formula,
    false,
    lnot,
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
import Data.CFTA.Refinement.Lattice (latticeEntailment, pointAt, pointCount, pointRank, points)
import qualified Language.Fixpoint.Types as Fixpoint

spec :: Spec
spec = do
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
