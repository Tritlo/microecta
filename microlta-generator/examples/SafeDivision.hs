{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}

-- | Compile a division precondition, then sample, replay, and shrink safely.
module Main (main) where

import Control.Monad (unless)
import qualified Test.QuickCheck as QC

import Data.CFTA.Refinement (Refinement)
import Data.CFTA.Refinement.Expression (integer, value, variable, (./=.), (.==.))
import Data.CFTA.Refinement.Guard (requires)
import Data.CFTA.Refinement.LiquidFixpoint (integerDeclarations, withZ3Assuming)
import qualified Data.LTA.Gen.QuickCheck as LTA

-- | The refinement used by the division precondition.
nonZero :: Refinement
nonZero = value ./=. integer 0

{- | Candidate denominators and their caller-supplied refinements.

The caller must ensure that each annotation describes its Haskell value.
LTA checks refinement implication. It does not inspect a value to prove its
annotation. The ambient assumption in 'main' fixes the named input at two.
-}
denominators :: LTA.LTAGen Integer
denominators =
    LTA.pool
        [ LTA.refined 0 "zero" (value .==. integer 0)
        , LTA.refined 1 "nonzero" nonZero
        , LTA.refined 2 "input" (value .==. variable "input")
        ]

-- | Reject the zero denominator before evaluating the division.
divisions :: LTA.LTAGen (Integer, Integer)
divisions = LTA.node "divide" (`requires` nonZero) $ LTA.do
    denominator <- denominators
    LTA.pure (denominator, 12 `div` denominator)

-- | Check accepted values, stable replay, and refinement-based shrinking.
main :: IO ()
main =
    -- 'value' means the refinement variable "v". 'variable "input"' names
    -- another expression. Declare both sorts before asking the solver.
    withZ3Assuming
        (integerDeclarations ["v", "input"])
        [variable "input" .==. integer 2]
        $ \solver -> do
            compiled <- LTA.compile solver divisions >>= either (fail . LTA.explain) pure
            unless (LTA.cardinality compiled > 1) $
                fail "expected more than one accepted division"
            let expected = [(1, 12), (2, 6)]
                replayed =
                    traverse
                        (fmap LTA.generatedValue . (LTA.unrank compiled))
                        [0 .. LTA.cardinality compiled - 1]
            unless (replayed == Right expected)
                $ fail
                $ "unexpected replayed divisions: " <> show replayed
            unless (LTA.shrinkRank compiled 1 == [0]) $
                fail "expected the exact input refinement to shrink to nonzero"
            print expected
            result <-
                QC.quickCheckResult $
                    QC.conjoin
                        [ LTA.forAll compiled $ \(denominator, quotient) ->
                            denominator /= 0 && quotient == 12 `div` denominator
                        , QC.forAll (LTA.toGenWithRank compiled) $ \(rank, division) ->
                            fmap LTA.generatedValue (LTA.unrank compiled rank) == Right division
                        ]
            unless (QC.isSuccess result) $
                fail "division generation or replay failed"
