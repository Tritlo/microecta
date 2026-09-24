{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}

-- | Divide by a denominator that the solver proves non-zero, then sample, replay, and shrink.
module Main (main) where

import Control.Monad (unless)
import qualified Test.QuickCheck as QC

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Refinement.Expression ((./=))

-- | Divide twelve by a denominator from zero to five that is not zero.
divisions :: LTAGen.LTAGen (Integer, Integer)
divisions = LTAGen.node "divide" $ LTAGen.do
    d <- LTAGen.elements [0 .. 5] `LTAGen.satisfying` (\v -> v ./= 0)
    LTAGen.pure (d, 12 `div` d)

-- | Check the accepted values, stable replay, and shrinking.
main :: IO ()
main = do
    compiled <- LTAGen.compile divisions
    let expected = [(1, 12), (2, 6), (3, 4), (4, 3), (5, 2)]
        replayed = LTAGen.values compiled
    unless (replayed == Right expected)
        $ fail
        $ "unexpected divisions: " <> show replayed
    unless (all (< 1) $ LTAGen.shrinkRank compiled 1) $
        fail "expected shrinks to earlier ranks"
    print expected
    result <-
        QC.quickCheckResult $
            QC.conjoin
                [ LTAGen.forAll compiled $ \(denominator, quotient) ->
                    denominator /= 0 && quotient == 12 `div` denominator
                , QC.forAll (LTAGen.toGenWithRank compiled) $ \(rank, division) ->
                    LTAGen.unrank compiled rank == Right division
                ]
    unless (QC.isSuccess result) $
        fail "division generation or replay failed"
