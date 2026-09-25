{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}

-- | Read a buffer below its length, with a million lengths, counted without enumeration.
module Main (main) where

import Control.Monad (unless)
import qualified Test.QuickCheck as QC

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Refinement.Expression ((.&&), (.<), (.<=))

-- | A length from one to a million, and an index below it.
boundedReads :: LTAGen.LTAGen (Integer, Integer)
boundedReads = LTAGen.guarded "read-at" (\n i -> 0 .<= i .&& i .< n) $ LTAGen.do
    n <- LTAGen.every `LTAGen.satisfying` (\v -> 1 .<= v .&& v .<= 1000000)
    i <- LTAGen.every `LTAGen.satisfying` (\v -> (-10) .<= v .&& v .<= 1000000)
    LTAGen.pure (n, i)

-- | Check the count, the rank order, replay, and shrinking.
main :: IO ()
main = do
    compiled <- LTAGen.compile boundedReads
    let total = LTAGen.cardinality compiled
    unless (total == Right 500000500000)
        $ fail
        $ "unexpected count: " <> show total
    let ends = (LTAGen.unrank compiled 0, LTAGen.unrank compiled 499999999999, LTAGen.unrank compiled 500000499999)
    unless (ends == (Right (1, 0), Right (1000000, 499999), Right (1000000, 999999)))
        $ fail
        $ "unexpected rank order: " <> show ends
    unless (all (< 7) $ LTAGen.shrinkRank compiled 7) $
        fail "expected shrinks to earlier ranks"
    print total
    result <-
        QC.quickCheckResult $
            QC.conjoin
                [ LTAGen.forAll compiled $ \(n, i) -> 1 <= n && n <= 1000000 && 0 <= i && i < n
                , QC.forAll (LTAGen.toGenWithRank compiled) $ \(rank, pair) ->
                    LTAGen.unrank compiled rank == Right pair
                ]
    unless (QC.isSuccess result) $
        fail "bounded reads, their replay, or their shrinking failed"
