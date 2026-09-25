{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}

-- | Count and sample sorted lists of integers up to a million, without enumeration.
module Main (main) where

import Control.Monad (unless)
import Data.List (sort)
import qualified Test.QuickCheck as QC

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Refinement.Expression ((.&&), (.<=), (.==))

{- | Non-decreasing lists of integers from zero to a million, of length up to
eight. The refinement of a list is its head. The head of the empty list is
above every element, so every element can come before it.
-}
sortedLists :: LTAGen.LTAGen [Integer]
sortedLists = LTAGen.recurUpTo 8 $ \rest -> LTAGen.oneof [nil, cons rest]
  where
    nil = LTAGen.leaf [] "nil" (.== 1000001)
    cons rest = LTAGen.guarded "cons" (\x t -> x .<= t) `LTAGen.ensuring` (\x _ -> x) $ LTAGen.do
        x <- LTAGen.every `LTAGen.satisfying` (\v -> 0 .<= v .&& v .<= 1000000)
        xs <- rest
        LTAGen.pure (x : xs)

-- | The binomial coefficient.
choose :: Integer -> Integer -> Integer
choose n k = product [n - k + 1 .. n] `div` product [1 .. k]

-- | Check the count against the closed form, and sample sorted lists.
main :: IO ()
main = do
    compiled <- LTAGen.compile sortedLists
    -- The non-decreasing lists of length at most k over m values number C(m + k, k).
    let expected = choose (1000001 + 8) 8
    unless (LTAGen.cardinality compiled == Right expected)
        $ fail
        $ "unexpected count: " <> show (LTAGen.cardinality compiled)
    print expected
    result <-
        QC.quickCheckResult $
            QC.conjoin
                [ LTAGen.forAll compiled $ \xs -> xs == sort xs && all (\x -> 0 <= x && x <= 1000000) xs && length xs <= 8
                , QC.forAll (LTAGen.toGenWithRank compiled) $ \(rank, xs) ->
                    LTAGen.unrank compiled rank == Right xs
                ]
    unless (QC.isSuccess result) $
        fail "sorted lists, their replay, or their shrinking failed"
