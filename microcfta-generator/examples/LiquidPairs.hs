{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}

-- | Generate pairs whose contract Z3 proves from what the pool says about each value.
module Main (main) where

import Control.Monad (unless)
import qualified Test.QuickCheck as QC

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Refinement.Expression (Expr, Formula, Refinement, (.&&), (.<), (.<=))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)

-- | Values that the solver knows only by the range that contains them.
ranged :: [(Integer, Refinement)]
ranged =
    [ (1, \v -> 0 .<= v .&& v .< 2)
    , (3, \v -> 2 .<= v .&& v .< 4)
    , (5, \v -> 4 .<= v .&& v .< 6)
    ]

-- | The contract of a pair: the left value is below the right value.
below :: Expr -> Expr -> Formula
below left right = left .< right

-- | Pairs whose ranges prove the contract.
pairs :: LTAGen.LTAGen (Integer, Integer)
pairs = LTAGen.guarded "pair" below $ LTAGen.do
    left <- LTAGen.pool ranged
    right <- LTAGen.pool ranged
    LTAGen.pure (left, right)

main :: IO ()
main = do
    unproved <- withZ3 [] $ \solver -> LTAGen.checkPool solver ranged
    unless (null unproved)
        $ fail
        $ "ranges that do not contain their values: " <> show unproved
    compiled <- LTAGen.compile pairs
    let expected = [(1, 3), (1, 5), (3, 5)]
        outcomes = LTAGen.values compiled
    unless (outcomes == Right expected)
        $ fail
        $ "unexpected ordered pairs: " <> show outcomes
    unless (all (< 2) $ LTAGen.shrinkRank compiled 2)
        $ fail
        $ "unexpected shrinks: "
            <> show (LTAGen.shrinkRank compiled 2)
    print outcomes
    result <-
        QC.quickCheckResult $
            LTAGen.forAll compiled (uncurry (<))
    unless (QC.isSuccess result) $
        fail "QuickCheck found an unordered pair"
    shrinkResult <-
        QC.quickCheckResult
            $ QC.expectFailure
            $ LTAGen.forAll compiled (== (1, 3))
    unless (QC.isSuccess shrinkResult) $
        fail "QuickCheck did not find the counterexample"
