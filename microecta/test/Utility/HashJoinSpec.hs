module Utility.HashJoinSpec (spec) where

import Data.List (nub, sort)

import Test.Hspec
import Test.QuickCheck

import Utility.HashJoin

-----------------------------------------------------------------

-- All three helpers assume an injective hash, so 'id' is a faithful stand-in
-- for the interned-id hashes the engine actually passes them.

spec :: Spec
spec = do
    describe "hash utilities" $ do
        it "nubByIdSinglePass is same as nub" $
            property $
                \(xs :: [Int]) -> sort (nub xs) == sort (nubByIdSinglePass id xs)

        it "clusterByHash partitions its input" $
            property $
                \(xs :: [Int]) -> sort (concat (clusterByHash id xs)) == sort xs

        it "clusterByHash puts equal elements in one cluster" $
            property $
                \(xs :: [Int]) ->
                    all (\cluster -> length (nub cluster) == 1) (clusterByHash id xs)

        it "hashJoin produces exactly the matching pairs" $
            property $
                \(xs :: [Int]) (ys :: [Int]) ->
                    sort (hashJoin id (,) xs ys)
                        == sort [(x, y) | x <- xs, y <- ys, x == y]
