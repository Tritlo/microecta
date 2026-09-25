{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}

-- | Count red-black trees exactly by size, and sample them uniformly, with black heights as results.
module Main (main) where

import Control.Monad (unless)
import qualified Test.QuickCheck as QC

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Refinement.Expression ((.==))

-- | The shape of a red-black tree. The keys are the positions in order.
data Tree = Leaf | Black Tree Tree | Red Tree Tree
    deriving (Eq, Show)

{- | Red-black trees with a black root, unfolded a bounded number of times.
The refinement of a tree is its black height. The grammar keeps red children
black, and the contracts keep the black heights equal.
-}
redBlackTrees :: Int -> LTAGen.LTAGen Tree
redBlackTrees bound = LTAGen.recurUpTo bound $ \blackRooted ->
    let anyRooted = LTAGen.oneof [blackRooted, red blackRooted]
     in LTAGen.oneof [leaf, black anyRooted]
  where
    leaf = LTAGen.leaf Leaf "leaf" (.== 0)
    black, red :: LTAGen.LTAGen Tree -> LTAGen.LTAGen Tree
    black child = LTAGen.guarded "black" (\l r -> l .== r) `LTAGen.ensuring` (\l _ -> l + 1) $ LTAGen.do
        l <- child
        r <- child
        LTAGen.pure (Black l r)
    red child = LTAGen.guarded "red" (\l r -> l .== r) `LTAGen.ensuring` (\l _ -> l) $ LTAGen.do
        l <- child
        r <- child
        LTAGen.pure (Red l r)

-- | Whether a tree is a red-black tree with a black root.
valid :: Tree -> Bool
valid tree = black tree && balanced tree
  where
    black (Red _ _) = False
    black _ = True
    balanced Leaf = True
    balanced (Black l r) = balanced l && balanced r && height l == height r
    balanced (Red l r) = black l && black r && balanced l && balanced r && height l == height r
    height Leaf = 0 :: Int
    height (Black l _) = 1 + height l
    height (Red l _) = height l

-- | Check the counts by size against the known counts, and sample valid trees.
main :: IO ()
main = do
    compiled <- LTAGen.compile $ redBlackTrees 3
    -- A tree with n internal nodes has 2n + 1 nodes.
    let counts = [LTAGen.countAtSize compiled (2 * n + 1) | n <- [0 .. 10]]
        expected = map Right [1, 1, 2, 2, 4, 8, 16, 33, 56, 90, 164]
    unless (counts == expected)
        $ fail
        $ "unexpected counts: " <> show counts
    print (LTAGen.cardinality compiled)
    result <-
        QC.quickCheckResult $
            QC.conjoin
                [ LTAGen.forAll compiled valid
                , QC.forAll (LTAGen.toGenWithRank compiled) $ \(rank, tree) ->
                    LTAGen.unrank compiled rank == Right tree
                ]
    unless (QC.isSuccess result) $
        fail "red-black trees, their replay, or their shrinking failed"
