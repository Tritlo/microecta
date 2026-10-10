{-# LANGUAGE OverloadedStrings #-}

-- | Count red-black trees exactly by size and sample them, with black heights as measures.
module Main (main) where

-- A measure names each child, as in \leftHeight _ -> leftHeight, as a contract does.
{- HLINT ignore "Use const" -}

import Control.Monad (unless)
import Data.CFTA.Index (Depth (..))
import qualified Test.QuickCheck as QC

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Refinement.Expression ((.==))

-- | The shape of a red-black tree. The keys are the positions in order.
data Tree = Leaf | Black Tree Tree | Red Tree Tree
    deriving (Eq, Show)

{- | Red-black trees with a black root, unfolded a bounded number of times.
The measure of a tree is its black height. The grammar keeps red children
black, and the contracts keep the black heights equal.
-}
redBlackTrees :: Depth -> LTAGen.LTAGen Tree
redBlackTrees bound = LTAGen.recurUpTo bound $ \blackRooted ->
    let anyRooted = LTAGen.oneof [blackRooted, red blackRooted]
     in LTAGen.oneof [leaf, black anyRooted]
  where
    -- A leaf has black height zero.
    leaf = LTAGen.leaf Leaf "leaf" (.== 0)
    black, red :: LTAGen.LTAGen Tree -> LTAGen.LTAGen Tree
    -- The two subtrees have equal black heights, and a black node adds one.
    black child =
        LTAGen.measured
            "black"
            (\leftHeight rightHeight -> leftHeight .== rightHeight)
            (\leftHeight _ -> leftHeight + 1)
            (Black <$> child <*> child)
    -- A red node keeps the black height of its subtrees.
    red child =
        LTAGen.measured
            "red"
            (\leftHeight rightHeight -> leftHeight .== rightHeight)
            (\leftHeight _ -> leftHeight)
            (Red <$> child <*> child)

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
                , QC.forAll (LTAGen.toGenWithRank compiled) $ \(LTAGen.RankedValue rank tree) ->
                    LTAGen.unrank compiled rank == Right tree
                ]
    unless (QC.isSuccess result) $
        fail "red-black trees, their replay, or their shrinking failed"
