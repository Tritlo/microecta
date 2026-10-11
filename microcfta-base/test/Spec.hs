{- | The contract of the rank arithmetic.

A product language ranks a pair in mixed radix, and a choice gives each group
a block of ranks after the groups before it. The ranked layer and the
generators rely on these maps being exact inverses on valid ranks. The Lean
model states the same facts as @split_pair@, @pair_split@, @pairRank_lt@, and
@offset_interval@.
-}
module Main (main) where

import Test.Hspec (describe, hspec, it, shouldBe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (NonNegative (..), Positive (..), (==>))

import Data.CFTA.Index

main :: IO ()
main = hspec $ do
    describe "pairRank and splitRank" $ do
        prop "splitRank undoes pairRank on valid ranks" $
            \(NonNegative first) (Positive radix) (NonNegative second) ->
                second < radix ==>
                    splitRank (Cardinality radix) (pairRank (Cardinality radix) (Rank first) (Rank second))
                        == (Rank first, Rank second)

        prop "pairRank undoes splitRank" $
            \(NonNegative rank) (Positive radix) ->
                let (first, second) = splitRank (Cardinality radix) (Rank rank)
                 in pairRank (Cardinality radix) first second == Rank rank

        prop "a pair of valid ranks is a valid rank of the product" $
            \(NonNegative first) (Positive firstCount) (NonNegative second) (Positive radix) ->
                first < firstCount && second < radix ==>
                    hasRank (Cardinality $ firstCount * radix) (pairRank (Cardinality radix) (Rank first) (Rank second))

    describe "offsetRank and rebaseRank" $ do
        prop "rebaseRank undoes offsetRank" $
            \offset rank -> rebaseRank (RankOffset offset) (offsetRank (RankOffset offset) (Rank rank)) == Rank rank

        prop "a valid rank of a group lies in the block of the group" $
            \(NonNegative offset) (NonNegative rank) (Positive count) ->
                rank < count ==>
                    let RankOffset start = RankOffset offset
                        RankOffset end = nextOffset (RankOffset offset) (Cardinality count)
                        Rank shifted = offsetRank (RankOffset offset) (Rank rank)
                     in start <= shifted && shifted < end

        prop "classMemberRank adds the rank in the class to the first rank of the class" $
            \offset rank -> classMemberRank (RankOffset offset) (ClassRank rank) == offsetRank (RankOffset offset) (Rank rank)

    describe "everyRank and hasRank" $
        prop "everyRank lists exactly the valid ranks, in order" $
            \(NonNegative count) ->
                everyRank (Cardinality count) == filter (hasRank $ Cardinality count) (map Rank [-2 .. count + 2])

    describe "childIndexes"
        $ it "lists the child indexes from zero"
        $ childIndexes (Arity 3) `shouldBe` map ChildIndex [0, 1, 2]
