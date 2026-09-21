{- | QuickCheck integration for indexed ECTA generators.

This module re-exports "Data.CFTA.Gen.Equality" and its qualified
do-notation, and adds sampling, pools, and properties over QuickCheck.

A generator knows exactly how many values it has, and can be addressed by
rank:

>>> cardinality (elements [1 .. 4] :: ECTAGen Int)
Right 4
>>> unrank (elements "abcd" :: ECTAGen Char) 2
Right 'c'

Applicative composition multiplies the counts without building the product:

>>> let paired = liftA2 (,) (elements [0, 1 :: Int]) (elements "xy") :: ECTAGen (Int, Char)
>>> cardinality paired
Right 4
>>> map (unrank paired) [0 .. 3]
[Right (0,'x'),Right (0,'y'),Right (1,'x'),Right (1,'y')]

'match' keeps exactly the pairs whose projected keys agree, and counts them
without testing the product:

>>> let matched = match (even :==: even) (elements [0 .. 3 :: Int]) (elements [10 .. 13 :: Int]) :: ECTAGen (Int, Int)
>>> cardinality matched
Right 8
>>> unrank matched 0
Right (1,11)

Weights are exact rather than sampled:

>>> pmf (frequency [(3, elements [0 :: Int]), (1, elements [1])] :: ECTAGen Int)
Right [(0,3 % 4),(1,1 % 4)]

A recursive language has no cardinality, but every size class is counted and
ranks are size-major:

>>> let tree = recur (\self -> oneof [elements [[] :: [Int]], liftA2 (:) (elements [0, 1]) self]) :: ECTAGen [Int]
>>> map (countAtSize tree) [1 .. 4]
[Right 1,Right 2,Right 4,Right 8]
>>> unrank tree 3
Right [0,0]
-}
module Data.CFTA.Gen.Equality.QuickCheck (
    -- * Generators
    module Data.CFTA.Gen.Equality,

    -- * Pools
    samplePool,
    freeze,

    -- * Sampling and properties
    toGen,
    toGenWithRank,
    toGenEither,
    forAll,
    forAllWithLimit,
    smallerMemberLimit,
    sized,

    -- * Qualified do-notation
    module Data.CFTA.Gen.Do,
) where

import Data.CFTA.Gen.Do
import Data.CFTA.Gen.Equality
import Data.CFTA.Gen.QuickCheck (
    forAll,
    forAllWithLimit,
    freeze,
    samplePool,
    sized,
    smallerMemberLimit,
    toGen,
    toGenEither,
    toGenWithRank,
 )
