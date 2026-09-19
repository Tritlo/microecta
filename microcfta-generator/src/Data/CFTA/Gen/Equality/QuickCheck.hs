{- | QuickCheck integration for indexed ECTA generators.

This module re-exports "Data.CFTA.Gen.Equality" and its qualified
do-notation, and adds sampling, pools, and properties over QuickCheck.

A generator knows exactly how many values it has, and can be addressed by
rank:

>>> cardinality (elements [1 .. 4 :: Int])
Right 4
>>> unrank (elements "abcd") 2
Right 'c'

Applicative composition multiplies the counts without building the product:

>>> let paired = liftA2 (,) (elements [0, 1 :: Int]) (elements "xy")
>>> cardinality paired
Right 4
>>> map (unrank paired) [0 .. 3]
[Right (0,'x'),Right (0,'y'),Right (1,'x'),Right (1,'y')]

'match' keeps exactly the pairs whose projected keys agree, and counts them
without testing the product:

>>> let matched = match (even :==: even) (elements [0 .. 3 :: Int]) (elements [10 .. 13 :: Int])
>>> cardinality matched
Right 8
>>> unrank matched 0
Right (1,11)

Weights are exact rather than sampled:

>>> pmf (frequency [(3, elements [0 :: Int]), (1, elements [1])])
Right [(0,3 % 4),(1,1 % 4)]

A recursive language has no cardinality, but every size class is counted and
ranks are size-major:

>>> let tree = recur (\self -> oneof [elements [[] :: [Int]], liftA2 (:) (elements [0, 1]) self])
>>> map (countAtSize tree) [1 .. 4]
[Right 1,Right 2,Right 4,Right 8]
>>> unrank tree 3
Right [0,0]
-}
module Data.CFTA.Gen.Equality.QuickCheck (
    -- * Generators
    module Data.CFTA.Gen.Equality,

    -- * Pools
    pool,
    freeze,

    -- * Sampling and properties
    toGen,
    toGenWithRank,
    toGenEither,
    toGenWithRankEither,
    forAll,
    forAllWithLimit,
    smallerMemberLimit,
    sized,

    -- * Qualified do-notation
    module Data.CFTA.Gen.Equality.Do,
) where

import Data.Maybe (fromMaybe)
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import Data.CFTA.Gen.Equality
import Data.CFTA.Gen.Equality.Do

{- | Sample a finite pool from an ordinary QuickCheck generator.

The outer 'QC.Gen' draws the pool once. The resulting 'ECTAGen' is finite and
transparent, so it supports exact inspection, matching, relations, replay, and
ECTA-aware shrinking. Repeated draws remain repeated ranks and retain the
native generator's empirical weight. A non-positive pool size produces an
empty generator.
-}
pool :: Int -> QC.Gen a -> QC.Gen (ECTAGen a)
pool sampleCount native =
    elements <$> QC.vectorOf (max 0 sampleCount) native

{- | 'pool' with the draws fixed by a seed.

The native generator is run once, at QuickCheck size 30 (the default of
'QC.generate'), so the result is an ordinary transparent generator: it can be
weighted by 'uniformly', keyed, joined, replayed, and shrunk, and its ranks are
the same in every run under the same seed. That is the trade against 'pool',
which draws afresh each time its outer 'QC.Gen' runs. Use 'QC.resize' on the
native generator for another size.
-}
freeze :: Int -> Int -> QC.Gen a -> ECTAGen a
freeze seed sampleCount native =
    unGen (pool sampleCount native) (mkQCGen seed) 30

{- | Sample a non-recursive generator while retaining structured generator errors.

Unlike 'toGen', this does not bound a recursive generator from QuickCheck's
size parameter; apply 'upToSize' explicitly first.
-}
toGenEither :: ECTAGen a -> QC.Gen (Either GenError a)
toGenEither = lower

{- | Sample a finite transparent generator while retaining its stable rank and
errors.

Unlike 'toGenWithRank', this does not bound a recursive generator from
QuickCheck's size parameter; apply 'upToSize' explicitly first.
-}
toGenWithRankEither :: ECTAGen a -> QC.Gen (Either GenError (Integer, a))
toGenWithRankEither = lowerWithRank

{- | Sample through the generator type expected by QuickCheck.

Recursive generators are bounded by QuickCheck's size parameter.
-}
toGen :: ECTAGen a -> QC.Gen a
toGen generator
    | isRecursive generator = QC.sized $ \size -> bounded !! max 0 size
    | Just direct <- lowerUniform generator = direct
    | otherwise = either (raise "toGen") id <$> toGenEither generator
  where
    bounded = [toGen (upToSize (max firstSize size) generator) | size <- [0 ..]]
    firstSize = either (raise "toGen") (fromMaybe 1) $ minimumSize generator

{- | Sample an inspectable generator together with its stable replay rank.

Recursive generators are bounded by QuickCheck's size parameter.
-}
toGenWithRank :: ECTAGen a -> QC.Gen (Integer, a)
toGenWithRank generator
    | isRecursive generator = QC.sized $ \size -> bounded !! max 0 size
    | Just direct <- lowerUniformWithRank generator = direct
    | otherwise = either (raise "toGenWithRank") id <$> toGenWithRankEither generator
  where
    bounded = [toGenWithRank (upToSize (max firstSize size) generator) | size <- [0 ..]]
    firstSize = either (raise "toGenWithRank") (fromMaybe 1) $ minimumSize generator

{- | Fail a sample with the error's own guidance.

Sampling cannot return a failure, so a generator that could not be built
raises one here. The name is kept alongside the guidance so it can be
looked up or grepped for.
-}
raise :: String -> GenError -> a
raise called err =
    error $
        "Data.CFTA.Gen.Equality.QuickCheck."
            <> called
            <> ": "
            <> show err
            <> "\n"
            <> explain err

{- | Check a property over a transparent generator, shrinking to the
smallest failing member.

Shrink candidates first search every member of strictly smaller size, in size
order, capped at 'smallerMemberLimit', so the result is the globally smallest
failing member whenever the search reaches one. Component shrinking through
'shrinkRank' follows as a fallback; its candidates are never larger than
the current member. For a recursive generator that fallback reads the candidates
from the form bounded at the current size, since a recursive generator has no
component shrinks of its own; bounding preserves ranks, so the candidates
replay against the unbounded generator unchanged. Every candidate is a member
of the generated language, and the failing rank is printed with the
counterexample, so 'unrank' replays it deterministically.

A generator with an opaque region has no ranks to shrink or replay, so it is
tested by sampling alone, with no shrinking.
-}
forAll :: (QC.Testable prop, Show a) => ECTAGen a -> (a -> prop) -> QC.Property
forAll = forAllWithLimit smallerMemberLimit

{- | 'forAll' with an explicit cap on the smaller-member search per shrink
step.

The cap bounds the members tested when the current failing member is
already minimal. When the language holds more small members than
'smallerMemberLimit' — command sequences, for example, accumulate many
short members — the default search never reaches the failing sizes and
structural shrinking alone cannot remove members in the middle of a
product. Raising the cap past the number of passing smaller members
restores the globally smallest failing member at the cost of testing that
many members per shrink step.
-}
forAllWithLimit ::
    (QC.Testable prop, Show a) => Int -> ECTAGen a -> (a -> prop) -> QC.Property
forAllWithLimit limit generator prop
    | isOpaque generator = QC.forAll (toGen generator) prop
    | otherwise =
        QC.forAllShrinkShow
            (toGenWithRank generator)
            shrinkCandidates
            showRanked
            (prop . snd)
  where
    shrinkCandidates (rank, _) = smaller <> structural
      where
        smaller = take limit (smallerMembers generator rank)
        -- 'shrinkRank' has no candidates for a recursive generator, so the
        -- structural candidates come from the form bounded at the current
        -- size, whose shrinking is size-major halving. Bounding preserves
        -- ranks, and leaves a finite generator alone. Every candidate has a
        -- strictly smaller rank and a member no larger than the current one.
        bounded = maybe generator (`upToSize` generator) (sizeOfRank generator rank)
        structural =
            [ (candidate, value)
            | candidate <- shrinkRank bounded rank
            , Right value <- [unrank generator candidate]
            ]

    showRanked (rank, value) = "rank " <> show rank <> ": " <> show value

{- | 'forAll' tests at most this many members of strictly smaller size per
shrink step before falling back to component shrinking.
-}
smallerMemberLimit :: Int
smallerMemberLimit = 1000

{- | Build the generator from QuickCheck's size parameter.

The generator for each size is built /and compiled/ once and shared across
samples, so neither the generator nor its decode plan is reconstructed on every
draw.
-}
sized :: (Int -> ECTAGen a) -> QC.Gen a
sized build = QC.sized $ \size -> towers !! max 0 size
  where
    towers = map (toGen . build) [0 ..]
