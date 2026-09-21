{- | QuickCheck integration for generators.

This module re-exports "Data.CFTA.Gen" and its qualified do-notation, and
adds sampling, pools, and properties over QuickCheck.
-}
module Data.CFTA.Gen.QuickCheck (
    -- * Generators
    module Data.CFTA.Gen,

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

import Data.Hashable (Hashable)
import Data.Maybe (fromMaybe)
import Data.Typeable (Typeable)
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import Data.CFTA.Constraint (Constraint)
import Data.CFTA.Gen
import Data.CFTA.Gen.Do
import qualified Data.CFTA.Ranked.QuickCheck as Tree

{- | Sample a finite pool from an ordinary QuickCheck generator.

The outer 'QC.Gen' draws the pool once. The resulting generator is finite, so
it supports exact inspection, matching, relations, replay, and structural
shrinking. Repeated draws remain repeated ranks and retain the native
generator's empirical weight. A non-positive pool size produces an empty
generator.
-}
samplePool ::
    (Constraint constraint, Hashable symbol, Typeable symbol) =>
    Int -> QC.Gen a -> QC.Gen (Gen symbol constraint a)
samplePool sampleCount native =
    elements <$> QC.vectorOf (max 0 sampleCount) native

{- | 'samplePool' with the draws fixed by a seed.

The native generator is run once, at QuickCheck size 30 (the default of
'QC.generate'), so the result is an ordinary transparent generator: it can be
weighted by 'uniformly', keyed, joined, replayed, and shrunk, and its ranks are
the same in every run under the same seed. That is the trade against 'samplePool',
which draws afresh each time its outer 'QC.Gen' runs. Use 'QC.resize' on the
native generator for another size.
-}
freeze ::
    (Constraint constraint, Hashable symbol, Typeable symbol) => Int -> Int -> QC.Gen a -> Gen symbol constraint a
freeze seed sampleCount native =
    unGen (samplePool sampleCount native) (mkQCGen seed) 30

{- | Sample a non-recursive generator while retaining structured generator errors.

Unlike 'toGen', this does not bound a recursive generator from QuickCheck's
size parameter; apply 'upToSize' explicitly first.
-}
toGenEither :: Gen symbol constraint a -> QC.Gen (Either GenError a)
toGenEither = lower

{- | Sample through the generator type expected by QuickCheck.

Recursive generators are bounded by QuickCheck's size parameter.
-}
toGen :: Gen symbol constraint a -> QC.Gen a
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
toGenWithRank :: Gen symbol constraint a -> QC.Gen (Integer, a)
toGenWithRank generator
    | isRecursive generator = QC.sized $ \size -> bounded !! max 0 size
    | Just direct <- lowerUniformWithRank generator = direct
    | otherwise = either (raise "toGenWithRank") id <$> lowerWithRank generator
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
        "Data.CFTA.Gen.QuickCheck."
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
forAll :: (QC.Testable prop, Show a) => Gen symbol constraint a -> (a -> prop) -> QC.Property
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
    (QC.Testable prop, Show a) => Int -> Gen symbol constraint a -> (a -> prop) -> QC.Property
forAllWithLimit limit generator prop
    | isOpaque generator = QC.forAll (toGen generator) prop
    | otherwise = Tree.forAllWith (toGenWithRank generator) shrinkCandidates prop
  where
    shrinkCandidates rank = smaller <> structural
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
sized :: (Int -> Gen symbol constraint a) -> QC.Gen a
sized build = QC.sized $ \size -> towers !! max 0 size
  where
    towers = map (toGen . build) [0 ..]
