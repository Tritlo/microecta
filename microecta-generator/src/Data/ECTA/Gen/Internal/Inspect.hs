{- | The observers of an inspectable generator.

Support, counts, ranks, and distributions are all read from the retained
structure. A finite generator answers with a cardinality, a recursive one with
one size class at a time, and an opaque one with
'CannotInspectOpaqueGenerator'.
-}
module Data.ECTA.Gen.Internal.Inspect (
    -- * Structure
    support,
    cardinality,
    countAtSize,
    minimumSize,

    -- * Ranks
    unrank,
    smallest,
    sizeOfRank,
    shrinkRank,
    smallerMembers,

    -- * Distributions
    countBy,
    pmf,
    pmfAtSize,
) where

import qualified Data.Map.Strict as Map

import Data.ECTA (Node)
import Data.ECTA.Gen.Internal
import Data.ECTA.Gen.Internal.Types
import Data.ECTA.Term (Symbol)
import Data.Tree.Gen.Internal.Sampler
import Data.Tree.Gen.Internal.Shrink (
    planMemberSize,
    shrinkPlanRank,
    smallerPlanMembers,
    smallestPlanRank,
 )
import Data.Tree.Gen.Internal.Size (
    SizeIndex (sizeClassCounts, sizeClassSelect),
    minimumMemberSize,
    sizeClassOf,
 )
import qualified Data.Tree.Gen.Internal.Size as Size

{- | Return the ECTA support of an inspectable generator.

A recursive generator's support is its @Mu@ node, which accepts members of
every size: a size bound restricts the rank space, not the automaton.
-}
support :: ECTAGen gen a -> Either ECTAGenError (Node Symbol)
support (Transparent result) = staticSupport <$> result
support (Cyclic result) = recursiveSupport <$> result
support (Opaque _) = Left CannotInspectOpaqueGenerator

{- | Return the exact number of ranks in a transparent generator.

A recursive generator has no cardinality; bound it with 'upToSize', or ask
for one size class with 'countAtSize'.
-}
cardinality :: ECTAGen gen a -> Either ECTAGenError Integer
cardinality (Transparent result) =
    outcomeCardinality . staticOutcomes <$> result
cardinality (Cyclic _) = Left UnboundedGenerator
cardinality (Opaque _) = Left CannotInspectOpaqueGenerator

{- | The number of members of one size, for any inspectable generator.

Size is the number of source choices in a member. This is the counting a
recursive generator supports in place of a cardinality: every class is
finite even when the language is not.
-}
countAtSize :: ECTAGen gen a -> Int -> Either ECTAGenError Integer
countAtSize generator size =
    flip Size.countAtSize size . recursiveIndex <$> recursiveView generator

{- | The smallest structural size in an inspectable language.

Size is the number of source choices in a member. 'Nothing' means the language
is empty. Opaque generators cannot be inspected.
-}
minimumSize :: ECTAGen gen a -> Either ECTAGenError (Maybe Int)
minimumSize generator = case recursiveView generator of
    Left EmptyGenerator -> Right Nothing
    Left err -> Left err
    Right recursive -> Right $ minimumMemberSize $ recursiveIndex recursive

{- | Decode one stable rank from an inspectable generator.

Ranks are stable while the generator definition and the ordering of its finite
sources remain unchanged.
-}
unrank :: ECTAGen gen a -> Integer -> Either ECTAGenError a
unrank _ index | index < 0 = Left $ NegativeRank index
unrank (Transparent result) index = do
    static <- result
    let outcomes = staticOutcomes static
    checkIndex (outcomeCardinality outcomes) index
    pure $ outcomeValueAt outcomes index
unrank (Cyclic result) index = do
    recursive <- result
    let recursiveIndex' = recursiveIndex recursive
    case (minimumMemberSize recursiveIndex', sizeClassOf recursiveIndex' index) of
        (Nothing, _) -> Left $ SelectionOutOfRange index 0
        (_, Just (size, position)) ->
            pure $ snd $ sizeClassSelect recursiveIndex' size position
        (_, Nothing) ->
            Left
                $ SelectionOutOfRange index
                $ sum
                $ sizeClassCounts recursiveIndex'
unrank (Opaque _) _ = Left CannotInspectOpaqueGenerator

{- | Return the first member in structural size and rank order.

For recursive generators this is a globally smallest member. 'Nothing' means
the language is empty; other construction or inspection failures stay explicit.
-}
smallest :: ECTAGen gen a -> Either ECTAGenError (Maybe a)
smallest (Transparent result) =
    case result of
        Left EmptyGenerator -> Right Nothing
        Left err -> Left err
        Right static ->
            case smallestPlanRank $ outcomePlan $ staticOutcomes static of
                Nothing -> Right Nothing
                Just rank -> Right $ Just $ outcomeValueAt (staticOutcomes static) rank
smallest generator@(Cyclic _) =
    case unrank generator 0 of
        Left EmptyGenerator -> Right Nothing
        Left (SelectionOutOfRange 0 0) -> Right Nothing
        Left err -> Left err
        Right value -> Right $ Just value
smallest (Opaque _) = Left CannotInspectOpaqueGenerator

{- | The number of source choices in the member a rank decodes to.

'Nothing' for opaque generators and out-of-range ranks.
-}
sizeOfRank :: ECTAGen gen a -> Integer -> Maybe Int
sizeOfRank (Cyclic (Right recursive)) rank =
    fst <$> sizeClassOf (recursiveIndex recursive) rank
sizeOfRank (Transparent (Right static)) rank
    | rank >= 0
    , rank < outcomeCardinality outcomes =
        Just $ planMemberSize (outcomePlan outcomes) rank
  where
    outcomes = staticOutcomes static
sizeOfRank _ _ = Nothing

{- | Structural shrink candidates for one rank of a transparent generator.

Candidates decode to values from the same language and are never larger than
the current member: earlier alternatives at their smallest members come
first, then each product component shrinks independently. Opaque generators
and out-of-range ranks have no candidates.
-}
shrinkRank :: ECTAGen gen a -> Integer -> [Integer]
shrinkRank (Cyclic _) _ = []
shrinkRank (Transparent (Right static)) rank
    | rank > 0
    , rank < outcomeCardinality outcomes =
        shrinkPlanRank (outcomePlan outcomes) rank
  where
    outcomes = staticOutcomes static
shrinkRank _ _ = []

{- | Every member of strictly smaller size than the given rank's member, in
size order, as replayable rank and value.

Size is the number of source choices in a member. The stream is lazy, so cap
it before use; a smallest failing member found in it is globally minimal.
Opaque generators have no smaller members, and neither does a rank outside
a finite generator. A recursive generator has a size class for every rank.
-}
smallerMembers :: ECTAGen gen a -> Integer -> [(Integer, a)]
smallerMembers (Transparent (Right static)) rank
    | rank >= 0
    , rank < outcomeCardinality outcomes =
        smallerPlanMembers (outcomeSizeIndex outcomes) (outcomePlan outcomes) rank
  where
    outcomes = staticOutcomes static
-- Recursive ranks are size-major, so the members of strictly smaller size are
-- exactly the ranks below the current size class. The rank is that class's
-- offset plus the position, which is what 'unrank' reads back; the rank
-- 'sizeClassSelect' reports is the plan's own, and the two differ whenever a
-- size class came from a finite bucket.
smallerMembers (Cyclic (Right recursive)) rank
    | Just (size, _) <- sizeClassOf index rank =
        [ (offset + position, snd $ sizeClassSelect index smallerSize position)
        | (smallerSize, offset) <- zip [1 .. size - 1] (scanl (+) 0 (sizeClassCounts index))
        , position <- [0 .. Size.countAtSize index smallerSize - 1]
        ]
  where
    index = recursiveIndex recursive
smallerMembers _ _ = []

-- | Count ranked outcomes by a projected key without aggregating equal values.
countBy :: (Ord key) => (a -> key) -> ECTAGen gen a -> Either ECTAGenError (Map.Map key Integer)
countBy key (Transparent result) = do
    static <- result
    outcomes <- enumerateOutcomeIndex $ staticOutcomes static
    pure $
        Map.fromListWith
            (+)
            [(key $ outcomeValue outcome, 1) | outcome <- outcomes]
countBy _ (Cyclic _) = Left UnboundedGenerator
countBy _ (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Aggregate the exact probability mass of every finite transparent result.
pmf :: (Ord a) => ECTAGen gen a -> Either ECTAGenError [(a, Rational)]
pmf (Transparent result) = do
    static <- result
    outcomes <- compileOutcomes static
    pure
        $ Map.toAscList
        $ Map.fromListWith (+) [(value, mass) | (mass, value) <- outcomes]
pmf (Cyclic _) = Left UnboundedGenerator
pmf (Opaque _) = Left CannotInspectOpaqueGenerator

{- | Aggregate the exact result distribution conditional on one structural
size.

For a recursive generator this interprets its size-indexed sampler, so a
weighted finite choice closed with 'atomic' retains its declared probability.
For a finite generator it conditions the retained outcome masses on the
requested size. A size with no members returns an empty distribution.

This enumerates every result in the selected size class before equal results
are aggregated. A language can therefore be cheap to count and too large for
this observer. Use 'countAtSize' for cardinality, or 'massesAtSize' when a
retained-key distribution answers the question.
-}
pmfAtSize :: (Ord a) => ECTAGen gen a -> Int -> Either ECTAGenError [(a, Rational)]
pmfAtSize (Transparent result) size = do
    static <- result
    if size < 1
        then Right []
        else do
            outcomes <- enumerateOutcomeIndex $ staticOutcomes static
            let plan = outcomePlan $ staticOutcomes static
                selected =
                    [ (outcomeMass outcome, outcomeValue outcome)
                    | (rank, outcome) <- zip [0 ..] outcomes
                    , planMemberSize plan rank == size
                    ]
            if null selected
                then Right []
                else do
                    normalized <- normalize selected
                    pure
                        $ Map.toAscList
                        $ Map.fromListWith (+) [(value, mass) | (mass, value) <- normalized]
pmfAtSize (Cyclic result) size = do
    recursive <- result
    if Size.countAtSize (recursiveIndex recursive) size <= 0
        then Right []
        else Right $ exactPmfAtSize (recursiveSampling recursive) size
pmfAtSize (Opaque _) _ = Left CannotInspectOpaqueGenerator
