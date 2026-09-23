{- | The queries of an inspectable generator.

Support, counts, ranks, and distributions are all read from the retained
structure. A finite generator answers with a cardinality, a recursive one with
one size class at a time, and an opaque one with
'CannotInspectOpaqueGenerator'.
-}
module Data.CFTA.Gen.Internal.Query (
    -- * Structure
    support,
    inspect,
    cardinality,
    values,
    countAtSize,
    minimumSize,

    -- * Ranks
    unrank,
    termAt,
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
import qualified Data.Tree as Tree

import Data.CFTA.Equality (Node)
import Data.CFTA.Gen.Error
import Data.CFTA.Gen.Internal.Inspection
import Data.CFTA.Gen.Internal.Recursive
import Data.CFTA.Gen.Internal.Static
import Data.CFTA.Gen.Internal.Types
import Data.CFTA.Gen.Label (Label)
import Data.CFTA.Ranked.Internal.Sampler
import Data.CFTA.Ranked.Internal.Shrink (
    planMemberSize,
    shrinkPlanRank,
    smallerPlanMembers,
    smallestPlanRank,
 )
import Data.CFTA.Ranked.Internal.Size (
    SizeIndex (sizeClassCounts, sizeClassSelect),
    minimumMemberSize,
    sizeClassOf,
 )
import qualified Data.CFTA.Ranked.Internal.Size as Size

-- | Return the ECTA support of an inspectable generator.
support :: Gen symbol constraint a -> Either GenError (Node (Label symbol) constraint)
support (Transparent result) = staticSupport <$> result
support (Cyclic result) = recursiveSupport <$> result
support (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Read retained source descriptions and group names as a diagnostic graph.
inspect :: Gen symbol constraint a -> Either GenError (Inspection symbol constraint)
inspect (Transparent result) = staticInspection <$> result
inspect (Cyclic result) = recursiveInspection <$> result
inspect (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Return the exact number of ranks in a transparent generator.
cardinality :: Gen symbol constraint a -> Either GenError Integer
cardinality (Transparent result) =
    outcomeCardinality . staticOutcomes <$> result
cardinality (Cyclic _) = Left UnboundedGenerator
cardinality (Opaque _) = Left CannotInspectOpaqueGenerator

{- | Every value of a finite generator, in rank order.

The list has 'cardinality' elements. A recursive or opaque generator gives the
error that 'cardinality' gives.
-}
values :: Gen symbol constraint a -> Either GenError [a]
values generator = do
    total <- cardinality generator
    traverse (unrank generator) [0 .. total - 1]

-- | The number of members of one size, for any inspectable generator.
countAtSize :: Gen symbol constraint a -> Int -> Either GenError Integer
countAtSize generator size =
    flip Size.countAtSize size . recursiveIndex <$> recursiveView generator

-- | The smallest structural size in an inspectable language.
minimumSize :: Gen symbol constraint a -> Either GenError (Maybe Int)
minimumSize generator = case recursiveView generator of
    Left EmptyGenerator -> Right Nothing
    Left err -> Left err
    Right recursive -> Right $ minimumMemberSize $ recursiveIndex recursive

-- | Decode one stable rank from an inspectable generator.
unrank :: Gen symbol constraint a -> Integer -> Either GenError a
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

-- | The term of one member by rank.
termAt :: Gen symbol constraint a -> Integer -> Either GenError (Tree.Tree (Label symbol))
termAt _ index | index < 0 = Left $ NegativeRank index
termAt (Transparent result) index = do
    static <- result
    outcomeTerm <$> outcomeSelect (staticOutcomes static) index
termAt (Cyclic _) _ = Left CannotInspectRecursiveGenerator
termAt (Opaque _) _ = Left CannotInspectOpaqueGenerator

-- | Return the first member in structural size and rank order.
smallest :: Gen symbol constraint a -> Either GenError (Maybe a)
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

-- | The number of source choices in the member a rank decodes to.
sizeOfRank :: Gen symbol constraint a -> Integer -> Maybe Int
sizeOfRank (Cyclic (Right recursive)) rank =
    fst <$> sizeClassOf (recursiveIndex recursive) rank
sizeOfRank (Transparent (Right static)) rank
    | rank >= 0
    , rank < outcomeCardinality outcomes =
        Just $ planMemberSize (outcomePlan outcomes) rank
  where
    outcomes = staticOutcomes static
sizeOfRank _ _ = Nothing

-- | Structural shrink candidates for one rank of a transparent generator.
shrinkRank :: Gen symbol constraint a -> Integer -> [Integer]
shrinkRank (Cyclic _) _ = []
shrinkRank (Transparent (Right static)) rank
    | rank > 0
    , rank < outcomeCardinality outcomes =
        shrinkPlanRank (outcomePlan outcomes) rank
  where
    outcomes = staticOutcomes static
shrinkRank _ _ = []

-- | Every member of strictly smaller size than the given rank's member, in size order, as replayable rank and value.
smallerMembers :: Gen symbol constraint a -> Integer -> [(Integer, a)]
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
countBy :: (Ord key) => (a -> key) -> Gen symbol constraint a -> Either GenError (Map.Map key Integer)
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
pmf :: (Ord a) => Gen symbol constraint a -> Either GenError [(a, Rational)]
pmf (Transparent result) = do
    static <- result
    outcomes <- compileOutcomes static
    pure
        $ Map.toAscList
        $ Map.fromListWith (+) [(value, mass) | (mass, value) <- outcomes]
pmf (Cyclic _) = Left UnboundedGenerator
pmf (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Aggregate the exact result distribution conditional on one structural size.
pmfAtSize :: (Ord a) => Gen symbol constraint a -> Int -> Either GenError [(a, Rational)]
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
