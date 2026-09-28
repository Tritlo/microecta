{- | The queries of an inspectable generator.

Support, counts, ranks, and distributions are all read from the retained
structure. A finite generator answers with a cardinality, a recursive one with
one size class at a time. A query that returns 'Either' reports an opaque
generator with 'CannotInspectOpaqueGenerator'. The rank helpers without an error
result, 'sizeOfRank', 'shrinkRank', and 'smallerMembers', return 'Nothing' or an
empty list for an opaque generator.
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
    rankOf,
    ranksOf,
    smallest,
    sizeOfRank,
    shrinkRank,
    smallerMembers,

    -- * Distributions
    countOn,
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
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Rank, Size, classMemberRank, everyRank, hasRank, nextOffset)
import Data.CFTA.Ranked.Internal.Decoder (RankedValue (..))
import Data.CFTA.Ranked.Internal.Sampler
import Data.CFTA.Ranked.Internal.Shrink (
    planMemberSize,
    shrinkPlanRank,
    smallerPlanMembers,
    smallestPlanRank,
 )
import Data.CFTA.Ranked.Internal.Size (
    MinimumSize (..),
    SizeIndex (sizeClassCounts, sizeClassSelect),
    SizedRank (SizedRank, rankSize),
    minimumMemberSize,
    sizeClassOf,
 )
import qualified Data.CFTA.Ranked.Internal.Size as Size

-- | Return the ECTA support of an inspectable generator.
support :: Gen symbol a -> Either GenError (Node (Label symbol))
support (Transparent result) = staticSupport <$> result
support (Cyclic result) = recursiveSupport <$> result
support (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Read retained source descriptions and group names as a diagnostic graph.
inspect :: Gen symbol a -> Either GenError (Inspection symbol)
inspect (Transparent result) = staticInspection <$> result
inspect (Cyclic result) = recursiveInspection <$> result
inspect (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Return the exact number of ranks in a transparent generator.
cardinality :: Gen symbol a -> Either GenError Cardinality
cardinality (Transparent result) =
    outcomeCardinality . staticOutcomes <$> result
cardinality (Cyclic (Left err)) = Left err
cardinality (Cyclic (Right _)) = Left UnboundedGenerator
cardinality (Opaque _) = Left CannotInspectOpaqueGenerator

{- | Every value of a finite generator, in rank order.

The list has 'cardinality' elements. A recursive or opaque generator gives the
error that 'cardinality' gives.
-}
values :: Gen symbol a -> Either GenError [a]
values generator = do
    total <- cardinality generator
    traverse (unrank generator) $ everyRank total

-- | The number of members of one size, for any inspectable generator.
countAtSize :: Gen symbol a -> Size -> Either GenError Cardinality
countAtSize generator size =
    flip Size.countAtSize size . recursiveIndex <$> recursiveView generator

-- | The smallest structural size in an inspectable language.
minimumSize :: Gen symbol a -> Either GenError (Maybe Size)
minimumSize generator = case recursiveView generator of
    Left EmptyGenerator -> Right Nothing
    Left err -> Left err
    Right recursive -> Right $ case minimumMemberSize $ recursiveIndex recursive of
        MinimumSize size -> Just size
        NoFiniteMember -> Nothing

-- | Decode one stable rank from an inspectable generator.
unrank :: Gen symbol a -> Rank -> Either GenError a
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
        (NoFiniteMember, _) -> Left $ SelectionOutOfRange index 0
        (_, Just (SizedRank size position)) ->
            pure $ rankedValue $ sizeClassSelect recursiveIndex' size position
        (_, Nothing) ->
            Left
                $ SelectionOutOfRange index
                $ sum
                $ map snd
                $ sizeClassCounts recursiveIndex'
unrank (Opaque _) _ = Left CannotInspectOpaqueGenerator

{- | The term of one member by rank.

A recursive generator uses the size-major ranks of 'unrank'.
-}
termAt :: Gen symbol a -> Rank -> Either GenError (Tree.Tree (Label symbol))
termAt _ index | index < 0 = Left $ NegativeRank index
termAt (Transparent result) index = do
    static <- result
    outcomeTerm <$> outcomeSelect (staticOutcomes static) index
termAt (Cyclic result) index = do
    recursive <- result
    terms <- maybe (Left CannotInspectRecursiveGenerator) (Right . recursiveTermIndex) $ recursiveTerm recursive
    let recursiveIndex' = recursiveIndex recursive
    case (minimumMemberSize recursiveIndex', sizeClassOf recursiveIndex' index) of
        (NoFiniteMember, _) -> Left $ SelectionOutOfRange index 0
        (_, Just (SizedRank size position)) -> pure $ rankedValue $ sizeClassSelect terms size position
        (_, Nothing) -> Left $ SelectionOutOfRange index $ sum $ map snd $ sizeClassCounts recursiveIndex'
termAt (Opaque _) _ = Left CannotInspectOpaqueGenerator

{- | The ranks whose term is the given engine term, in ascending order.

This reads the terms that 'termAt' returns, with the private labels of the
engine, and not a term written by hand; @rankOfTerm@ reads the terms that an
imported automaton accepts. One term can have several ranks, because a node
label removes the choice wrapper of its alternatives. A recursive generator
gives the size-major ranks of 'unrank'.
-}
ranksOf :: Gen symbol a -> Tree.Tree (Label symbol) -> Either GenError [Rank]
ranksOf (Transparent result) term = do
    static <- result
    pure $ outcomeRanks (staticOutcomes static) $ WholeTerm term
ranksOf (Cyclic result) term = do
    recursive <- result
    maybe (Left CannotInspectRecursiveGenerator) Right $ recursivePositions recursive $ WholeTerm term
ranksOf (Opaque _) _ = Left CannotInspectOpaqueGenerator

{- | The least rank whose term is the given engine term: the inverse of
'termAt', so that @termAt g =<< rankOf g t@ gives @t@ back. A term that is not
a member gives 'TermNotInLanguage'.
-}
rankOf :: Gen symbol a -> Tree.Tree (Label symbol) -> Either GenError Rank
rankOf generator term = do
    ranks <- ranksOf generator term
    case ranks of
        rank : _ -> Right rank
        [] -> Left TermNotInLanguage

-- | Return the first member in structural size and rank order.
smallest :: Gen symbol a -> Either GenError (Maybe a)
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
sizeOfRank :: Gen symbol a -> Rank -> Maybe Size
sizeOfRank (Cyclic (Right recursive)) rank =
    rankSize <$> sizeClassOf (recursiveIndex recursive) rank
sizeOfRank (Transparent (Right static)) rank
    | hasRank (outcomeCardinality outcomes) rank =
        Just $ planMemberSize (outcomePlan outcomes) rank
  where
    outcomes = staticOutcomes static
sizeOfRank _ _ = Nothing

-- | Structural shrink candidates for one rank of a transparent generator.
shrinkRank :: Gen symbol a -> Rank -> [Rank]
shrinkRank (Cyclic _) _ = []
shrinkRank (Transparent (Right static)) rank
    | rank > 0
    , hasRank (outcomeCardinality outcomes) rank =
        shrinkPlanRank (outcomePlan outcomes) rank
  where
    outcomes = staticOutcomes static
shrinkRank _ _ = []

-- | Every member of strictly smaller size than the given rank's member, in size order, as replayable rank and value.
smallerMembers :: Gen symbol a -> Rank -> [RankedValue a]
smallerMembers (Transparent (Right static)) rank
    | hasRank (outcomeCardinality outcomes) rank =
        smallerPlanMembers (outcomeSizeIndex outcomes) (outcomePlan outcomes) rank
  where
    outcomes = staticOutcomes static
-- Recursive ranks are size-major, so the members of strictly smaller size are
-- exactly the ranks below the current size class. The rank is that class's
-- offset plus the position, which is what 'unrank' reads back; the rank
-- 'sizeClassSelect' reports is the plan's own, and the two differ whenever a
-- size class came from a finite bucket.
smallerMembers (Cyclic (Right recursive)) rank
    | Just (SizedRank size _) <- sizeClassOf index rank =
        [ RankedValue (classMemberRank offset classRank) (rankedValue $ sizeClassSelect index smallerSize classRank)
        | ((smallerSize, Cardinality count), offset) <-
            zip (takeWhile ((< size) . fst) $ sizeClassCounts index) (scanl nextOffset 0 $ map snd $ sizeClassCounts index)
        , classRank <- map ClassRank [0 .. count - 1]
        ]
  where
    index = recursiveIndex recursive
smallerMembers _ _ = []

-- | Count ranked outcomes by a projected key without aggregating equal values.
countOn :: (Ord key) => (a -> key) -> Gen symbol a -> Either GenError (Map.Map key Cardinality)
countOn key (Transparent result) = do
    static <- result
    outcomes <- enumerateOutcomeIndex $ staticOutcomes static
    pure $
        Map.fromListWith
            (+)
            [(key $ outcomeValue outcome, 1) | outcome <- outcomes]
countOn _ (Cyclic (Left err)) = Left err
countOn _ (Cyclic (Right _)) = Left UnboundedGenerator
countOn _ (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Aggregate the exact probability mass of every finite transparent result.
pmf :: (Ord a) => Gen symbol a -> Either GenError [(a, Rational)]
pmf (Transparent result) = do
    static <- result
    outcomes <- compileOutcomes static
    pure
        $ Map.toAscList
        $ Map.fromListWith (+) [(value, mass) | (mass, value) <- outcomes]
pmf (Cyclic (Left err)) = Left err
pmf (Cyclic (Right _)) = Left UnboundedGenerator
pmf (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Aggregate the exact result distribution conditional on one structural size.
pmfAtSize :: (Ord a) => Gen symbol a -> Size -> Either GenError [(a, Rational)]
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
