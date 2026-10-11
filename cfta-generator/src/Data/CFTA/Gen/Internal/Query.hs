{- | The queries of an inspectable generator.

Each query reads the support, the counts, the ranks, or the distribution that
the generator keeps. A finite generator answers with a cardinality, a
recursive one with one size class at a time. A query that returns 'Either' reports an opaque
generator with 'CannotInspectOpaqueGenerator'. The rank helpers without an error
result, 'sizeOfRank', 'shrinkRank', and 'smallerMembers', return 'Nothing' or an
empty list for an opaque or a failed generator. 'shrinkRank' also returns an
empty list for a recursive generator.
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
    rankOfTerm,
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

import Data.CFTA.Equality (Node)
import Data.CFTA.Gen.Error
import Data.CFTA.Gen.Internal.Inspection
import Data.CFTA.Gen.Internal.Recursive
import Data.CFTA.Gen.Internal.Static
import Data.CFTA.Gen.Internal.Types
import Data.CFTA.Gen.Label (Label (Label))
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
import Data.CFTA.Term (Term)

-- | Return the ECTA support of an inspectable generator.
support :: Gen symbol a -> Either GenError (Node (Label symbol))
support (Transparent result) = staticSupport <$> result
support (Cyclic result) = recursiveSupport <$> result
support (Opaque _) = Left CannotInspectOpaqueGenerator

{- | The source descriptions and the group names of a generator, as a graph for
diagnostics.
-}
inspect :: Gen symbol a -> Either GenError (Inspection symbol)
inspect (Transparent result) = staticInspection <$> result
inspect (Cyclic result) = recursiveInspection <$> result
inspect (Opaque _) = Left CannotInspectOpaqueGenerator

{- | The number of members of a finite generator. A recursive generator gives
'UnboundedGenerator'.
-}
cardinality :: Gen symbol a -> Either GenError Cardinality
cardinality = fmap (outcomeCardinality . staticOutcomes) . staticView

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

-- | The size of the smallest member. An empty generator gives 'Nothing'.
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
    classMember (recursiveIndex recursive) (recursiveIndex recursive) index
unrank (Opaque _) _ = Left CannotInspectOpaqueGenerator

{- | The member at a size-major rank. The first index gives the size class of
the rank, and the second index gives the member of that class.
-}
classMember :: SizeIndex a -> SizeIndex b -> Rank -> Either GenError b
classMember ranks members index = case (minimumMemberSize ranks, sizeClassOf ranks index) of
    (NoFiniteMember, _) -> Left $ SelectionOutOfRange index 0
    (_, Just (SizedRank size position)) -> Right $ rankedValue $ sizeClassSelect members size position
    (_, Nothing) -> Left $ SelectionOutOfRange index $ sum $ map snd $ sizeClassCounts ranks

{- | The term of one member by rank.

A recursive generator uses the size-major ranks of 'unrank'.
-}
termAt :: Gen symbol a -> Rank -> Either GenError (Term (Label symbol))
termAt _ index | index < 0 = Left $ NegativeRank index
termAt (Transparent result) index = do
    static <- result
    outcomeTerm <$> outcomeSelect (staticOutcomes static) index
termAt (Cyclic result) index = do
    recursive <- result
    terms <- maybe (Left CannotInspectRecursiveGenerator) (Right . recursiveTermIndex) $ recursiveTerm recursive
    classMember (recursiveIndex recursive) terms index
termAt (Opaque _) _ = Left CannotInspectOpaqueGenerator

{- | The ranks whose term is the given engine term, in ascending order.

This reads the terms that 'termAt' returns, with the private labels of the
engine, and not a term written by hand; @rankOfTerm@ reads the terms that an
imported automaton accepts. One term can have several ranks, because a node
label removes the choice wrapper of its alternatives. A recursive generator
gives the size-major ranks of 'unrank'. The ranking follows the private
labels, and it checks the user symbols where it can. For a rank whose symbols
it did not check, 'ranksOf' compares the term that 'termAt' gives with the
given term. So a term with other user symbols has no rank.
-}
ranksOf :: (Eq symbol) => Gen symbol a -> Term (Label symbol) -> Either GenError [Rank]
ranksOf generator term = map checkedRank . filter checked <$> candidates generator
  where
    checked (CheckedRank rank symbolsChecked) = symbolsChecked || termAt generator rank == Right term
    candidates (Transparent result) = do
        static <- result
        pure $ outcomeRanks (staticOutcomes static) $ WholeTerm term
    candidates (Cyclic result) = do
        recursive <- result
        maybe (Left CannotInspectRecursiveGenerator) Right $ recursivePositions recursive $ WholeTerm term
    candidates (Opaque _) = Left CannotInspectOpaqueGenerator

{- | The least rank whose term is the given engine term: the inverse of
'termAt', so that @termAt g =<< rankOf g t@ gives @t@ back. A term that is not
a member gives 'TermNotInLanguage'.
-}
rankOf :: (Eq symbol) => Gen symbol a -> Term (Label symbol) -> Either GenError Rank
rankOf generator term = do
    ranks <- ranksOf generator term
    case ranks of
        rank : _ -> Right rank
        [] -> Left TermNotInLanguage

{- | The least rank of a user term: the tree of user symbols that an imported
automaton accepts, as 'fromAutomaton' returns it. A term that is not a member
gives 'TermNotInLanguage'. An import keeps its terms under 'fmap', so the
rank of a mapped import is the rank of the term it maps.
-}
rankOfTerm :: (Eq symbol) => Gen symbol a -> Term symbol -> Either GenError Rank
rankOfTerm generator = rankOf generator . fmap Label

-- | A smallest member: the first member by size, then by rank.
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

{- | The size of the member a rank decodes to: its number of pays, as in FEAT.
'pure' has size zero, an atom one, a product the sum of its sides, and a
'pay' or a constructor one more.
-}
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

-- | The exact distribution of the values of the members of one size.
pmfAtSize :: (Ord a) => Gen symbol a -> Size -> Either GenError [(a, Rational)]
pmfAtSize (Transparent result) size = do
    static <- result
    if size < 0
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
