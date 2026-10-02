{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

{- | Internal representation for finite ranked generators.

The public contracts of the ranked API are documented again in
"Data.CFTA.Ranked". Keep the two consistent.

This module is an exposed internal module. The generator layers of
microcfta-generator use it directly. Its exports are not covered by the PVP
contract of the package.
-}
module Data.CFTA.Ranked.Internal (
    Indexed (..),
    WeightedIndexed (..),
    Ranked,
    rankedPlan,
    rankedValueAt,
    RankedError (..),
    fromIndexed,
    fromIndexedOnDemand,
    fromWeightedIndexedOnDemand,
    share,
    fromWeighted,
    frequency,
    oneof,
    cardinality,
    unrank,
    lower,
    lowerWithRank,
    shrinkRank,
    smallerMembers,
    sizeOfRank,
    withOffsets,
) where

import Data.Array (listArray, (!))
import qualified Data.Bifunctor as Bifunctor

import Data.CFTA.Ranked.Internal.Decoder (
    Plan (..),
    RankDecoder (..),
    compilePlan,
    planCardinality,
 )
import Data.CFTA.Ranked.Internal.Sampler (
    GenBackend (..),
    Sampler (..),
    mapSampler,
    productSampler,
    uniformSampler,
 )
import Data.CFTA.Ranked.Internal.Shrink (
    planMemberSize,
    shrinkPlanRank,
    smallerPlanMembers,
    withOffsets,
 )
import Data.CFTA.Ranked.Internal.Size (SizeIndex (minimumMemberSize), sizeIndex)

-- | A finite source addressed by a stable zero-based integer index.
data Indexed a = Indexed
    { indexedCardinality :: !Integer
    -- ^ Number of selectable values.
    , indexedSelect :: Integer -> a
    -- ^ Decode one valid index.
    }

{- | A weighted finite source with separate replay ranks and sampling tickets.

Each valid rank must receive a positive number of tickets. That number is its
relative sampling weight. The ticket callback must return a valid rank for
every ticket below the total weight. These callback invariants are the caller's
responsibility; checking them would enumerate the source.
-}
data WeightedIndexed a = WeightedIndexed
    { weightedIndexedCardinality :: !Integer
    -- ^ Number of distinct zero-based replay ranks.
    , weightedIndexedTotalWeight :: !Integer
    -- ^ Number of zero-based sampling tickets across all ranks.
    , weightedIndexedSelect :: Integer -> a
    -- ^ Decode one valid replay rank.
    , weightedIndexedRankAtTicket :: Integer -> Integer
    -- ^ Map one valid sampling ticket to its replay rank.
    }

-- | Failure while constructing or selecting from a finite ranked generator.
data RankedError
    = -- | The language has no members.
      EmptyRanked
    | -- | A weighted alternative carried a weight below one.
      NonPositiveRankedWeight !Integer
    | {- | The total weight cannot give every rank a positive integer weight.
      The fields contain the cardinality and total weight, respectively.
      -}
      InsufficientRankedWeight !Integer !Integer
    | -- | Ranks start at zero.
      NegativeRankedRank !Integer
    | -- | A rank fell outside a language of the given cardinality.
      RankedSelectionOutOfRange !Integer !Integer
    deriving (Eq, Show)

-- | A non-empty finite language with stable ranks and a sampling plan.
data Ranked a = Ranked
    { rankedPlan :: !(Plan a)
    -- ^ The raw plan. It is the source of truth for rank order and shrinking.
    , rankedSampler :: !(Sampler a)
    -- ^ The compositional sampler used by 'lower'.
    , rankedDecoder :: !(RankDecoder a)
    -- ^ The compiled decoder used by 'unrank'.
    , rankedSizeIndex :: SizeIndex a
    {- ^ The size classes of the plan, built on first use and retained so a
    shrink loop pays for them once.
    -}
    }

instance Functor Ranked where
    fmap transform Ranked{rankedPlan, rankedSampler} =
        makeRanked
            (PlanMap transform rankedPlan)
            (mapSampler transform rankedSampler)

instance Applicative Ranked where
    pure value =
        makeRanked
            (PlanSelect 1 $ const value)
            (uniformSampler 1 $ const value)

    functions <*> arguments =
        makeRanked
            ( PlanAp
                (cardinality arguments)
                (rankedPlan functions)
                (rankedPlan arguments)
            )
            ( productSampler
                (cardinality arguments)
                (rankedSampler functions)
                (rankedSampler arguments)
            )

-- | Build a ranked language from an indexed source.
fromIndexed :: Indexed a -> Either RankedError (Ranked a)
fromIndexed Indexed{indexedCardinality, indexedSelect}
    | indexedCardinality <= 0 = Left EmptyRanked
    | otherwise =
        Right $
            makeRanked
                (PlanSelect indexedCardinality indexedSelect)
                (uniformSampler indexedCardinality indexedSelect)

{- | Build a ranked language whose members are decoded only when selected.

Unlike 'fromIndexed', small sources are not tabulated while the rank decoder
is compiled. Automaton adapters use this to keep term materialization at the
enumeration boundary.
-}
fromIndexedOnDemand :: Indexed a -> Either RankedError (Ranked a)
fromIndexedOnDemand Indexed{indexedCardinality, indexedSelect}
    | indexedCardinality <= 0 = Left EmptyRanked
    | otherwise =
        Right $
            makeRanked
                (PlanSelectOnDemand indexedCardinality indexedSelect)
                (uniformSampler indexedCardinality indexedSelect)

{- | Build a weighted ranked language without enumerating its values or tickets.

Sampling selects one ticket and maps it to the retained replay rank. Weight
does not change cardinality or rank order. The constructor checks cardinality
and total weight only; it does not evaluate either callback.
-}
fromWeightedIndexedOnDemand :: WeightedIndexed a -> Either RankedError (Ranked a)
fromWeightedIndexedOnDemand
    WeightedIndexed
        { weightedIndexedCardinality
        , weightedIndexedTotalWeight
        , weightedIndexedSelect
        , weightedIndexedRankAtTicket
        }
        | weightedIndexedCardinality <= 0 = Left EmptyRanked
        | weightedIndexedTotalWeight <= 0 = Left $ NonPositiveRankedWeight weightedIndexedTotalWeight
        | weightedIndexedTotalWeight < weightedIndexedCardinality =
            Left $ InsufficientRankedWeight weightedIndexedCardinality weightedIndexedTotalWeight
        | otherwise =
            Right $
                makeRanked
                    (PlanSelectOnDemand weightedIndexedCardinality weightedIndexedSelect)
                    ( Sampler
                        (weightedIndexedSelect <$> runValueSampler tickets)
                        ((\rank -> (rank, weightedIndexedSelect rank)) <$> runValueSampler tickets)
                    )
      where
        tickets = uniformSampler weightedIndexedTotalWeight weightedIndexedRankAtTicket

{- | Reuse a compiled subplan without expanding it at each parent occurrence.

The original plan remains available for structural sizes and shrinking. A
language with one member is a sized leaf instead: one size class with one
member. Its plan can be a shared tree with far more nodes than the plan has,
for example a balanced tree whose two children are one node. A walk of the
plan for sizes or for shrinking follows every path, so it would visit every
node of that tree. The leaf gives the size and the member directly. A part
with two or more members cannot occur that often in one member: each
occurrence multiplies the cardinality by at least two.
-}
share :: Ranked a -> Ranked a
share ranked
    | cardinality ranked == 1 = ranked{rankedPlan = PlanSized [(size, 1, const member, const member)]}
    | otherwise = ranked{rankedPlan = PlanShared (cardinality ranked) (rankedDecoder ranked) (rankedPlan ranked)}
  where
    member = decode (rankedDecoder ranked) 0
    size = case minimumMemberSize (rankedSizeIndex ranked) of
        Just size' -> size'
        Nothing ->
            error
                "microcfta-generator bug in Data.CFTA.Ranked.Internal.share: \
                \a language with one member has no size"

{- | Build a ranked language whose members have positive relative weights.

Weight affects sampling, not cardinality or rank order: each list entry has
exactly one stable rank.
-}
fromWeighted :: [(Integer, a)] -> Either RankedError (Ranked a)
fromWeighted [] = Left EmptyRanked
fromWeighted weighted
    | badWeight : _ <- [weight | (weight, _) <- weighted, weight <= 0] =
        Left (NonPositiveRankedWeight badWeight)
    | otherwise =
        Right $
            makeRanked
                (PlanSelect total selectValue)
                ( Sampler
                    (frequencyGen [(weight, pure value) | (weight, value) <- weighted])
                    ( frequencyGen
                        [ (weight, pure (rank, value))
                        | (rank, (weight, value)) <- zip [0 ..] weighted
                        ]
                    )
                )
  where
    total = toInteger $ length weighted
    table = listArray (0, length weighted - 1) (map snd weighted)
    selectValue = (table !) . fromInteger

-- | Combine non-empty alternatives with positive relative weights.
frequency :: [(Integer, Ranked a)] -> Either RankedError (Ranked a)
frequency [] = Left EmptyRanked
frequency alternatives
    | badWeight : _ <- [weight | (weight, _) <- alternatives, weight <= 0] =
        Left (NonPositiveRankedWeight badWeight)
    | otherwise =
        Right $
            makeRanked
                ( PlanChoice
                    [ (cardinality ranked, rankedPlan ranked)
                    | (_, ranked) <- alternatives
                    ]
                )
                ( Sampler
                    ( frequencyGen
                        [ (weight, runValueSampler $ rankedSampler ranked)
                        | (weight, ranked) <- alternatives
                        ]
                    )
                    ( frequencyGen
                        [ ( weight
                          , (Bifunctor.first (offset +))
                                <$> runRankSampler (rankedSampler ranked)
                          )
                        | (offset, (weight, ranked)) <- withOffsets (cardinality . snd) alternatives
                        ]
                    )
                )

-- | Combine equally weighted non-empty alternatives.
oneof :: [Ranked a] -> Either RankedError (Ranked a)
oneof = frequency . map (1,)

-- | Return the exact number of stable ranks.
cardinality :: Ranked a -> Integer
cardinality = planCardinality . rankedPlan

-- | Decode one stable rank.
unrank :: Ranked a -> Integer -> Either RankedError a
unrank _ rank | rank < 0 = Left (NegativeRankedRank rank)
unrank ranked rank
    | rank >= total = Left (RankedSelectionOutOfRange rank total)
    | otherwise = Right $ decode (rankedDecoder ranked) rank
  where
    total = cardinality ranked

-- | Decode a valid rank without range checks. Internal adapters check it first.
rankedValueAt :: Ranked a -> Integer -> a
rankedValueAt = decode . rankedDecoder

-- | Lower a ranked language to any supported sampling backend.
lower :: (GenBackend gen) => Ranked a -> gen a
lower = runValueSampler . rankedSampler

-- | Lower a ranked language while retaining the selected replay rank.
lowerWithRank :: (GenBackend gen) => Ranked a -> gen (Integer, a)
lowerWithRank = runRankSampler . rankedSampler

{- | Structural shrink candidates for one rank.

Each candidate is a strictly smaller valid rank of the same language whose
member is no larger than the current member, measured in source choices.
Earlier alternatives come first at their smallest member, then each product
component shrinks on its own. Use 'smallerMembers' for every member of
strictly smaller size.
-}
shrinkRank :: Ranked a -> Integer -> [Integer]
shrinkRank ranked rank
    | rank < 0 || rank >= cardinality ranked = []
    | otherwise = shrinkPlanRank (rankedPlan ranked) rank

-- | Every member structurally smaller than the selected member, in size order.
smallerMembers :: Ranked a -> Integer -> [(Integer, a)]
smallerMembers ranked rank
    | rank < 0 || rank >= cardinality ranked = []
    | otherwise = smallerPlanMembers (rankedSizeIndex ranked) (rankedPlan ranked) rank

-- | Structural size of the member at a valid rank.
sizeOfRank :: Ranked a -> Integer -> Maybe Integer
sizeOfRank ranked rank
    | rank < 0 || rank >= cardinality ranked = Nothing
    | otherwise = Just $ planMemberSize (rankedPlan ranked) rank

-- | Build a ranked language from its plan and sampler, and compile the plan once.
makeRanked :: Plan a -> Sampler a -> Ranked a
makeRanked plan sampler =
    Ranked
        plan
        sampler
        (compilePlan (planCardinality plan) plan)
        (sizeIndex plan)

-- | Decode a valid rank with a compiled decoder.
decode :: RankDecoder a -> Integer -> a
decode (SmallDecoder _ select) = select . fromInteger
decode (LargeDecoder _ select) = select
