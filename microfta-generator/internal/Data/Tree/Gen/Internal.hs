{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}

-- | Internal representation for finite ranked generators.
module Data.Tree.Gen.Internal (
    Indexed (..),
    WeightedIndexed (..),
    Ranked,
    rankedPlan,
    rankedSampler,
    rankedValueAt,
    RankedError (..),
    fromIndexed,
    fromIndexedOnDemand,
    fromWeightedIndexedOnDemand,
    fromSizeIndex,
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
) where

import Data.Array (listArray, (!))

import Data.Tree.Gen.Internal.Decoder (
    Plan (..),
    RankDecoder (..),
    compilePlan,
    planCardinality,
 )
import Data.Tree.Gen.Internal.Sampler (
    GenBackend (..),
    Sampler (..),
    mapSampler,
    productSampler,
    uniformSampler,
 )
import Data.Tree.Gen.Internal.Shrink (
    planMemberSize,
    shrinkPlanRank,
    smallerPlanMembers,
 )
import Data.Tree.Gen.Internal.Size (SizeIndex, sizeClasses, sizeIndex)

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

The public contracts of the ranked API are documented again in
"Data.Tree.Gen"; keep the two in step. This module belongs to the @internal@
sublibrary. It is an integration
interface for the constrained generator packages, and its exports are not
covered by the PVP contract of the main library.
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
fromWeightedIndexedOnDemand WeightedIndexed{weightedIndexedCardinality, weightedIndexedTotalWeight, weightedIndexedSelect, weightedIndexedRankAtTicket}
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

{- | Compile a finite prefix of a size-major index.

Each rank keeps its position in the unbounded index. Sampling is uniform over
the retained ranks. A non-positive bound or empty prefix gives 'EmptyRanked'.
-}
fromSizeIndex :: Int -> SizeIndex a -> Either RankedError (Ranked a)
fromSizeIndex bound index
    | total <= 0 = Left EmptyRanked
    | otherwise = Right $ Ranked plan (uniformSampler total select) decoder (sizeIndex plan)
  where
    plan = PlanSized $ sizeClasses bound index
    total = planCardinality plan
    decoder = compilePlan total plan
    select = decode decoder

{- | Reuse a compiled subplan without expanding it at each parent occurrence.

The original plan remains available for structural sizes and shrinking.
-}
share :: Ranked a -> Ranked a
share ranked =
    ranked
        { rankedPlan =
            PlanShared (cardinality ranked) (rankedDecoder ranked) (rankedPlan ranked)
        }

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
                          , (\(rank, value) -> (offset + rank, value))
                                <$> runRankSampler (rankedSampler ranked)
                          )
                        | (offset, (weight, ranked)) <- withOffsets alternatives
                        ]
                    )
                )

-- | Combine equally weighted non-empty alternatives.
oneof :: [Ranked a] -> Either RankedError (Ranked a)
oneof = frequency . map (\ranked -> (1, ranked))

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
sizeOfRank :: Ranked a -> Integer -> Maybe Int
sizeOfRank ranked rank
    | rank < 0 || rank >= cardinality ranked = Nothing
    | otherwise = Just $ planMemberSize (rankedPlan ranked) rank

makeRanked :: Plan a -> Sampler a -> Ranked a
makeRanked plan sampler =
    Ranked
        plan
        sampler
        (compilePlan (planCardinality plan) plan)
        (sizeIndex plan)

decode :: RankDecoder a -> Integer -> a
decode (SmallDecoder _ select) = select . fromInteger
decode (LargeDecoder _ select) = select

withOffsets :: [(Integer, Ranked a)] -> [(Integer, (Integer, Ranked a))]
withOffsets = go 0
  where
    go _ [] = []
    go offset (alternative@(_, ranked) : rest) =
        (offset, alternative) : go (offset + cardinality ranked) rest
