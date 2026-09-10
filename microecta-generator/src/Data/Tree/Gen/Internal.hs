{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}

-- | Internal representation for finite ranked generators.
module Data.Tree.Gen.Internal (
    Indexed (..),
    Ranked,
    RankedError (..),
    fromIndexed,
    fromIndexedOnDemand,
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

import Data.ECTA.Gen.Internal.Decoder (
    Plan (..),
    RankDecoder (..),
    compilePlan,
    planCardinality,
 )
import Data.ECTA.Gen.Internal.Sampler (
    GenBackend (..),
    Sampler (..),
    mapSampler,
    productSampler,
    uniformSampler,
 )
import Data.ECTA.Gen.Internal.Shrink (
    planMemberSize,
    shrinkPlanRank,
    smallerPlanMembers,
 )

-- | A finite source addressed by a stable zero-based integer index.
data Indexed a = Indexed
    { indexedCardinality :: !Integer
    -- ^ Number of selectable values.
    , indexedSelect :: Integer -> a
    -- ^ Decode one valid index.
    }

-- | Failure while constructing or selecting from a finite ranked generator.
data RankedError
    = -- | The language has no members.
      EmptyRanked
    | -- | A weighted alternative carried a weight below one.
      NonPositiveRankedWeight !Integer
    | -- | Ranks start at zero.
      NegativeRankedRank !Integer
    | -- | A rank fell outside a language of the given cardinality.
      RankedSelectionOutOfRange !Integer !Integer
    deriving (Eq, Show)

-- | A non-empty finite language with stable ranks and a sampling plan.
data Ranked a = Ranked
    { rankedPlan :: !(Plan a)
    , rankedSampler :: !(Sampler a)
    , rankedDecoder :: !(RankDecoder a)
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

-- | Lower a ranked language to any supported sampling backend.
lower :: (GenBackend gen) => Ranked a -> gen a
lower = runValueSampler . rankedSampler

-- | Lower a ranked language while retaining the selected replay rank.
lowerWithRank :: (GenBackend gen) => Ranked a -> gen (Integer, a)
lowerWithRank = runRankSampler . rankedSampler

-- | Structurally smaller valid ranks from the same language.
shrinkRank :: Ranked a -> Integer -> [Integer]
shrinkRank ranked rank
    | rank < 0 || rank >= cardinality ranked = []
    | otherwise = shrinkPlanRank (rankedPlan ranked) rank

-- | Every member structurally smaller than the selected member.
smallerMembers :: Ranked a -> Integer -> [(Integer, a)]
smallerMembers ranked rank
    | rank < 0 || rank >= cardinality ranked = []
    | otherwise = smallerPlanMembers (rankedPlan ranked) rank

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

decode :: RankDecoder a -> Integer -> a
decode (SmallDecoder _ select) = select . fromInteger
decode (LargeDecoder _ select) = select

withOffsets :: [(Integer, Ranked a)] -> [(Integer, (Integer, Ranked a))]
withOffsets = go 0
  where
    go _ [] = []
    go offset (alternative@(_, ranked) : rest) =
        (offset, alternative) : go (offset + cardinality ranked) rest
