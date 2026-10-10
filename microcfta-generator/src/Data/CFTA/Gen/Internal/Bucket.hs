{- | Retained key groups of finite languages.

A t'KeyedBucket' is one finite language and its mass in the whole
distribution. Grouping, application, and relation all produce buckets, so the
merge that normalizes them is written once here.
-}
module Data.CFTA.Gen.Internal.Bucket (
    KeyedBucket (..),
    groupOutcomes,
    bucketFromOutcomes,
    mergeBucketGroup,
    mergeComponentsByKey,

    -- * Masses
    MassIndex (..),
    massAtSize,
    emptyMassIndex,
    countMassIndex,
    atomicMassIndex,
    sumMassIndexes,
    productMassIndex,
) where

import Data.Foldable (toList)
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Sequence
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import Data.CFTA.Equality (Edge (Edge), Node (Node))
import Data.CFTA.Gen.Error (GenError (..))
import Data.CFTA.Gen.Internal.Inspection
import Data.CFTA.Gen.Internal.Static
import Data.CFTA.Gen.Internal.Support (singletonNode)
import Data.CFTA.Index (Size)
import Data.CFTA.Ranked.Internal.Decoder (Plan (..))
import Data.CFTA.Ranked.Internal.Sampler (atomicSampleIndex)
import Data.CFTA.Ranked.Internal.Size (SizeIndex (sizeClassCounts), addSparse, mulSparse, valueAtSize)

-- | One compact conditional generator and its mass in the whole distribution.
data KeyedBucket symbol a = KeyedBucket
    { keyedBucketMass :: !Rational
    , keyedBucketStatic :: !(Static symbol a)
    , keyedBucketMasses :: !(Maybe MassIndex)
    {- ^ The weight of the group in each size class, on the scale of member
    counts, when it is not the member count of the class. A group that keeps
    some members of a language keeps their weights in that language here, so
    a merge chooses it inside a size class by these weights. 'Nothing' means
    the member counts.
    -}
    }

-- | Group enumerated outcomes by key, in their order.
groupOutcomes :: (Ord key) => [(key, outcome)] -> Map.Map key (Seq outcome)
groupOutcomes = Map.fromListWith (flip (<>)) . map (fmap Sequence.singleton)

{- | Build one retained group from its outcomes, in rank order.

Every outcome comes with the weight of its rank inside its size class in the
grouped language, as 'enumerateWeighted' gives it. Every member of a group
has size one, and the members keep their weights relative to each other, so
an atomic choice inside the grouped language keeps its distribution inside
the group.
-}
bucketFromOutcomes ::
    (Hashable symbol, Typeable symbol) =>
    Bool -> [(Rational, Outcome symbol a)] -> Either GenError (KeyedBucket symbol a)
bucketFromOutcomes retainAtomic weightedOutcomes = do
    sampler <- sequenceSampler conditional
    sizeSampling <- case commonValue $ map (Just . fst) weightedOutcomes of
        Just _ -> pure Nothing
        Nothing -> do
            weightSampler <-
                sequenceSampler $
                    Sequence.fromList
                        [ outcome{outcomeMass = weight}
                        | (weight, outcome) <- weightedOutcomes
                        ]
            pure $ Just (atomicSampleIndex weightSampler, Right . weightAt)
    let static =
            Static
                bucketSupport
                ( mkOutcomeIndex
                    totalOutcomes
                    uniformMass
                    select
                    (enumeratedRanks $ map outcomeTerm outcomes)
                    selectValue
                    sampler
                    (PlanSelect totalOutcomes selectValue)
                )
                    { outcomeSizeSampling = sizeSampling
                    }
                retainAtomic
                (Inspection Nothing $ Node [inspectionEdge $ outcomeInspection outcome | outcome <- outcomes])
                (commonRootCount $ map (RootCount . termRootCount . outcomeTerm) outcomes)
    pure $ KeyedBucket bucketMass static Nothing
  where
    outcomes = map snd weightedOutcomes
    -- The weights of the group add up to its number of members.
    weights = Sequence.fromList $ map fst weightedOutcomes
    totalWeight = sum weights
    weightAt index =
        toRational totalOutcomes * Sequence.index weights (fromEnum index) / totalWeight
    bucketMass = sum $ map outcomeMass outcomes
    conditional =
        Sequence.fromList
            [ outcome{outcomeMass = outcomeMass outcome / bucketMass}
            | outcome <- outcomes
            ]
    totalOutcomes = toEnum $ length outcomes
    uniformMass = commonValue $ Just . outcomeMass <$> toList conditional
    bucketSupport = Node [termEdge $ outcomeTerm outcome | outcome <- outcomes]
    termEdge (Tree.Node symbol children) = Edge symbol $ map singletonNode children
    inspectionEdge (Tree.Node symbol children) = Edge symbol $ map singletonNode children

    select index = do
        checkIndex totalOutcomes index
        pure $ Sequence.index conditional $ fromEnum index

    selectValue = outcomeValue . Sequence.index conditional . fromEnum

-- | Merge weighted buckets into one group.
mergeBucketGroup ::
    (Hashable symbol, Typeable symbol) =>
    [KeyedBucket symbol a] -> Either GenError (KeyedBucket symbol a)
-- One bucket is already the group, and rebuilding it through
-- 'frequencyStatic' would drop its atomic marker.
mergeBucketGroup [bucket] | keyedBucketMass bucket > 0 = Right bucket
mergeBucketGroup buckets = do
    weighted <- integerOutcomes [(keyedBucketMass bucket, bucket) | bucket <- buckets]
    pure $ KeyedBucket (sum $ map keyedBucketMass buckets) (merged weighted) masses
  where
    massWeighted = any (isJust . keyedBucketMasses) buckets
    merged weighted
        -- A bucket with weights of its own is chosen by them inside a size class.
        | massWeighted =
            frequencyStaticWithMasses
                [(weight, massAtSize <$> keyedBucketMasses bucket, keyedBucketStatic bucket) | (weight, bucket) <- weighted]
        -- All-atomic alternatives have size-one plans, so their merge is
        -- still one source choice and stays atomic. A mixed merge is not.
        | otherwise = retainAtomic $ frequencyStatic [(weight, keyedBucketStatic bucket) | (weight, bucket) <- weighted]
    masses
        | massWeighted = Just $ sumMassIndexes $ map bucketMasses buckets
        | otherwise = Nothing
    bucketMasses bucket =
        fromMaybe (countMassIndex $ outcomeSizeIndex $ staticOutcomes $ keyedBucketStatic bucket) $ keyedBucketMasses bucket
    retainAtomic
        | all (staticAtomic . keyedBucketStatic) buckets = atomicStatic
        | otherwise = id

-- | Merge weighted joined components into normalized result-key groups.
mergeComponentsByKey ::
    (Ord resultKey, Hashable symbol, Typeable symbol) =>
    [(resultKey, KeyedBucket symbol a)] ->
    Either GenError (Map.Map resultKey (KeyedBucket symbol a))
mergeComponentsByKey [] = Left EmptyGenerator
mergeComponentsByKey components = do
    unnormalized <- traverse (mergeBucketGroup . toList) grouped
    let totalAcceptedMass = sum $ keyedBucketMass <$> unnormalized
    pure $ fmap (normalizeBucket totalAcceptedMass) unnormalized
  where
    grouped = groupOutcomes components

    normalizeBucket totalAcceptedMass bucket =
        bucket
            { keyedBucketMass =
                keyedBucketMass bucket / totalAcceptedMass
            }

{- | A memoized unnormalized mass for sizes in ascending order. Sizes without
members are left out, except for the zero mass that a product starts with.
-}
newtype MassIndex = MassIndex [(Size, Rational)]

-- | Read one size, returning zero outside the sizes with mass.
massAtSize :: MassIndex -> Size -> Rational
massAtSize (MassIndex masses) = valueAtSize masses

-- | A language with no members at any size.
emptyMassIndex :: MassIndex
emptyMassIndex = MassIndex []

-- | Structural counts interpreted as unnormalized uniform mass.
countMassIndex :: SizeIndex a -> MassIndex
countMassIndex index =
    MassIndex [(size, toRational count) | (size, count) <- sizeClassCounts index]

-- | One finite atom's complete mass at size one.
atomicMassIndex :: Rational -> MassIndex
atomicMassIndex mass = MassIndex [(1, mass) | mass > 0]

-- | Add alternative masses by size.
sumMassIndexes :: [MassIndex] -> MassIndex
sumMassIndexes indexes = MassIndex $ foldr (\(MassIndex masses) -> addSparse masses) [] indexes

{- | Convolve two mass series: the sizes of a pair add, and the masses
multiply. The zero mass at size one lets a recursive knot of masses give its
smallest sizes before the product is computed, as for the size counts.
-}
productMassIndex :: MassIndex -> MassIndex -> MassIndex
productMassIndex (MassIndex left) (MassIndex right) = MassIndex $ (1, 0) : mulSparse left right
