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
) where

import Data.Foldable (toList)
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Sequence
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import Data.CFTA.Equality (Edge (Edge), Node (Node))
import Data.CFTA.Gen.Error (GenError (..))
import Data.CFTA.Gen.Internal.Inspection
import Data.CFTA.Gen.Internal.Static
import Data.CFTA.Gen.Internal.Support (singletonNode)
import Data.CFTA.Ranked.Internal.Decoder (Plan (..))
import Data.CFTA.Ranked.Internal.Sampler (atomicSampleIndex)

-- | One compact conditional generator and its mass in the whole distribution.
data KeyedBucket symbol a = KeyedBucket
    { keyedBucketMass :: !Rational
    , keyedBucketStatic :: !(Static symbol a)
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
    Bool -> Seq (Rational, Outcome symbol a) -> Either GenError (KeyedBucket symbol a)
bucketFromOutcomes retainAtomic weightedOutcomes = do
    sampler <- sequenceSampler conditional
    sizeSampling <- case commonValue $ toList $ Just . fst <$> weightedOutcomes of
        Just _ -> pure Nothing
        Nothing -> do
            weightSampler <-
                sequenceSampler $
                    (\(weight, outcome) -> outcome{outcomeMass = weight}) <$> weightedOutcomes
            pure $ Just (atomicSampleIndex weightSampler, Right . weightAt)
    pure
        $ KeyedBucket bucketMass
        $ Static
            bucketSupport
            ( mkOutcomeIndex
                totalOutcomes
                uniformMass
                select
                (enumeratedRanks $ toList $ outcomeTerm <$> outcomes)
                selectValue
                sampler
                (PlanSelect totalOutcomes selectValue)
            )
                { outcomeSizeSampling = sizeSampling
                }
            retainAtomic
            (Inspection Nothing $ Node [inspectionEdge $ outcomeInspection outcome | outcome <- toList outcomes])
            (commonRootCount $ toList $ RootCount . termRootCount . outcomeTerm <$> outcomes)
  where
    outcomes = snd <$> weightedOutcomes
    -- The weights of the group add up to its number of members.
    weights = fst <$> weightedOutcomes
    totalWeight = sum weights
    weightAt index =
        toRational totalOutcomes * Sequence.index weights (fromEnum index) / totalWeight
    bucketMass = sum $ outcomeMass <$> outcomes
    conditional = (\outcome -> outcome{outcomeMass = outcomeMass outcome / bucketMass}) <$> outcomes
    totalOutcomes = toEnum $ length outcomes
    uniformMass = commonValue $ Just . outcomeMass <$> toList conditional
    bucketSupport = Node [termEdge $ outcomeTerm outcome | outcome <- toList outcomes]
    termEdge (Tree.Node symbol children) = Edge symbol $ map singletonNode children
    inspectionEdge (Tree.Node symbol children) = Edge symbol $ map singletonNode children

    select index = do
        checkIndex totalOutcomes index
        pure $ Sequence.index conditional $ fromEnum index

    selectValue = outcomeValue . Sequence.index conditional . fromEnum

-- | Merge weighted static languages into one group.
mergeBucketGroup ::
    (Hashable symbol, Typeable symbol) =>
    [(Rational, Static symbol a)] -> Either GenError (KeyedBucket symbol a)
-- One alternative is already the group, and rebuilding it through
-- 'frequencyStatic' would drop its atomic marker.
mergeBucketGroup [(mass, static)] | mass > 0 = Right $ KeyedBucket mass static
mergeBucketGroup alternatives = do
    weightedAlternatives <- integerOutcomes alternatives
    pure $
        KeyedBucket
            (sum $ map fst alternatives)
            -- All-atomic alternatives have size-one plans, so their merge is
            -- still one source choice and stays atomic. A mixed merge is not.
            (retainAtomic $ frequencyStatic weightedAlternatives)
  where
    retainAtomic
        | all (staticAtomic . snd) alternatives = atomicStatic
        | otherwise = id

-- | Merge weighted joined components into normalized result-key groups.
mergeComponentsByKey ::
    (Ord resultKey, Hashable symbol, Typeable symbol) =>
    [(resultKey, Rational, Static symbol a)] ->
    Either GenError (Map.Map resultKey (KeyedBucket symbol a))
mergeComponentsByKey [] = Left EmptyGenerator
mergeComponentsByKey components = do
    unnormalized <- traverse (mergeBucketGroup . toList) grouped
    let totalAcceptedMass = sum $ keyedBucketMass <$> unnormalized
    pure $ fmap (normalizeBucket totalAcceptedMass) unnormalized
  where
    grouped = groupOutcomes [(resultKey, (mass, static)) | (resultKey, mass, static) <- components]

    normalizeBucket totalAcceptedMass bucket =
        bucket
            { keyedBucketMass =
                keyedBucketMass bucket / totalAcceptedMass
            }
