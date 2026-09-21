{- | Retained key groups of finite languages.

A t'KeyedBucket' is one finite language and its mass in the whole
distribution. Grouping, application, and relation all produce buckets, so the
merge that normalizes them is written once here.
-}
module Data.CFTA.Gen.Equality.Internal.Bucket (
    KeyedBucket (..),
    groupOutcomes,
    bucketFromOutcomes,
    mergeBucketGroup,
    mergeComponentsByKey,
) where

import Data.CFTA.Constraint (Constraint (..))
import Data.Foldable (toList)
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Sequence
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import Data.CFTA.Equality (Edge (Edge), Node (Node))
import Data.CFTA.Gen.Equality.Internal.Inspection
import Data.CFTA.Gen.Equality.Internal.Static
import Data.CFTA.Gen.Equality.Internal.Support (singletonNode)
import Data.CFTA.Gen.Error (GenError (..))
import Data.CFTA.Ranked.Internal.Decoder (Plan (..))

-- | One compact conditional generator and its mass in the whole distribution.
data KeyedBucket symbol constraint a = KeyedBucket
    { keyedBucketMass :: !Rational
    , keyedBucketStatic :: !(Static symbol constraint a)
    }

-- | Group enumerated outcomes by key.
groupOutcomes :: (Ord key) => [(key, Outcome symbol value)] -> Map.Map key [Outcome symbol value]
groupOutcomes = Map.fromListWith (flip (<>)) . map (fmap pure)

-- | Build one retained group from its outcomes, in rank order.
bucketFromOutcomes ::
    (Constraint constraint, Hashable symbol, Typeable symbol) =>
    Bool -> [Outcome symbol a] -> Either GenError (KeyedBucket symbol constraint a)
bucketFromOutcomes retainAtomic outcomes = do
    sampler <- sequenceSampler conditional
    pure
        $ KeyedBucket bucketMass
        $ Static
            bucketSupport
            ( mkOutcomeIndex
                totalOutcomes
                uniformMass
                select
                selectValue
                sampler
                (PlanSelect totalOutcomes selectValue)
            )
            retainAtomic
            (Inspection Nothing $ Node [inspectionEdge $ outcomeInspection outcome | outcome <- outcomes])
  where
    bucketMass = sum $ map outcomeMass outcomes
    conditional =
        Sequence.fromList
            [ outcome{outcomeMass = outcomeMass outcome / bucketMass}
            | outcome <- outcomes
            ]
    totalOutcomes = toInteger $ length outcomes
    uniformMass = commonValue $ Just . outcomeMass <$> toList conditional
    bucketSupport = Node [termEdge $ outcomeTerm outcome | outcome <- outcomes]
    termEdge (Tree.Node symbol children) = Edge symbol $ map singletonNode children
    inspectionEdge (Tree.Node symbol children) = Edge symbol $ map singletonNode children

    select index = do
        checkIndex totalOutcomes index
        pure $ Sequence.index conditional $ fromInteger index

    selectValue = outcomeValue . Sequence.index conditional . fromInteger

-- | Merge weighted static languages into one group.
mergeBucketGroup ::
    (Constraint constraint, Hashable symbol, Typeable symbol) =>
    [(Rational, Static symbol constraint a)] -> Either GenError (KeyedBucket symbol constraint a)
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
    (Constraint constraint, Ord resultKey, Hashable symbol, Typeable symbol) =>
    [(resultKey, Rational, Static symbol constraint a)] ->
    Either GenError (Map.Map resultKey (KeyedBucket symbol constraint a))
mergeComponentsByKey [] = Left EmptyGenerator
mergeComponentsByKey components = do
    unnormalized <- traverse mergeBucketGroup grouped
    let totalAcceptedMass = sum $ keyedBucketMass <$> unnormalized
    pure $ fmap (normalizeBucket totalAcceptedMass) unnormalized
  where
    grouped =
        foldl'
            ( \groups (resultKey, mass, static) ->
                Map.insertWith
                    (flip (<>))
                    resultKey
                    [(mass, static)]
                    groups
            )
            Map.empty
            components

    normalizeBucket totalAcceptedMass bucket =
        bucket
            { keyedBucketMass =
                keyedBucketMass bucket / totalAcceptedMass
            }
