{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | QuickCheck integration for indexed ECTA generators.
module Data.ECTA.Gen.QuickCheck (
    Indexed (..),
    ECTAGen,
    KeyedECTAGen,
    ECTAGenError (..),
    fromIndexed,
    elements,
    keyedElements,
    mapKeyed,
    innerJoin3Keyed,
    forgetKey,
    frequency,
    innerJoinOn,
    innerJoin3On,
    support,
    cardinality,
    unrank,
    countBy,
    pmf,
    fromGen,
    toGen,
    toGenEither,
    toGenWithRank,
    toGenWithRankEither,
) where

import Data.Map.Strict (Map)
import qualified Test.QuickCheck as QC

import Data.ECTA (Node)
import Data.ECTA.Gen (
    ECTAGenError (..),
    Indexed (..),
 )
import qualified Data.ECTA.Gen as ECTA

-- | The private wrapper avoids an orphan backend instance for 'QC.Gen'.
newtype QuickCheckBackend a = QuickCheckBackend (QC.Gen a)
    deriving newtype (Functor, Applicative)

instance ECTA.GenBackend QuickCheckBackend where
    selectInteger bound =
        QuickCheckBackend $ QC.chooseInteger (0, bound - 1)

    frequencyGen alternatives =
        QuickCheckBackend $ do
            let total = sum $ map fst alternatives
            selected <- QC.chooseInteger (0, total - 1)
            pick selected alternatives
      where
        pick _ [] = error "frequencyGen: impossible empty alternatives"
        pick selected ((weight, QuickCheckBackend generated) : remaining)
            | selected < weight = generated
            | otherwise = pick (selected - weight) remaining

    filterGen predicate (QuickCheckBackend generated) =
        QuickCheckBackend $ generated `QC.suchThat` predicate

-- | An indexed ECTA generator with QuickCheck as its opaque backend.
type ECTAGen = ECTA.ECTAGen QuickCheckBackend

-- | A partition-preserving ECTA generator with QuickCheck hidden as backend.
type KeyedECTAGen key = ECTA.KeyedECTAGen QuickCheckBackend key

-- | Lift one finite indexed source into transparent ECTA structure.
fromIndexed :: Indexed a -> ECTAGen a
fromIndexed = ECTA.fromIndexed

-- | Choose uniformly from a finite non-empty list.
elements :: [a] -> ECTAGen a
elements = ECTA.elements

-- | Uniformly choose from a finite source while retaining its key partitions.
keyedElements :: (Ord key) => (a -> key) -> [a] -> KeyedECTAGen key a
keyedElements = ECTA.keyedElements

-- | Map partition values without changing their retained keys.
mapKeyed :: (a -> b) -> KeyedECTAGen key a -> KeyedECTAGen key b
mapKeyed = ECTA.mapKeyed

-- | Join a keyed center with two keyed arguments and retain result partitions.
innerJoin3Keyed ::
    (Ord leftKey, Ord rightKey, Ord resultKey) =>
    (centerKey -> (leftKey, rightKey, resultKey)) ->
    KeyedECTAGen centerKey center ->
    KeyedECTAGen leftKey left ->
    KeyedECTAGen rightKey right ->
    KeyedECTAGen resultKey (center, left, right)
innerJoin3Keyed = ECTA.innerJoin3Keyed

-- | Forget retained keys while preserving the represented distribution.
forgetKey :: KeyedECTAGen key a -> ECTAGen a
forgetKey = ECTA.forgetKey

-- | Choose one generator with the supplied positive relative weight.
frequency :: [(Integer, ECTAGen a)] -> ECTAGen a
frequency = ECTA.frequency

-- | Condition independently generated values on equal projected keys.
innerJoinOn ::
    (Ord key) =>
    (left -> key) ->
    (right -> key) ->
    ECTAGen left ->
    ECTAGen right ->
    ECTAGen (left, right)
innerJoinOn = ECTA.innerJoinOn

-- | Condition a center value and two arguments on two projected key equalities.
innerJoin3On ::
    (Ord leftKey, Ord rightKey) =>
    (center -> (leftKey, rightKey)) ->
    (left -> leftKey) ->
    (right -> rightKey) ->
    ECTAGen center ->
    ECTAGen left ->
    ECTAGen right ->
    ECTAGen (center, left, right)
innerJoin3On = ECTA.innerJoin3On

-- | Return the ECTA support of a fully transparent generator.
support :: ECTAGen a -> Either ECTAGenError Node
support = ECTA.support

-- | Return the exact number of ranks in a transparent generator.
cardinality :: ECTAGen a -> Either ECTAGenError Integer
cardinality = ECTA.cardinality

-- | Decode one stable rank from a transparent generator.
unrank :: ECTAGen a -> Integer -> Either ECTAGenError a
unrank = ECTA.unrank

-- | Count ranked outcomes by a projected key.
countBy :: (Ord key) => (a -> key) -> ECTAGen a -> Either ECTAGenError (Map key Integer)
countBy = ECTA.countBy

-- | Aggregate the exact PMF of a fully transparent generator.
pmf :: (Ord a) => ECTAGen a -> Either ECTAGenError [(a, Rational)]
pmf = ECTA.pmf

-- | Embed an ordinary QuickCheck generator as an opaque region.
fromGen :: QC.Gen a -> ECTAGen a
fromGen = ECTA.fromBackend . QuickCheckBackend

-- | Sample while retaining structured generator errors.
toGenEither :: ECTAGen a -> QC.Gen (Either ECTAGenError a)
toGenEither generator = case ECTA.lower generator of
    QuickCheckBackend generated -> generated

-- | Sample a transparent generator while retaining its stable rank and errors.
toGenWithRankEither :: ECTAGen a -> QC.Gen (Either ECTAGenError (Integer, a))
toGenWithRankEither generator = case ECTA.lowerWithRank generator of
    QuickCheckBackend generated -> generated

-- | Sample through the generator type expected by QuickCheck.
toGen :: ECTAGen a -> QC.Gen a
toGen generator =
    either (error . ("ECTAGen: " <>) . show) id <$> toGenEither generator

-- | Sample a transparent generator together with its stable replay rank.
toGenWithRank :: ECTAGen a -> QC.Gen (Integer, a)
toGenWithRank generator =
    either (error . ("ECTAGen: " <>) . show) id
        <$> toGenWithRankEither generator
