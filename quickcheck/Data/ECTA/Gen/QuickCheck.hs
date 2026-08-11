{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | QuickCheck integration for indexed ECTA generators.
module Data.ECTA.Gen.QuickCheck (
    Indexed (..),
    ECTAGen,
    ECTAGenError (..),
    fromIndexed,
    elements,
    frequency,
    innerJoinOn,
    support,
    pmf,
    fromGen,
    toGen,
    toGenEither,
) where

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

-- | Lift one finite indexed source into transparent ECTA structure.
fromIndexed :: Indexed a -> ECTAGen a
fromIndexed = ECTA.fromIndexed

-- | Choose uniformly from a finite non-empty list.
elements :: [a] -> ECTAGen a
elements = ECTA.elements

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

-- | Return the ECTA support of a fully transparent generator.
support :: ECTAGen a -> Either ECTAGenError Node
support = ECTA.support

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

-- | Sample through the generator type expected by QuickCheck.
toGen :: ECTAGen a -> QC.Gen a
toGen generator =
    either (error . ("ECTAGen: " <>) . show) id <$> toGenEither generator
