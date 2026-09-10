{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | QuickCheck lowering for finite ranked generators.
module Data.Tree.Gen.QuickCheck (
    toGen,
    toGenWithRank,
    forAll,
) where

import Data.List (mapAccumL, sortOn)
import Data.Ord (Down (Down))
import qualified Test.QuickCheck as QC

import qualified Data.Tree.Gen as Tree

newtype QuickCheckBackend a = QuickCheckBackend (QC.Gen a)
    deriving newtype (Functor, Applicative)

instance Tree.GenBackend QuickCheckBackend where
    selectInteger bound =
        QuickCheckBackend $ QC.chooseInteger (0, bound - 1)

    selectInt bound =
        QuickCheckBackend $ QC.chooseInt (0, bound - 1)

    frequencyGen alternatives =
        let ordered = sortOn (Down . fst) alternatives
            (total, cumulative) = mapAccumL accumulateWeight 0 ordered
         in QuickCheckBackend $ do
                selected <-
                    if total <= toInteger (maxBound :: Int)
                        then toInteger <$> QC.chooseInt (0, fromInteger total - 1)
                        else QC.chooseInteger (0, total - 1)
                pick selected cumulative
      where
        accumulateWeight total (weight, generated) =
            let upperBound = total + weight
             in (upperBound, (upperBound, generated))

        pick _ [] =
            error "microecta-generator bug: no ranked QuickCheck alternative"
        pick selected ((upperBound, QuickCheckBackend generated) : remaining)
            | selected < upperBound = generated
            | otherwise = pick selected remaining

    filterGen predicate (QuickCheckBackend generated) =
        QuickCheckBackend $ generated `QC.suchThat` predicate

-- | Lower a ranked language to a QuickCheck generator.
toGen :: Tree.Ranked a -> QC.Gen a
toGen ranked = case Tree.lower ranked of
    QuickCheckBackend generated -> generated

-- | Lower a ranked language with its deterministic replay rank.
toGenWithRank :: Tree.Ranked a -> QC.Gen (Integer, a)
toGenWithRank ranked = case Tree.lowerWithRank ranked of
    QuickCheckBackend generated -> generated

-- | Quantify over a ranked language and shrink only to valid members.
forAll :: (QC.Testable prop, Show a) => Tree.Ranked a -> (a -> prop) -> QC.Property
forAll ranked prop =
    QC.forAllShrinkShow
        (toGenWithRank ranked)
        shrink
        (\(rank, value) -> "rank " <> show rank <> ": " <> show value)
        (prop . snd)
  where
    shrink (rank, _) =
        [ (candidate, value)
        | candidate <- Tree.shrinkRank ranked rank
        , Right value <- [Tree.unrank ranked candidate]
        ]
