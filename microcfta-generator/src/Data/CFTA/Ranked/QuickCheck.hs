{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | QuickCheck lowering for finite ranked generators.
module Data.CFTA.Ranked.QuickCheck (
    QuickCheckBackend (..),
    toGen,
    toGenWithRank,
    forAll,
    forAllWith,
) where

import Data.Array (listArray, (!))
import Data.List (mapAccumL, sortOn)
import Data.Ord (Down (Down))
import qualified Test.QuickCheck as QC

import Data.CFTA.Index (Cardinality (..), Rank (..), Weight (..))
import qualified Data.CFTA.Ranked as Tree

{- | QuickCheck as the sampling backend.

The wrapper exists to avoid an orphan 'Tree.GenBackend' instance for 'QC.Gen'.
-}
newtype QuickCheckBackend a = QuickCheckBackend (QC.Gen a)
    deriving newtype (Functor, Applicative)

instance Tree.GenBackend QuickCheckBackend where
    selectInteger (Cardinality bound) =
        QuickCheckBackend $ Rank <$> QC.chooseInteger (0, bound - 1)

    selectInt bound =
        QuickCheckBackend $ QC.chooseInt (0, bound - 1)

    frequencyGen [] =
        error "microcfta-generator bug: no ranked QuickCheck alternative"
    frequencyGen alternatives =
        let ordered = sortOn (Down . fst) alternatives
            (total, cumulative) = mapAccumL accumulateWeight 0 ordered
            lastIndex = length cumulative - 1
            table = listArray (0, lastIndex) cumulative
            -- Search for the first alternative whose upper bound is above
            -- the selected ticket. The upper bounds do not decrease, so a
            -- binary search finds the alternative that a linear scan finds.
            pick selected low high
                | low == high = case snd (table ! low) of QuickCheckBackend generated -> generated
                | selected < fst (table ! middle) = pick selected low middle
                | otherwise = pick selected (middle + 1) high
              where
                middle = (low + high) `quot` 2
         in QuickCheckBackend $ do
                selected <-
                    if total <= toInteger (maxBound :: Int)
                        then toInteger <$> QC.chooseInt (0, fromInteger total - 1)
                        else QC.chooseInteger (0, total - 1)
                pick selected 0 lastIndex
      where
        accumulateWeight total (Weight weight, generated) =
            let upperBound = total + weight
             in (upperBound, (upperBound, generated))

    filterGen predicate (QuickCheckBackend generated) =
        QuickCheckBackend $ generated `QC.suchThat` predicate

-- | Lower a ranked language to a QuickCheck generator.
toGen :: Tree.Ranked a -> QC.Gen a
toGen ranked = case Tree.lower ranked of
    QuickCheckBackend generated -> generated

-- | Lower a ranked language with its deterministic replay rank.
toGenWithRank :: Tree.Ranked a -> QC.Gen (Rank, a)
toGenWithRank ranked = case Tree.lowerWithRank ranked of
    QuickCheckBackend generated -> generated

-- | Quantify over a ranked language and shrink only to valid members.
forAll :: (QC.Testable prop, Show a) => Tree.Ranked a -> (a -> prop) -> QC.Property
forAll ranked = forAllWith (toGenWithRank ranked) shrink
  where
    shrink rank =
        [ (candidate, value)
        | candidate <- Tree.shrinkRank ranked rank
        , Right value <- [Tree.unrank ranked candidate]
        ]

{- | Quantify over ranked members with a shrink function of the layer's
choosing, which maps a failing rank to candidate ranks and their members.
The failing rank is printed with the counterexample.
-}
forAllWith ::
    (QC.Testable prop, Show a) =>
    QC.Gen (Rank, a) ->
    (Rank -> [(Rank, a)]) ->
    (a -> prop) ->
    QC.Property
forAllWith ranked shrink prop =
    QC.forAllShrinkShow
        ranked
        (shrink . fst)
        (\(rank, value) -> "rank " <> show rank <> ": " <> show value)
        (prop . snd)
