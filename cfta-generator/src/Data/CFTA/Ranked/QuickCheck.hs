{-# LANGUAGE DerivingStrategies #-}

-- | QuickCheck lowering for finite ranked generators.
module Data.CFTA.Ranked.QuickCheck (
    QuickCheckBackend (..),
    toGen,
    toGenWithRank,
    forAll,
    forAllWith,
) where

import Data.Array (listArray, (!))
import Data.List (mapAccumL)
import qualified Test.QuickCheck as QC

import Data.CFTA.Index (Cardinality (..), Rank (..), Weight (..))
import qualified Data.CFTA.Ranked as Ranked

{- | QuickCheck as the sampling backend.

The wrapper exists to avoid an orphan 'Ranked.GenBackend' instance for 'QC.Gen'.
-}
newtype QuickCheckBackend a = QuickCheckBackend (QC.Gen a)
    deriving newtype (Functor, Applicative)

instance Ranked.GenBackend QuickCheckBackend where
    selectInteger (Cardinality bound) =
        QuickCheckBackend $ Rank <$> QC.chooseInteger (0, bound - 1)

    selectInt bound =
        QuickCheckBackend $ QC.chooseInt (0, bound - 1)

    frequencyGen [] =
        error "cfta-generator bug: no ranked QuickCheck alternative"
    frequencyGen alternatives =
        let (total, cumulative) = mapAccumL accumulateWeight 0 alternatives
            lastIndex = length cumulative - 1
            table = listArray (0, lastIndex) cumulative
            -- Search for the first alternative whose upper bound is above
            -- the selected ticket. The alternatives keep the order the user
            -- gave them. The upper bounds do not decrease in any order, so a
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

-- | Lower a ranked language to a QuickCheck generator.
toGen :: Ranked.Ranked a -> QC.Gen a
toGen ranked = case Ranked.lower ranked of
    QuickCheckBackend generated -> generated

-- | Lower a ranked language with its deterministic replay rank.
toGenWithRank :: Ranked.Ranked a -> QC.Gen (Ranked.RankedValue a)
toGenWithRank ranked = case Ranked.lowerWithRank ranked of
    QuickCheckBackend generated -> generated

-- | Quantify over a ranked language and shrink only to valid members.
forAll :: (QC.Testable prop, Show a) => Ranked.Ranked a -> (a -> prop) -> QC.Property
forAll ranked = forAllWith (toGenWithRank ranked) shrink
  where
    shrink rank =
        [ Ranked.RankedValue candidate value
        | candidate <- Ranked.shrinkRank ranked rank
        , Right value <- [Ranked.unrank ranked candidate]
        ]

{- | Quantify over ranked members with a shrink function of the layer's
choosing, which maps a failing rank to candidate ranks and their members.
The failing rank is printed with the counterexample.
-}
forAllWith ::
    (QC.Testable prop, Show a) =>
    QC.Gen (Ranked.RankedValue a) ->
    (Rank -> [Ranked.RankedValue a]) ->
    (a -> prop) ->
    QC.Property
forAllWith ranked shrink prop =
    QC.forAllShrinkShow
        ranked
        (shrink . Ranked.valueRank)
        (\(Ranked.RankedValue rank value) -> "rank " <> show rank <> ": " <> show value)
        (prop . Ranked.rankedValue)
