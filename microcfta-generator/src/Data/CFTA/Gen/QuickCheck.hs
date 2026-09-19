-- | QuickCheck integration and qualified-do syntax for ordinary FTA generators.
module Data.CFTA.Gen.QuickCheck (
    module Data.CFTA.Gen,
    module Data.CFTA.Gen.Do,
    toGen,
    toGenWithRank,
    forAll,
) where

import qualified Test.QuickCheck as QC

import Data.CFTA.Gen
import Data.CFTA.Gen.Do
import qualified Data.CFTA.Ranked.QuickCheck as Ranked

-- | Lower a finite FTA generator to QuickCheck.
toGen :: FTAGen symbol a -> QC.Gen a
toGen = Ranked.toGen . toRanked

-- | Lower with the stable replay rank selected by QuickCheck.
toGenWithRank :: FTAGen symbol a -> QC.Gen (Integer, a)
toGenWithRank = Ranked.toGenWithRank . toRanked

-- | Quantify over the exact FTA language with structural rank shrinking.
forAll :: (QC.Testable prop, Show a) => FTAGen symbol a -> (a -> prop) -> QC.Property
forAll generator = Ranked.forAll (toRanked generator)
