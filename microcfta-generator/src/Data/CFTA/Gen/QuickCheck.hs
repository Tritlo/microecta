-- | QuickCheck integration and qualified-do syntax for ordinary generators.
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
import Data.CFTA.Ranked (Ranked)
import qualified Data.CFTA.Ranked.QuickCheck as Ranked

-- | Lower a finite generator to QuickCheck. A failed generator raises its own guidance.
toGen :: FTAGen symbol a -> QC.Gen a
toGen = Ranked.toGen . ranked "toGen"

-- | Lower with the stable replay rank selected by QuickCheck.
toGenWithRank :: FTAGen symbol a -> QC.Gen (Integer, a)
toGenWithRank = Ranked.toGenWithRank . ranked "toGenWithRank"

-- | Quantify over the exact language with structural rank shrinking.
forAll :: (QC.Testable prop, Show a) => FTAGen symbol a -> (a -> prop) -> QC.Property
forAll = Ranked.forAll . ranked "forAll"

-- | The ranked language, or the failure's own guidance.
ranked :: String -> FTAGen symbol a -> Ranked a
ranked caller = either (\err -> error $ caller <> ": " <> explain err) id . toRanked
