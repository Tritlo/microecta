-- | QuickCheck-facing syntax for compiled liquid tree generators.
module Data.LTA.Gen.QuickCheck (
    module Data.LTA.Gen,
    module Data.LTA.Gen.Do,
    samplePool,
    freeze,
    compileSampled,
    toGen,
    toGenWithRank,
    forAll,
) where

import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import Prelude hiding ((>>=))
import qualified Prelude

import Data.LTA (Entailment)
import Data.LTA.Gen
import Data.LTA.Gen.Do
import qualified Data.Tree.Gen.QuickCheck as Tree

{- | Freeze refined draws from a native QuickCheck generator into one pool.

Reuse the returned 'LTAGen' wherever several child positions should range over
the same finite universe. Repeated draws retain empirical sampling weight;
refinement implication determines shrinking when the language is compiled.
-}
samplePool :: Int -> QC.Gen (Refined a) -> QC.Gen (LTAGen a)
samplePool sampleCount native =
    pool <$> QC.vectorOf (max 0 sampleCount) native

{- | 'samplePool' with the draws fixed by a seed.

The native generator is run once at QuickCheck size 30, matching
'QC.generate'. The resulting pool has the same members and ranks in every run
under the same seed. Use 'QC.resize' on the native generator for another size.
-}
freeze :: Int -> Int -> QC.Gen (Refined a) -> LTAGen a
freeze seed sampleCount native =
    unGen (samplePool sampleCount native) (mkQCGen seed) 30

{- | Freeze every sampled pool once, then compile the resulting language.

The snapshot remains fixed for the lifetime of the returned 'Compiled' value,
so replay ranks and shrink edges stay stable. A single generator may sample
several independent pools before assembling the final 'LTAGen'.
-}
compileSampled :: Entailment -> QC.Gen (LTAGen a) -> IO (Either GeneratorError (Compiled a))
compileSampled entailment generated =
    QC.generate generated Prelude.>>= compile entailment

-- | Sample only the values of a compiled liquid language.
toGen :: Compiled a -> QC.Gen a
toGen compiled =
    generatedValue <$> Tree.toGen (compiledRanked compiled)

-- | Sample a value together with its deterministic replay rank.
toGenWithRank :: Compiled a -> QC.Gen (Integer, a)
toGenWithRank compiled =
    (\(rank, generated) -> (rank, generatedValue generated))
        <$> Tree.toGenWithRank (compiledRanked compiled)

-- | Quantify over accepted values and shrink along compiled liquid relations.
forAll :: (QC.Testable prop, Show a) => Compiled a -> (a -> prop) -> QC.Property
forAll compiled prop =
    QC.forAllShrinkShow
        (toGenWithRank compiled)
        shrink
        (\(rank, value) -> "rank " <> show rank <> ": " <> show value)
        (prop . snd)
  where
    shrink (rank, _) =
        [ (candidate, generatedValue generated)
        | candidate <- shrinkRank compiled rank
        , Right generated <- [select candidate compiled]
        ]
