-- | QuickCheck-facing syntax for compiled liquid tree generators.
module Data.LTA.Gen.QuickCheck (
    module Data.LTA.Gen,
    module Data.LTA.Gen.Do,
    OpaqueSource,
    opaqueSource,
    SampledChildren,
    opaquePool,
    sampledNode,
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

import qualified Data.Map.Strict as Map

import Data.LTA (
    Entailment,
    Guard (And, Satisfies),
    LiquidConstraint (constraintGuard),
    Refinement,
    Symbol,
    unPath,
 )
import Data.LTA.Gen
import Data.LTA.Gen.Do
import Data.LTA.Guard (GuardBuilder, buildGuard)
import qualified Data.Tree.Gen.QuickCheck as Tree

{- | A native generator that can use refinements demanded by its LTA context.

The first callback receives every positive direct requirement pushed into this
source. It may interpret them with 'QC.suchThat' or construct values directly.
The other callbacks describe the sampled value as one refined LTA leaf.
Compilation still checks the resulting refinement, so an incomplete or buggy
pushdown can lose candidates but cannot admit an invalid one.
-}
data OpaqueSource a = OpaqueSource
    { sourceGenerate :: [Refinement] -> QC.Gen a
    , sourceSymbol :: a -> Symbol
    , sourceRefinement :: a -> Refinement
    }

-- | Describe one refinement-aware opaque QuickCheck source.
opaqueSource ::
    ([Refinement] -> QC.Gen a) ->
    (a -> Symbol) ->
    (a -> Refinement) ->
    OpaqueSource a
opaqueSource = OpaqueSource

{- | Direct child pools awaiting one surrounding LTA guard.

The applicative instance preserves source order so the guard's first argument
maps to the first pool, its second argument to the second pool, and so on.
-}
data SampledChildren a = SampledChildren
    { sampledArity :: !Int
    , sampleChildren :: Map.Map Int [Refinement] -> QC.Gen (Children a)
    }

instance Functor SampledChildren where
    fmap transform sampled =
        sampled
            { sampleChildren = Prelude.fmap (Prelude.fmap transform) . sampleChildren sampled
            }

instance Applicative SampledChildren where
    pure value = SampledChildren 0 $ const $ Prelude.pure $ Prelude.pure value

    functions <*> arguments =
        SampledChildren
            (functionArity + argumentArity)
            sampleBoth
      where
        functionArity = sampledArity functions
        argumentArity = sampledArity arguments

        sampleBoth requirements =
            Prelude.fmap
                applyChildren
                (sampleChildren functions $ requirementsFor 0 functionArity requirements)
                Prelude.<*> sampleChildren arguments (requirementsFor functionArity argumentArity requirements)

-- | Freeze one refinement-aware source as one direct child pool.
opaquePool :: Int -> OpaqueSource a -> SampledChildren a
opaquePool sampleCount source =
    SampledChildren 1 $ \requirements ->
        children . pool . map annotate
            <$> QC.vectorOf
                (max 0 sampleCount)
                (sourceGenerate source $ Map.findWithDefault [] 0 requirements)
  where
    annotate value =
        refined
            value
            (sourceSymbol source value)
            (sourceRefinement source value)

{- | Sample direct opaque pools after pushing down required refinements.

Only positive @Satisfies [child] refinement@ atoms, including those in a
conjunction, are safe to push without seeing another child value. Semantic
subtyping, substitution, disjunction, negation, and nested positions remain in
the LTA and are checked normally during 'compile'.
-}
sampledNode ::
    (GuardBuilder guard) =>
    Symbol ->
    guard ->
    SampledChildren a ->
    QC.Gen (LTAGen a)
sampledNode symbol guardBuilder sampled =
    node symbol guard <$> sampleChildren sampled (directRequirements guard)
  where
    guard = buildGuard guardBuilder

-- | Rebase one slice of global child requirements onto a local applicative.
requirementsFor ::
    Int ->
    Int ->
    Map.Map Int [Refinement] ->
    Map.Map Int [Refinement]
requirementsFor offset count requirements =
    Map.fromList
        [ (index - offset, refinements)
        | (index, refinements) <- Map.toList requirements
        , index >= offset
        , index < offset + count
        ]

-- | Refinements unconditionally required at direct child positions.
directRequirements :: LiquidConstraint -> Map.Map Int [Refinement]
directRequirements = semanticRequirements . constraintGuard

semanticRequirements :: Guard -> Map.Map Int [Refinement]
semanticRequirements (Satisfies target refinement) =
    case unPath target of
        [index] -> Map.singleton index [refinement]
        _ -> Map.empty
semanticRequirements (And guards) =
    Map.unionsWith (<>) $ map semanticRequirements guards
semanticRequirements _ = Map.empty

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
