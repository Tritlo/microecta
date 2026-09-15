{- | Symbolic compilation and explicit diagnostic enumeration.

'compile' prepares deferred imports, then asks the grouped solver path for
a compact plan. Unsupported guards and value-computed refinements produce
an error. 'validOutcomes' is the explicit complete-candidate diagnostic.
-}
module Data.LTA.Gen.Internal.Compile (
    compile,
    validOutcomes,
) where

import Data.Bifunctor (first)

import qualified Data.ECTA.Gen.QuickCheck as ECTA
import Data.LTA
import Data.LTA.Gen.Internal.Error (GeneratorError (..), fromRankedError)
import Data.LTA.Gen.Internal.Recipe (requiredImplications, transparentCompiled, validateGenerator)
import Data.LTA.Gen.Internal.Relational (ObservationKey, RecipeGroups, RelationalValue, acceptedAlphabet, acceptedSources, compileRecipe, ensureConsistentArities)
import Data.LTA.Gen.Internal.Replay (evaluateImplications, sourceShrinkRanks)
import qualified Data.LTA.Gen.Internal.SourceIndex as Source
import Data.LTA.Gen.Internal.Surface (prepareGenerator)
import Data.LTA.Gen.Internal.Types
import Data.LTA.Gen.Internal.Witness (cacheEntailment, checkWitness, validateWitness, witnessTerm)
import qualified Data.Tree.Gen as Tree

{- | Compile a generator with stable source ranks, weights, and valid shrinks.

The compiler first groups candidates by the observations their guards need.
If a guard or result refinement cannot be compiled symbolically, compilation
returns an error. Compilation preserves source order and the weight of repeated
draws. All solver work finishes
before sampling, replay, or shrinking.
-}
compile :: Entailment -> LTAGen a -> IO (Either GeneratorError (Compiled a))
compile uncachedEntailment generator
    | Left err <- validateGenerator generator = pure $ Left err
    | otherwise = do
        entailment <- cacheEntailment uncachedEntailment
        prepared <- prepareGenerator entailment generator
        case prepared of
            Left err -> pure $ Left err
            Right source -> compilePreparedGenerator entailment source

-- | Compile a prepared source whose imports have fixed accepted rank domains.
compilePreparedGenerator :: Entailment -> LTAGen a -> IO (Either GeneratorError (Compiled a))
compilePreparedGenerator entailment generator =
    case generatorRecipe generator of
        Left err -> pure $ Left err
        Right recipe | Just compiled <- transparentCompiled recipe -> pure $ Right compiled
        Right recipe -> do
            grouped <- compileRecipe entailment [path []] recipe
            case grouped of
                Right prepared -> compileIndexedRecipe entailment generator prepared
                Left err -> pure $ Left err

-- | Compile accepted observation groups in their original source-rank order.
compileIndexedRecipe ::
    Entailment ->
    LTAGen a ->
    (ECTA.Grouped ObservationKey (RelationalValue a), RecipeGroups) ->
    IO (Either GeneratorError (Compiled a))
compileIndexedRecipe entailment generator (grouped, groups)
    | Source.cardinality sources == 0 = pure $ Left EmptyGenerator
    | otherwise = do
        table <- evaluateImplications entailment $ requiredImplications generator
        pure $ do
            ensureConsistentArities $ acceptedAlphabet groups
            acceptedSupport <- first InvalidECTAGenerator $ ECTA.support $ ECTA.ungroup grouped
            ranked <-
                first fromRankedError
                    $ Tree.fromWeightedIndexedOnDemand
                    $ Tree.WeightedIndexed
                        (Source.cardinality sources)
                        (Source.mass sources)
                        generatedAt
                        rankAtTicket
            pure $
                Compiled
                    (RelationalSupport acceptedSupport)
                    ranked
                    (\rank -> maybe [] (sourceShrinkRanks generator (Source.cardinality sources) (Source.rank sources) table) $ Source.select sources rank)
  where
    sources = acceptedSources groups
    generatedAt rank =
        case Source.select sources rank >>= either (const Nothing) Just . (`finiteSelect` generatorOutcomes generator) of
            Nothing -> error "microlta-generator bug in Data.LTA.Gen.Internal.Compile: invalid accepted source rank"
            Just outcome ->
                Generated (outcomeWeight outcome) (outcomeValue outcome) (witnessTerm $ outcomeWitness outcome)
    rankAtTicket ticket =
        case Source.selectByMass sources ticket >>= Source.rank sources of
            Just rank -> rank
            Nothing -> error "microlta-generator bug in Data.LTA.Gen.Internal.Compile: invalid sampling ticket"

-- | Check every complete candidate and keep the accepted ones in source order.
checkedOutcomes ::
    Entailment ->
    Finite (Outcome a) ->
    IO (Either GeneratorError [Accepted a])
checkedOutcomes entailment outcomes = go 0 []
  where
    total = finiteCardinality outcomes

    go sourceIndex accepted
        | sourceIndex >= total = pure (Right $ reverse accepted)
        | otherwise =
            case finiteSelect sourceIndex outcomes of
                Left err -> pure (Left err)
                Right outcome ->
                    case validateWitness (outcomeWitness outcome) of
                        Left err -> pure (Left err)
                        Right () -> do
                            verdict <- checkWitness entailment (outcomeWitness outcome)
                            case verdict of
                                Yes ->
                                    go
                                        (sourceIndex + 1)
                                        ( ( sourceIndex
                                          , outcome
                                          , Generated
                                                (outcomeWeight outcome)
                                                (outcomeValue outcome)
                                                (witnessTerm $ outcomeWitness outcome)
                                          )
                                            : accepted
                                        )
                                No -> go (sourceIndex + 1) accepted
                                Unknown -> pure (Left SolverUnknown)

-- | Check every candidate, preserving weights for the accepted members.
validOutcomes :: Entailment -> LTAGen a -> IO (Either GeneratorError [Generated a])
validOutcomes uncachedEntailment generator
    | Left err <- validateGenerator generator = pure $ Left err
    | otherwise = do
        entailment <- cacheEntailment uncachedEntailment
        prepared <- prepareGenerator entailment generator
        case prepared of
            Left err -> pure $ Left err
            Right source -> fmap (fmap $ map acceptedGenerated) $ checkedOutcomes entailment (generatorOutcomes source)
