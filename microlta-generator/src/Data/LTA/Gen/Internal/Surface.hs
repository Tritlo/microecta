{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}

{- | The source constructors and the preparation of deferred imports.

These functions build a generator without a solver. 'prepareGenerator'
completes a source that still holds a deferred 'fromLTA' import, and rebuilds
it with the same constructors.
-}
module Data.LTA.Gen.Internal.Surface (
    -- * Refined sources
    refined,
    pool,
    minimizePoolBy,
    leaf,

    -- * Tree constructors
    node,
    refinedNode,
    refinedNodeBy,
    refinedNodeByRoots,
    unary,
    binary,
    frequency,
    oneof,
    fromLTA,
    fromDatatypeUpToDepth,

    -- * Inspection and preparation
    support,
    prepareGenerator,
) where

import Data.Bifunctor (first)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.String (fromString)
import qualified Data.Text as Text
import qualified Data.Tree as Tree

import qualified Data.CFTA as FTA
import Data.CFTA.Generic (TypedFTA, constructorLabel, datatypeFTA, decodeLabelledTerm)
import Data.CFTA.Refinement
import Data.CFTA.Refinement.Expression (true)
import Data.CFTA.Refinement.Guard (GuardBuilder, buildGuard, guardArgumentCount)
import Data.LTA.Gen.Internal.AutomatonCompile (compileBoundedAutomaton)
import Data.LTA.Gen.Internal.Error (GeneratorError (..))
import Data.LTA.Gen.Internal.Recipe (childRecipeArity, knownEmptyRecipe, validateGenerator)
import Data.LTA.Gen.Internal.Replay (compiledSource)
import Data.LTA.Gen.Internal.Types
import Data.LTA.Gen.Internal.Witness (Witness (..), compileWitnesses)

-- | Build one refined pool entry.
refined :: a -> Symbol -> Refinement -> Refined a
refined = Refined

{- | Build a finite source whose shrink order is discovered from refinements.

At compile time, an entry may shrink to another entry when its refinement
implies the candidate refinement. Strict implication always shrinks; equivalent
refinements shrink toward the earlier pool entry, preventing cycles. Repeated
entries remain repeated ranks and retain empirical weight.
-}
pool :: [Refined a] -> LTAGen a
pool entries =
    LTAGen
        ( Just $
            Prepared
                ( finiteFromList
                    [ Outcome 1 value (Witness symbol refinement unconstrainedConstraint [])
                    | Refined value symbol refinement <- entries
                    ]
                )
                shrinkFrom
        )
        (Right $ PoolRecipe entries)
  where
    shrinkFrom source = case drop (fromInteger source) entries of
        Refined _ _ sourceRefinement : _ ->
            [ ShrinkCandidate
                target
                ( WeakenRefinement
                    sourceRefinement
                    candidateRefinement
                    (target < source)
                )
            | (target, Refined _ _ candidateRefinement) <- zip [0 :: Integer ..] entries
            , target /= source
            ]
        [] -> []

{- | Retain the most specific semantic representatives in each similarity
class through the core LTA @Similarity@ and @Minimize@ procedures.

The pool is represented as a one-state LTA whose transition refinements are the
entry annotations. The projection supplies the non-liquid type class used by
'refinementSubtypingBy'. Within one class, a subtype replaces its supertype;
equivalent refinements keep the earlier entry. Incomparable entries remain.
This operation is opt-in: ordinary QuickCheck pools should keep syntactically
distinct values when broad coverage matters more than semantic representatives.
-}
minimizePoolBy ::
    (Eq key) =>
    Entailment ->
    (a -> key) ->
    [Refined a] ->
    IO (Either GeneratorError (LTAGen a))
minimizePoolBy _ _ [] = pure $ Left EmptyGenerator
minimizePoolBy entailment similarityKey entries =
    case mkAutomaton poolState [(poolState, poolTransitions)] of
        Left err -> pure $ Left $ InvalidSupport err
        Right automaton -> do
            inferred <- similarity (refinementSubtypingBy entailment classify) automaton
            pure $ do
                related <- first InvalidSimilarity inferred
                reduced <- first InvalidMinimization $ minimize automaton related
                let retained =
                        Set.fromList
                            [ transitionSymbol transition
                            | transition <- Map.findWithDefault [] poolState $ automatonTransitions reduced
                            ]
                pure . pool $
                    [ entry
                    | (symbol, entry) <- zip poolSymbols entries
                    , Set.member symbol retained
                    ]
  where
    poolState = State 0
    poolSymbols = map poolSymbol [0 :: Int .. length entries - 1]
    poolTransitions =
        [ Transition symbol refinement [] unconstrainedConstraint
        | (symbol, Refined _ _ refinement) <- zip poolSymbols entries
        ]
    classes =
        Map.fromList
            [ (symbol, similarityKey value)
            | (symbol, Refined value _ _) <- zip poolSymbols entries
            ]
    classify transition = Map.lookup (transitionSymbol transition) classes

    poolSymbol index = fromString $ "__microlta_pool_" <> show index

-- | Build a singleton refined leaf.
leaf :: a -> Symbol -> Refinement -> LTAGen a
leaf value symbol refinement = pool [refined value symbol refinement]

{- | Add one annotated constructor around a generated child forest.

With @ApplicativeDo@ and @QualifiedDo@, use this as:

@node symbol guard $ LTA.do ...@

The result refinement defaults to the universally accepting refinement. Use
'refinedNode' when the constructor establishes a more precise result.
-}
node :: (NodeLayer layer, GuardBuilder guard) => Symbol -> guard -> layer a -> LTAGen a
node symbol = refinedNode symbol true

-- | Add a constructor with an explicit result refinement and liquid guard.
refinedNode ::
    (NodeLayer layer, GuardBuilder guard) =>
    Symbol ->
    Refinement ->
    guard ->
    layer a ->
    LTAGen a
refinedNode symbol refinement = closeNode symbol (FixedRefinement refinement)

{- | Add a constructor whose result refinement is computed from each generated
value.

Only the explicit 'validOutcomes' diagnostic evaluates this function.
Compilation rejects it because an arbitrary Haskell function has no symbolic
interpretation. Use 'refinedNodeByRoots' for compiled generators.
-}
refinedNodeBy ::
    (NodeLayer layer, GuardBuilder guard) =>
    Symbol ->
    (a -> Refinement) ->
    guard ->
    layer a ->
    LTAGen a
refinedNodeBy symbol refinementOf = closeNode symbol (ComputedRefinement refinementOf)

{- | Compute a node refinement from the labels and refinements of its children.

Compilation calls this function once per child observation group. The explicit
diagnostic evaluator applies the same function to each candidate's child roots.
-}
refinedNodeByRoots ::
    (NodeLayer layer, GuardBuilder guard) =>
    Symbol ->
    ([RootObservation] -> Refinement) ->
    guard ->
    layer a ->
    LTAGen a
refinedNodeByRoots symbol refinementOfRoots =
    closeNode symbol (RootComputedRefinement refinementOfRoots)

-- | Shared node constructor for fixed and value-computed refinements.
closeNode ::
    (NodeLayer layer, GuardBuilder guard) =>
    Symbol ->
    NodeRefinement a ->
    guard ->
    layer a ->
    LTAGen a
closeNode symbol nodeRefinement guardBuilder layer =
    LTAGen
        (closePrepared <$> childrenPrepared childForest)
        (childrenRecipe childForest >>= checkedRecipe)
  where
    childForest = asChildren layer
    guard = buildGuard guardBuilder
    closePrepared prepared =
        Prepared (closeOutcome <$> childrenOutcomes prepared) (childrenShrinks prepared)
    checkedRecipe recipe =
        case guardArgumentCount guardBuilder of
            Just supplied
                | supplied /= childRecipeArity recipe ->
                    Left $ InvalidSupport $ GuardArityMismatch symbol (childRecipeArity recipe) supplied
            _ -> Right $ NodeRecipe symbol nodeRefinement guard recipe
    closeOutcome outcome =
        Outcome
            (forestWeight outcome)
            (forestValue outcome)
            (Witness symbol (outcomeRefinement nodeRefinement outcome) guard $ forestWitnesses outcome)

-- | Use one refinement rule for a complete constructor witness.
outcomeRefinement :: NodeRefinement a -> ForestOutcome a -> Refinement
outcomeRefinement (FixedRefinement refinement) _ = refinement
outcomeRefinement (ComputedRefinement project) outcome = project $ forestValue outcome
outcomeRefinement (RootComputedRefinement project) outcome =
    project [RootObservation (witnessSymbol witness) (witnessRefinement witness) | witness <- forestWitnesses outcome]

-- | Apply a unary constructor to every member of a language.
unary :: (GuardBuilder guard) => (a -> b) -> Symbol -> Refinement -> guard -> LTAGen a -> LTAGen b
unary function symbol refinement guard generator =
    refinedNode symbol refinement guard (function <$> generator)

-- | Apply a binary constructor to the Cartesian product of two languages.
binary ::
    (GuardBuilder guard) =>
    (a -> b -> c) ->
    Symbol ->
    Refinement ->
    guard ->
    LTAGen a ->
    LTAGen b ->
    LTAGen c
binary function symbol refinement guard left right =
    refinedNode symbol refinement guard $
        applyChildren
            (children $ function <$> left)
            (children right)

-- | Combine alternatives with positive relative weights.
frequency :: [(Integer, LTAGen a)] -> Either GeneratorError (LTAGen a)
frequency [] = Left EmptyGenerator
frequency alternatives = do
    mapM_ ensurePositive alternatives
    pure $
        LTAGen
            (compilePrepared <$> traverse preparedAlternative alternatives)
            (ChoiceRecipe <$> traverse recipeAlternative alternatives)
  where
    preparedAlternative (weight, generator) = (,) weight <$> generatorPrepared generator
    compilePrepared prepared =
        let branches = withOffsets prepared
         in Prepared (finiteOneof $ map weightedOutcomes branches) (shrinkChoice branches)

    ensurePositive (weight, _)
        | weight > 0 = Right ()
        | otherwise = Left (NonPositiveWeight weight)

    weightedOutcomes (_, weight, generator, _) =
        fmap
            (\outcome -> outcome{outcomeWeight = weight * outcomeWeight outcome})
            (preparedOutcomes generator)

    recipeAlternative (weight, generator) =
        fmap (weight,) $ generatorRecipe generator

-- | Place each choice branch at its own offset in one combined rank domain.
withOffsets :: [(Integer, Prepared a)] -> [(Integer, Integer, Prepared a, Integer)]
withOffsets = go 0
  where
    go _ [] = []
    go offset ((weight, generator) : rest) =
        let count = finiteCardinality $ preparedOutcomes generator
         in (offset, weight, generator, count) : go (offset + count) rest

-- | Shrink toward every earlier non-empty branch, and within the selected one.
shrinkChoice :: [(Integer, Integer, Prepared a, Integer)] -> Integer -> [ShrinkCandidate]
shrinkChoice branches index = case break (\(offset, _, _, count) -> index < offset + count) branches of
    (_, []) -> []
    (earlier, (offset, _, generator, _) : _) ->
        [ ShrinkCandidate earlierOffset AlwaysShrink
        | (earlierOffset, _, _, earlierCount) <- earlier
        , earlierCount > 0
        ]
            <> [ liftShrink (offset +) candidate
               | candidate <- preparedShrinks generator (index - offset)
               ]

-- | Combine equally weighted alternatives.
oneof :: [LTAGen a] -> Either GeneratorError (LTAGen a)
oneof = frequency . map (1,)

{- | Use a core LTA as a generator source with an explicit tree-height bound.

Each distinct accepted term is one source member, even when several runs
accept it. The graph remains shared until 'compile' prepares the source.
The source composes with ordinary pools and constructors. A leaf has height
zero. Map the resulting terms to domain values with 'fmap'.
-}
fromLTA :: Int -> Automaton -> LTAGen (Tree.Tree LiquidSymbol)
fromLTA maximumHeight automaton =
    LTAGen Nothing $ Right $ AutomatonRecipe maximumHeight automaton

{- | Import a derived datatype with constructor refinements and liquid guards.

The grammar is bounded before LTA validation. The existing compiler determines
which terms satisfy the annotations. Its ranks and valid shrink graph remain
unchanged when the datatype codec supplies the generated Haskell values.
-}
fromDatatypeUpToDepth :: Int -> TypedFTA (Refinement, LiquidConstraint) a -> LTAGen a
fromDatatypeUpToDepth depth datatype =
    case annotateFTA annotate (FTA.boundDepth depth $ datatypeFTA datatype) of
        Left err -> LTAGen Nothing $ Left $ InvalidSupport err
        Right graph -> decode <$> fromLTA depth graph
  where
    annotate _ transition =
        let (refinement, constraint) = FTA.transitionGuard transition
         in (fromString $ constructorLabel $ FTA.transitionSymbol transition, refinement, constraint)
    decode term =
        case decodeLabelledTerm datatype (fmap (\(Symbol label) -> Text.unpack label) $ eraseRefinements term) of
            Just value -> value
            Nothing ->
                error
                    "microlta-generator bug in Data.LTA.Gen.Internal.Surface.fromDatatypeUpToDepth: \
                    \the derived codec rejected a term of its own grammar"

-- | Compile all candidates into one inspectable LTA support.
support :: LTAGen a -> Either GeneratorError Automaton
support generator = do
    validateGenerator generator
    case generatorPrepared generator of
        Nothing -> Left SourceRequiresCompilation
        Just _ -> Right ()
    outcomes <- enumerateFinite $ generatorOutcomes generator
    compileWitnesses $ map outcomeWitness outcomes

-- | Prepare deferred imports once while preserving pure source construction.
prepareGenerator :: Entailment -> LTAGen a -> IO (Either GeneratorError (LTAGen a))
prepareGenerator entailment generator =
    case generatorRecipe generator of
        Left err -> pure $ Left err
        Right recipe -> case generatorPrepared generator of
            Just _ -> pure $ Right generator
            Nothing -> prepareRecipe entailment recipe

-- | Rebuild only a recipe that contains an unresolved automaton source.
prepareRecipe :: Entailment -> Recipe a -> IO (Either GeneratorError (LTAGen a))
prepareRecipe _ recipe
    | knownEmptyRecipe recipe = pure $ Right $ pool []
prepareRecipe _ (PoolRecipe entries) = pure $ Right $ pool entries
prepareRecipe entailment (MapRecipe transform recipe) =
    fmap (fmap $ fmap transform) $ prepareRecipe entailment recipe
prepareRecipe entailment (NodeRecipe symbol refinement constraint childRecipe) =
    fmap (fmap $ closeNode symbol refinement constraint) $ prepareChildRecipe entailment childRecipe
prepareRecipe entailment (ChoiceRecipe alternatives) = do
    prepared <- traverse prepareAlternative alternatives
    pure $ sequence prepared >>= frequency
  where
    prepareAlternative (weight, recipe) =
        fmap (fmap $ (,) weight) $ prepareRecipe entailment recipe
prepareRecipe entailment (AutomatonRecipe maximumHeight automaton) = do
    compiled <-
        compileBoundedAutomaton
            entailment
            (\symbol refinement -> Tree.Node (LiquidSymbol symbol refinement))
            maximumHeight
            automaton
    pure $ case compiled of
        Left EmptyGenerator -> Right $ pool []
        Left err -> Left err
        Right source -> Right $ compiledSource source
prepareRecipe _ (CompiledRecipe compiled) = pure $ Right $ compiledSource compiled

-- | Prepare each direct child without evaluating the constructor's value.
prepareChildRecipe :: Entailment -> ChildRecipe a -> IO (Either GeneratorError (Children a))
prepareChildRecipe _ (PureChildRecipe value) = pure $ Right $ pure value
prepareChildRecipe entailment (OneChildRecipe recipe) =
    fmap (fmap children) $ prepareRecipe entailment recipe
prepareChildRecipe entailment (ApplyChildRecipe functions arguments) = do
    preparedFunctions <- prepareChildRecipe entailment functions
    preparedArguments <- prepareChildRecipe entailment arguments
    pure $ applyChildren <$> preparedFunctions <*> preparedArguments
