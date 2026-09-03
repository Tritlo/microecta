{-# LANGUAGE GADTs #-}

{- | Finite generators whose support is a liquid tree automaton.

'pool' supplies refined atoms. 'node' adds one constructor around an
applicatively-built child forest; "Data.LTA.Gen.Do" provides the corresponding
qualified-do syntax. 'compile' checks guards and refinement-shrink relations
once, then returns pure sampling, replay, and shrinking.
-}
module Data.LTA.Gen (
    LTAGen,
    Compiled,
    CompiledSupport (..),
    GeneratorError (..),
    Generated (..),

    -- * Refined sources
    Refined,
    refined,
    pool,
    minimizePoolBy,
    leaf,

    -- * Tree constructors
    node,
    refinedNode,
    refinedNodeBy,
    refinedNodeByRoots,
    RootObservation (..),
    unary,
    binary,
    frequency,
    oneof,
    fromAutomatonUpToDepth,

    -- * Compilation and inspection
    support,
    validOutcomes,
    compile,
    compileRelational,
    compileAutomaton,
    compileAutomatonWith,
    mapCompiled,
    compiledSupport,
    compiledRanked,
    cardinality,
    select,
    shrinkRank,
    smallerMembers,

    -- * Qualified-do support
    Children,
    NodeLayer (..),
    children,
    applyChildren,
) where

import Data.Bifunctor (first)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.List (nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.String (fromString)

import qualified Data.ECTA as ECTA.Core
import qualified Data.ECTA.Gen.QuickCheck as ECTA
import Data.ECTA.Paths (EqConstraints (EmptyConstraints))
import Data.LTA
import qualified Data.LTA.ECTA as LTAECTA
import Data.LTA.Guard (GuardBuilder, buildGuard)
import Data.LTA.Refinement (true)
import qualified Data.Tree.FTA as FTA
import qualified Data.Tree.Gen as Tree

{- | A finite weighted language paired with guarded witness trees and shrinks.

The outcome language is an indexed rank plan. Applicative composition retains
products as mixed-radix decoders, so constructing a generator does not allocate
one 'Outcome' for every element of its Cartesian product.
-}
data LTAGen a = LTAGen
    { generatorOutcomes :: !(Finite (Outcome a))
    , generatorShrinks :: Integer -> [ShrinkCandidate]
    , generatorRecipe :: !(Maybe (Recipe a))
    }

-- | Compositional source retained for solver-compiled grouped generation.
data Recipe a where
    PoolRecipe :: [Refined a] -> Recipe a
    MapRecipe :: (a -> b) -> Recipe a -> Recipe b
    NodeRecipe :: Symbol -> NodeRefinement a -> LiquidConstraint -> ChildRecipe a -> Recipe a
    ChoiceRecipe :: [(Integer, Recipe a)] -> Recipe a

-- | Whether a node refinement is known before decoding its domain value.
data NodeRefinement a
    = FixedRefinement !Refinement
    | ComputedRefinement (a -> Refinement)
    | RootComputedRefinement (a -> Refinement) ([RootObservation] -> Refinement)

-- | Symbol and refinement identifying one direct child relation group.
data RootObservation = RootObservation
    { observedSymbol :: !Symbol
    , observedRefinement :: !Refinement
    }
    deriving (Eq, Ord, Show)

-- | The free applicative child spine preserved by qualified do notation.
data ChildRecipe a where
    PureChildRecipe :: a -> ChildRecipe a
    OneChildRecipe :: Recipe a -> ChildRecipe a
    ApplyChildRecipe :: ChildRecipe (a -> b) -> ChildRecipe a -> ChildRecipe b

-- | Map a child forest without adding another generated child position.
fmapChildRecipe :: (a -> b) -> ChildRecipe a -> ChildRecipe b
fmapChildRecipe function recipe =
    ApplyChildRecipe (PureChildRecipe function) recipe

-- | A possibly empty wrapper around the shared non-empty ranked engine.
data Finite a
    = EmptyFinite
    | RankedFinite !(Tree.Ranked a)

instance Functor Finite where
    fmap _ EmptyFinite = EmptyFinite
    fmap function (RankedFinite ranked) = RankedFinite $ function <$> ranked

instance Applicative Finite where
    pure = RankedFinite . pure
    EmptyFinite <*> _ = EmptyFinite
    _ <*> EmptyFinite = EmptyFinite
    RankedFinite functions <*> RankedFinite arguments =
        RankedFinite $ functions <*> arguments

-- | Build a finite indexed language from an ordinary atomic pool.
finiteFromList :: [a] -> Finite a
finiteFromList [] = EmptyFinite
finiteFromList values =
    case Tree.fromWeighted [(1, value) | value <- values] of
        Right ranked -> RankedFinite ranked
        Left err -> error $ "finiteFromList: " <> show err

-- | Combine ranked branches without flattening their members.
finiteOneof :: [Finite a] -> Finite a
finiteOneof alternatives =
    case [ranked | RankedFinite ranked <- alternatives] of
        [] -> EmptyFinite
        rankedAlternatives ->
            case Tree.oneof rankedAlternatives of
                Right ranked -> RankedFinite ranked
                Left err -> error $ "finiteOneof: " <> show err

-- | Exact number of ranks without enumerating their values.
finiteCardinality :: Finite a -> Integer
finiteCardinality EmptyFinite = 0
finiteCardinality (RankedFinite ranked) = Tree.cardinality ranked

-- | Decode one valid rank.
finiteSelect :: Integer -> Finite a -> Either GeneratorError a
finiteSelect rank EmptyFinite = Left $ SelectionOutOfRange rank 0
finiteSelect rank (RankedFinite ranked) =
    first fromRankedError $ Tree.unrank ranked rank

-- | All valid ranks of a finite language.
finiteRanks :: Finite a -> [Integer]
finiteRanks finite = [0 .. finiteCardinality finite - 1]

-- | Materialize a finite language only for an explicit support observer.
enumerateFinite :: Finite a -> Either GeneratorError [a]
enumerateFinite finite = traverse (`finiteSelect` finite) $ finiteRanks finite

{- | One atom that can participate in refinement-based pool shrinking.

The refinement is trusted metadata; checking that an arbitrary Haskell value
satisfies it requires a separate value encoding.
-}
data Refined a = Refined !a !Symbol !Refinement

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
        ( finiteFromList
            [ Outcome 1 value (Witness symbol refinement unconstrainedConstraint [])
            | Refined value symbol refinement <- entries
            ]
        )
        shrinkFrom
        (Just $ PoolRecipe entries)
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

-- | A generated child forest awaiting one root constructor.
data Children a = Children
    { childrenOutcomes :: !(Finite (ForestOutcome a))
    , childrenShrinks :: Integer -> [ShrinkCandidate]
    , childrenRecipe :: !(Maybe (ChildRecipe a))
    }

data ForestOutcome a = ForestOutcome
    { forestWeight :: !Integer
    , forestValue :: a
    , forestWitnesses :: ![Witness]
    }

-- | Values that can be closed with one 'node'.
class NodeLayer layer where
    asChildren :: layer a -> Children a

instance NodeLayer LTAGen where
    asChildren = children

instance NodeLayer Children where
    asChildren = id

instance Functor LTAGen where
    fmap function generator =
        generator
            { generatorOutcomes =
                fmap
                    (\outcome -> outcome{outcomeValue = function (outcomeValue outcome)})
                    (generatorOutcomes generator)
            , generatorRecipe = MapRecipe function <$> generatorRecipe generator
            }

instance Functor Children where
    fmap function childForest =
        childForest
            { childrenOutcomes =
                fmap
                    (\outcome -> outcome{forestValue = function (forestValue outcome)})
                    (childrenOutcomes childForest)
            , childrenRecipe = fmap (fmapChildRecipe function) $ childrenRecipe childForest
            }

instance Applicative Children where
    pure value = Children (pure $ ForestOutcome 1 value []) (const []) (Just $ PureChildRecipe value)

    functions <*> arguments =
        Children
            (combine <$> functionOutcomes <*> argumentOutcomes)
            shrinkProduct
            (ApplyChildRecipe <$> childrenRecipe functions <*> childrenRecipe arguments)
      where
        functionOutcomes = childrenOutcomes functions
        argumentOutcomes = childrenOutcomes arguments
        argumentCount = finiteCardinality argumentOutcomes

        combine function argument =
            ForestOutcome
                (forestWeight function * forestWeight argument)
                (forestValue function $ forestValue argument)
                (forestWitnesses function <> forestWitnesses argument)

        shrinkProduct index
            | argumentCount <= 0 = []
            | otherwise =
                let (functionIndex, argumentIndex) = index `quotRem` argumentCount
                 in [ liftShrink
                        (\candidate -> candidate * argumentCount + argumentIndex)
                        shrink
                    | shrink <- childrenShrinks functions functionIndex
                    ]
                        <> [ liftShrink
                                (functionIndex * argumentCount +)
                                shrink
                           | shrink <- childrenShrinks arguments argumentIndex
                           ]

-- | Treat one LTA language as a one-child forest.
children :: LTAGen a -> Children a
children generator =
    Children
        ( toForest
            <$> generatorOutcomes generator
        )
        (generatorShrinks generator)
        (OneChildRecipe <$> generatorRecipe generator)
  where
    toForest outcome =
        ForestOutcome
            (outcomeWeight outcome)
            (outcomeValue outcome)
            [outcomeWitness outcome]

-- | Apply one generated child-forest function to another child forest.
applyChildren :: Children (a -> b) -> Children a -> Children b
applyChildren = (<*>)

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
refinedNode symbol refinement = closeNode symbol (FixedRefinement refinement) (const refinement)

{- | Add a constructor whose result refinement is computed from each generated
value.

This is useful for compositional refined languages: an operation such as
append can retain a symbolic result length derived from its selected children,
so a later node can use that result in another liquid guard.
-}
refinedNodeBy ::
    (NodeLayer layer, GuardBuilder guard) =>
    Symbol ->
    (a -> Refinement) ->
    guard ->
    layer a ->
    LTAGen a
refinedNodeBy symbol refinementOf = closeNode symbol (ComputedRefinement refinementOf) refinementOf

{- | Compute a node refinement from both its value and its child root groups.

The first projection is used by the complete-witness compiler. The second is
used once per relational group and must agree with the first for every value in
that group. This makes result-state propagation explicit without enumerating
the values hidden under a group.
-}
refinedNodeByRoots ::
    (NodeLayer layer, GuardBuilder guard) =>
    Symbol ->
    (a -> Refinement) ->
    ([RootObservation] -> Refinement) ->
    guard ->
    layer a ->
    LTAGen a
refinedNodeByRoots symbol refinementOf refinementOfRoots =
    closeNode
        symbol
        (RootComputedRefinement refinementOf refinementOfRoots)
        refinementOf

-- | Shared node constructor for fixed and value-computed refinements.
closeNode ::
    (NodeLayer layer, GuardBuilder guard) =>
    Symbol ->
    NodeRefinement a ->
    (a -> Refinement) ->
    guard ->
    layer a ->
    LTAGen a
closeNode symbol nodeRefinement refinementOf guardBuilder layer =
    LTAGen
        ( closeOutcome
            <$> childrenOutcomes childForest
        )
        (childrenShrinks childForest)
        (NodeRecipe symbol nodeRefinement guard <$> childrenRecipe childForest)
  where
    childForest = asChildren layer
    guard = buildGuard guardBuilder
    closeOutcome outcome =
        Outcome
            (forestWeight outcome)
            (forestValue outcome)
            (Witness symbol (refinementOf $ forestValue outcome) guard $ forestWitnesses outcome)

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
            (finiteOneof $ map weightedOutcomes branches)
            (shrinkChoice branches)
            (ChoiceRecipe <$> traverse recipeAlternative alternatives)
  where
    branches = withOffsets alternatives

    ensurePositive (weight, _)
        | weight > 0 = Right ()
        | otherwise = Left (NonPositiveWeight weight)

    weightedOutcomes (_, weight, generator, _) =
        fmap
            (\outcome -> outcome{outcomeWeight = weight * outcomeWeight outcome})
            (generatorOutcomes generator)

    recipeAlternative (weight, generator) =
        fmap (\recipe -> (weight, recipe)) $ generatorRecipe generator

-- | Combine equally weighted alternatives.
oneof :: [LTAGen a] -> Either GeneratorError (LTAGen a)
oneof = frequency . map (\generator -> (1, generator))

{- | Unfold an LTA into a finite generator up to a maximum constructor depth.

Depth zero contains only nullary transitions. A recursive transition consumes
one unit of depth before its children are expanded, so cyclic LTAs become
ordinary finite 'LTAGen' values before solver compilation. Unproductive
transitions are omitted; an entirely unproductive bound returns
'EmptyGenerator'.
-}
fromAutomatonUpToDepth :: Int -> Automaton -> Either GeneratorError (LTAGen LiquidTerm)
fromAutomatonUpToDepth maximumDepth automaton
    | maximumDepth < 0 = Left EmptyGenerator
    | otherwise = build maximumDepth (automatonInitial automaton)
  where
    build :: Int -> State -> Either GeneratorError (LTAGen LiquidTerm)
    build remaining state =
        oneof
            [ generated
            | transition <- Map.findWithDefault [] state $ automatonTransitions automaton
            , Right generated <- [buildTransition remaining transition]
            ]

    buildTransition :: Int -> Transition -> Either GeneratorError (LTAGen LiquidTerm)
    buildTransition remaining transition
        | null childStates = Right $ closeTransition transition (pure [] :: Children [LiquidTerm])
        | remaining <= 0 = Left EmptyGenerator
        | otherwise = do
            childGenerators <- traverse (build $ remaining - 1) childStates
            pure $
                closeTransition transition $
                    foldr
                        prependChild
                        (pure [])
                        childGenerators
      where
        childStates = transitionChildren transition

    prependChild :: LTAGen LiquidTerm -> Children [LiquidTerm] -> Children [LiquidTerm]
    prependChild child rest =
        (:) <$> children child <*> rest

    closeTransition :: Transition -> Children [LiquidTerm] -> LTAGen LiquidTerm
    closeTransition transition childForest =
        refinedNode
            (transitionSymbol transition)
            (transitionRefinement transition)
            (transitionConstraint transition)
            ( makeTerm
                <$> childForest
            )
      where
        makeTerm childTerms =
            LiquidTerm
                (transitionSymbol transition)
                (transitionRefinement transition)
                childTerms

-- | Compile all candidates into one inspectable LTA support.
support :: LTAGen a -> Either GeneratorError Automaton
support generator = do
    outcomes <- enumerateFinite $ generatorOutcomes generator
    compileWitnesses $ map outcomeWitness outcomes

-- | Check every candidate, preserving weights for the accepted members.
validOutcomes :: Entailment -> LTAGen a -> IO (Either GeneratorError [Generated a])
validOutcomes uncachedEntailment generator = do
    entailment <- cacheEntailment uncachedEntailment
    fmap (fmap $ map acceptedGenerated) $
        checkedOutcomes entailment (generatorOutcomes generator)

-- | The support retained by either compilation path.
data CompiledSupport
    = -- | Semantic pruning produced an equality-annotated generic FTA.
      EqualitySupport !EqualityAutomaton
    | -- | A grouped relational plan produced native hash-consed ECTA support.
      RelationalSupport !(ECTA.Core.Node Symbol)

-- | Solver-checked support paired with its pure ranked language and shrinks.
data Compiled a = Compiled
    { compiledSupport :: !CompiledSupport
    -- ^ The equality-layer support after every semantic guard is discharged.
    , compiledRanked :: !(Tree.Ranked (Generated a))
    -- ^ Pure sampling and replay after solver compilation.
    , compiledShrinkRanks :: !(Map.Map Integer [Integer])
    -- ^ Valid refinement and structural shrinks between accepted ranks.
    , compiledPlanShrinks :: !(Integer -> [Integer])
    -- ^ On-demand shrinks retained by a symbolic relational rank plan.
    }

-- | A checked generator member and its relative sampling weight.
data Generated a = Generated
    { generatedWeight :: !Integer
    , generatedValue :: a
    , generatedTerm :: LiquidTerm
    {- ^ The annotated witness. Automaton decoders build this lazily so sampling
    a mapped domain value does not pay for an intermediate 'LiquidTerm'.
    -}
    }
    deriving (Eq, Show)

-- | Failure while building, checking, or selecting from a generator.
data GeneratorError
    = EmptyGenerator
    | NonPositiveWeight !Integer
    | NegativeRank !Integer
    | SelectionOutOfRange !Integer !Integer
    | SolverUnknown
    | InvalidSupport !AutomatonError
    | InvalidPruning !PruneError
    | InvalidSimilarity !SimilarityError
    | InvalidMinimization !MinimizeError
    | InvalidECTAGenerator !ECTA.ECTAGenError
    | -- | The reduced equality fragment could not be represented by MicroECTA.
      InvalidEqualityView !LTAECTA.EqualityViewError
    | RelationalPlanUnavailable
    | RelationalComputedRefinement !Symbol
    | RelationalEqualityUnsupported !EqConstraints
    | -- | The sparse relational shortcut cannot inspect complete subtrees.
      RelationalSyntacticEqualityUnsupported !Guard
    | ResidualEquality !State !EqConstraints
    | RecursiveAutomaton
    | AmbiguousAutomaton !State
    deriving (Eq, Show)

-- | Discharge guards and refinement ordering once, producing a pure language.
compile :: Entailment -> LTAGen a -> IO (Either GeneratorError (Compiled a))
compile uncachedEntailment generator = do
    entailment <- cacheEntailment uncachedEntailment
    checked <- checkedOutcomes entailment (generatorOutcomes generator)
    case checked of
        Left err -> pure (Left err)
        Right accepted -> case compileAccepted accepted of
            Left err -> pure (Left err)
            Right (acceptedSupport, ranked) -> do
                implications <-
                    evaluateImplications
                        entailment
                        (requiredImplications generator)
                pure $ do
                    table <- implications
                    pure $
                        Compiled
                            (EqualitySupport acceptedSupport)
                            ranked
                            (buildShrinkTable generator accepted table)
                            (const [])

{- | Compile a compositional LTA generator as solver-approved ECTA joins.

Unlike 'compile', this path never scans the complete applicative witness
product. It retains qualified-do child structure, groups each child language by
the finite observations used by its parent guard, asks the solver once per live
observation tuple, and lowers accepted tuples through
'ECTA.relateGroupsM'. Fixed result refinements are known at that boundary;
'refinedNodeBy' remains on the general witness compiler because an arbitrary
Haskell projection may vary inside one relational group.
-}
compileRelational :: Entailment -> LTAGen a -> IO (Either GeneratorError (Compiled a))
compileRelational uncachedEntailment generator =
    case generatorRecipe generator of
        Nothing -> pure $ Left RelationalPlanUnavailable
        Just recipe
            | not $ uniformlyWeightedRecipe recipe ->
                pure $ Left RelationalPlanUnavailable
            | otherwise -> do
                entailment <- cacheEntailment uncachedEntailment
                compiled <- compileRecipe entailment [path []] recipe
                pure $ do
                    grouped <- compiled
                    let flattened = ECTA.ungroup grouped
                    total <- first InvalidECTAGenerator $ ECTA.cardinality flattened
                    ectaSupport <- first InvalidECTAGenerator $ ECTA.support flattened
                    ranked <-
                        first fromRankedError $
                            Tree.fromIndexedOnDemand $
                                Tree.Indexed total (relationalGeneratedAt flattened)
                    pure $
                        Compiled
                            (RelationalSupport ectaSupport)
                            ranked
                            Map.empty
                            (ECTA.shrinkRank flattened)

-- | Whether relational compilation preserves this recipe's source weights.
uniformlyWeightedRecipe :: Recipe a -> Bool
uniformlyWeightedRecipe (PoolRecipe _) = True
uniformlyWeightedRecipe (MapRecipe _ recipe) = uniformlyWeightedRecipe recipe
uniformlyWeightedRecipe (NodeRecipe _ _ _ childrenRecipe) = uniformlyWeightedChildren childrenRecipe
uniformlyWeightedRecipe (ChoiceRecipe alternatives) =
    all ((== 1) . fst) alternatives
        && all (uniformlyWeightedRecipe . snd) alternatives

-- | Whether every source below one applicative child spine is unit-weighted.
uniformlyWeightedChildren :: ChildRecipe a -> Bool
uniformlyWeightedChildren (PureChildRecipe _) = True
uniformlyWeightedChildren (OneChildRecipe recipe) = uniformlyWeightedRecipe recipe
uniformlyWeightedChildren (ApplyChildRecipe functions arguments) =
    uniformlyWeightedChildren functions && uniformlyWeightedChildren arguments

-- | The sparse liquid observations that identify one relational group.
newtype ObservationKey = ObservationKey
    { unObservationKey :: Map.Map Path RootObservation
    }
    deriving (Eq, Ord, Show)

-- | A domain value paired lazily with the witness selected at the same rank.
data RelationalValue a = RelationalValue a Witness

-- | One applicative result and its ordered child witnesses.
data RelationalForest a = RelationalForest a [Witness]

-- | Compile one retained recipe, grouped by the observations its parent needs.
compileRecipe ::
    Entailment ->
    [Path] ->
    Recipe a ->
    IO (Either GeneratorError (ECTA.Grouped ObservationKey (RelationalValue a)))
compileRecipe _ requested (PoolRecipe entries) =
    pure . Right . ECTA.frequencies $
        [ ( 1
          , ECTA.keyed
                (leafObservationKey requested symbol refinement)
                (ECTA.elements [RelationalValue value $ Witness symbol refinement unconstrainedConstraint []])
          )
        | Refined value symbol refinement <- entries
        ]
compileRecipe entailment requested (MapRecipe transform recipe) =
    fmap (fmap $ ECTA.mapWithKey mapValue) $
        compileRecipe entailment requested recipe
  where
    mapValue _ (RelationalValue value witness) =
        RelationalValue (transform value) witness
compileRecipe entailment requested (ChoiceRecipe alternatives) = do
    compiled <-
        traverse
            ( \(weight, recipe) ->
                fmap (fmap $ \grouped -> (weight, grouped)) $
                    compileRecipe entailment requested recipe
            )
            alternatives
    pure $ ECTA.frequencies . filter liveGroup <$> sequence compiled
  where
    liveGroup (_, grouped) = ECTA.sizes grouped /= Left ECTA.EmptyGenerator
compileRecipe _ _ (NodeRecipe symbol (ComputedRefinement _) _ _) =
    pure $ Left $ RelationalComputedRefinement symbol
compileRecipe entailment requested (NodeRecipe symbol nodeRefinement constraint childRecipe) = do
    let arity = childRecipeArity childRecipe
        needsChildRoots = case nodeRefinement of
            RootComputedRefinement _ _ -> True
            _ -> False
        rootPaths
            | needsChildRoots = [path [childIndex] | childIndex <- [0 .. arity - 1]]
            | otherwise = []
        observedPaths = nub $ requested <> constraintPaths constraint <> rootPaths
        childRequirements =
            [ nub
                [ path suffix
                | observed <- observedPaths
                , index : suffix <- [unPath observed]
                , index == childIndex
                ]
            | childIndex <- [0 .. arity - 1]
            ]
    compiledChildren <- compileChildRecipe entailment childRequirements childRecipe
    case compiledChildren of
        Left err -> pure $ Left err
        Right childGroups -> do
            filtered <-
                ECTA.filterGroupsM
                    ( \childKeys ->
                        constraintDecision
                            entailment
                            symbol
                            (refinementForChildren nodeRefinement childKeys)
                            constraint
                            childKeys
                    )
                    childGroups
            pure $
                fmap
                    ( ECTA.regroupBy closeKey
                        . ECTA.mapWithKey closeValue
                    )
                    filtered
  where
    closeKey childKeys =
        parentObservationKey
            requested
            symbol
            (refinementForChildren nodeRefinement childKeys)
            childKeys

    closeValue childKeys (RelationalForest value witnesses) =
        let observationKey = closeKey childKeys
         in RelationalValue value $
                Witness
                    symbol
                    (observationKeyRefinement observationKey)
                    constraint
                    witnesses

-- | Result refinement known for one tuple of direct child groups.
refinementForChildren :: NodeRefinement a -> [ObservationKey] -> Refinement
refinementForChildren (FixedRefinement refinement) _ = refinement
refinementForChildren (RootComputedRefinement _ project) childKeys =
    project $ map observationKeyRoot childKeys
refinementForChildren (ComputedRefinement _) _ =
    error "refinementForChildren: value-computed refinement reached relational compilation"

-- | Root observation retained by every relational group.
observationKeyRoot :: ObservationKey -> RootObservation
observationKeyRoot (ObservationKey observations) =
    case Map.lookup (path []) observations of
        Just rootObservation -> rootObservation
        Nothing -> error "microlta relational compiler: child group has no root observation"

-- | Root refinement retained by every relational group.
observationKeyRefinement :: ObservationKey -> Refinement
observationKeyRefinement = observedRefinement . observationKeyRoot

-- | Number of generated child positions in one free applicative spine.
childRecipeArity :: ChildRecipe a -> Int
childRecipeArity (PureChildRecipe _) = 0
childRecipeArity (OneChildRecipe _) = 1
childRecipeArity (ApplyChildRecipe functions arguments) =
    childRecipeArity functions + childRecipeArity arguments

-- | Compile a heterogeneous child spine while retaining its observation tuple.
compileChildRecipe ::
    Entailment ->
    [[Path]] ->
    ChildRecipe a ->
    IO (Either GeneratorError (ECTA.Grouped [ObservationKey] (RelationalForest a)))
compileChildRecipe _ _ (PureChildRecipe value) =
    pure . Right $
        ECTA.keyed [] $
            ECTA.elements [RelationalForest value []]
compileChildRecipe entailment requirements (OneChildRecipe recipe) = do
    compiled <- compileRecipe entailment (firstRequirements requirements) recipe
    pure $
        fmap
            ( ECTA.regroupBy pure
                . ECTA.mapWithKey
                    (\_ (RelationalValue value witness) -> RelationalForest value [witness])
            )
            compiled
  where
    firstRequirements (requirementsAtChild : _) = requirementsAtChild
    firstRequirements [] = []
compileChildRecipe entailment requirements (ApplyChildRecipe (PureChildRecipe function) arguments) = do
    compiled <- compileChildRecipe entailment requirements arguments
    pure $
        fmap
            ( ECTA.mapWithKey $ \_ (RelationalForest argument witnesses) ->
                RelationalForest (function argument) witnesses
            )
            compiled
compileChildRecipe entailment requirements (ApplyChildRecipe functions arguments) = do
    let functionArity = childRecipeArity functions
        (functionRequirements, argumentRequirements) = splitAt functionArity requirements
    compiledFunctions <- compileChildRecipe entailment functionRequirements functions
    compiledArguments <- compileChildRecipe entailment argumentRequirements arguments
    case (compiledFunctions, compiledArguments) of
        (Left err, _) -> pure $ Left err
        (_, Left err) -> pure $ Left err
        (Right functionGroups, Right argumentGroups) -> do
            related <-
                ECTA.relateGroupsM
                    (\_ _ -> pure $ Right True)
                    (<>)
                    functionGroups
                    argumentGroups
            pure $
                fmap
                    ( ECTA.mapWithKey $ \_ (RelationalForest function functionWitnesses, RelationalForest argument argumentWitnesses) ->
                        RelationalForest
                            (function argument)
                            (functionWitnesses <> argumentWitnesses)
                    )
                    related

-- | Decide one parent guard from the already-grouped child observations.
constraintDecision ::
    Entailment ->
    Symbol ->
    Refinement ->
    LiquidConstraint ->
    [ObservationKey] ->
    IO (Either GeneratorError Bool)
constraintDecision entailment symbol refinement constraint childKeys
    | constraintEqualities constraint /= EmptyConstraints =
        pure $ Left $ RelationalEqualityUnsupported $ constraintEqualities constraint
    | containsSyntacticEquality (constraintGuard constraint) =
        pure $ Left $ RelationalSyntacticEqualityUnsupported $ constraintGuard constraint
    | otherwise = do
        verdict <-
            evaluateGuardWith
                entailment
                ( \target -> do
                    RootObservation observedSymbol observedRefinement <- Map.lookup target observations
                    pure (observedSymbol, observedRefinement)
                )
                (constraintGuard constraint)
        pure $ case verdict of
            Yes -> Right True
            No -> Right False
            Unknown -> Left SolverUnknown
  where
    ObservationKey observations = completeObservationKey symbol refinement childKeys

-- | Sparse root observations cannot decide equality of complete subtrees.
containsSyntacticEquality :: Guard -> Bool
containsSyntacticEquality Top = False
containsSyntacticEquality Bottom = False
containsSyntacticEquality (Same _ _) = True
containsSyntacticEquality (Entails _ _) = False
containsSyntacticEquality (Satisfies _ _) = False
containsSyntacticEquality (Substitute _ nested) = containsSyntacticEquality nested
containsSyntacticEquality (Not nested) = containsSyntacticEquality nested
containsSyntacticEquality (And guards) = any containsSyntacticEquality guards
containsSyntacticEquality (Or guards) = any containsSyntacticEquality guards

-- | Observations needed above one accepted node.
parentObservationKey ::
    [Path] ->
    Symbol ->
    Refinement ->
    [ObservationKey] ->
    ObservationKey
parentObservationKey requested symbol refinement childKeys =
    ObservationKey $
        Map.restrictKeys observations $
            Set.insert (path []) $
                Set.fromList requested
  where
    ObservationKey observations = completeObservationKey symbol refinement childKeys

-- | Root plus the sparse observations retained by every direct child group.
completeObservationKey ::
    Symbol ->
    Refinement ->
    [ObservationKey] ->
    ObservationKey
completeObservationKey symbol refinement childKeys =
    ObservationKey $
        Map.fromList $
            (path [], RootObservation symbol refinement)
                : [ (path $ childIndex : unPath target, observed)
                  | (childIndex, ObservationKey childObservations) <- zip [0 ..] childKeys
                  , (target, observed) <- Map.toList childObservations
                  ]

-- | Available observations for one nullary source.
leafObservationKey :: [Path] -> Symbol -> Refinement -> ObservationKey
leafObservationKey requested symbol refinement =
    ObservationKey $
        if path [] `elem` requested
            then Map.singleton (path []) (RootObservation symbol refinement)
            else Map.empty

-- | Decode a valid ECTA rank into the public generated-member view.
relationalGeneratedAt :: ECTA.ECTAGen (RelationalValue a) -> Integer -> Generated a
relationalGeneratedAt generator rank =
    case ECTA.unrank generator rank of
        Left err -> error $ "compileRelational: invalid retained rank: " <> show err
        Right (RelationalValue value witness) ->
            Generated 1 value (witnessTerm witness)

{- | Prune and rank a finite acyclic LTA.

The core's authoritative 'prune' pass runs first. If no syntactic equality
remains, the adapter counts accepting runs by dynamic programming and only
'select' materializes the chosen 'LiquidTerm'. Positive equality residuals are
lowered explicitly to MicroECTA and use a correctness-first finite enumerator.
Recursive automata should first be unfolded to the desired generation bound.
-}
compileAutomaton :: Entailment -> Automaton -> IO (Either GeneratorError (Compiled LiquidTerm))
compileAutomaton entailment =
    compileAutomatonWith entailment LiquidTerm

{- | Compile an LTA while folding each selected transition directly into a value.

The annotated witness remains available through 'generatedTerm', but is lazy.
QuickCheck sampling that only demands 'generatedValue' therefore avoids
constructing and immediately decoding an intermediate 'LiquidTerm'.
-}
compileAutomatonWith ::
    Entailment ->
    (Symbol -> Refinement -> [a] -> a) ->
    Automaton ->
    IO (Either GeneratorError (Compiled a))
compileAutomatonWith uncachedEntailment buildValue automaton = do
    entailment <- cacheEntailment uncachedEntailment
    reduced <- pruneToECTA entailment automaton
    pure $ do
        acceptedSupport <- first InvalidPruning reduced
        ranked <- case ensureUnconstrained acceptedSupport of
            Right () -> compileUnconstrainedAutomaton buildValue acceptedSupport
            Left (ResidualEquality _ _) -> compileEqualityAutomaton buildValue acceptedSupport
            Left err -> Left err
        pure $ Compiled (EqualitySupport acceptedSupport) ranked Map.empty (const [])

-- | Count and unrank an equality-free reduced LTA as an ordinary FTA.
compileUnconstrainedAutomaton ::
    (Symbol -> Refinement -> [a] -> a) ->
    EqualityAutomaton ->
    Either GeneratorError (Tree.Ranked (Generated a))
compileUnconstrainedAutomaton buildValue acceptedSupport = do
    counts <- countAutomaton acceptedSupport
    ensureUnambiguous acceptedSupport $ Map.keys counts
    let total = Map.findWithDefault 0 (automatonInitial acceptedSupport) counts
    first fromRankedError $
        Tree.fromIndexedOnDemand $
            Tree.Indexed
                total
                (generatedAtWith buildValue acceptedSupport counts)

{- | Enumerate a positive-equality residual through the real MicroECTA core.

This is the correctness-first backend. It may materialize the finite accepted
language; future equality-aware counting can replace it without changing the
authoritative LTA or this compilation boundary.
-}
compileEqualityAutomaton ::
    (Symbol -> Refinement -> [a] -> a) ->
    EqualityAutomaton ->
    Either GeneratorError (Tree.Ranked (Generated a))
compileEqualityAutomaton buildValue acceptedSupport = do
    equalityView <- first InvalidEqualityView $ LTAECTA.toECTA acceptedSupport
    terms <-
        traverse
            (first InvalidEqualityView . LTAECTA.decodeTerm equalityView)
            (nub $ ECTA.Core.getAllTermsWith (-1) $ LTAECTA.equalityRoot equalityView)
    first fromRankedError $
        Tree.fromWeighted
            [ (1, Generated 1 (foldValue term) term)
            | term <- terms
            ]
  where
    foldValue (LiquidTerm symbol refinement childTerms) =
        buildValue symbol refinement $ map foldValue childTerms

{- | Require the pruned automaton to be an ordinary FTA before multiplying
child cardinalities.

Semantic guards are eliminated by LTA state splitting. Syntactic equality may
remain because equality between arbitrary subtrees is not a regular tree
language; it needs the ECTA counting path instead of an FTA product count.
-}
ensureUnconstrained :: EqualityAutomaton -> Either GeneratorError ()
ensureUnconstrained automaton =
    case [ (state, FTA.transitionGuard transition)
         | (state, transitions) <- Map.toList $ automatonTransitions automaton
         , transition <- transitions
         , FTA.transitionGuard transition /= EmptyConstraints
         ] of
        residual : _ -> Left $ uncurry ResidualEquality residual
        [] -> Right ()

{- | Change only the Haskell view of a compiled LTA member.

The accepted liquid term, stable rank, support automaton, and shrink graph are
unchanged.
-}
mapCompiled :: (a -> b) -> Compiled a -> Compiled b
mapCompiled transform compiled =
    compiled
        { compiledRanked = mapGenerated <$> compiledRanked compiled
        }
  where
    mapGenerated generated =
        generated{generatedValue = transform $ generatedValue generated}

-- | Count every reachable state of an acyclic automaton once.
countAutomaton :: EqualityAutomaton -> Either GeneratorError (Map.Map State Integer)
countAutomaton automaton =
    snd <$> countState Set.empty Map.empty (automatonInitial automaton)
  where
    table = automatonTransitions automaton

    countState visiting counts state =
        case Map.lookup state counts of
            Just count -> Right (count, counts)
            Nothing
                | Set.member state visiting -> Left RecursiveAutomaton
                | otherwise -> do
                    (transitionCounts, counted) <-
                        countTransitions
                            (Set.insert state visiting)
                            counts
                            (Map.findWithDefault [] state table)
                    let count = sum transitionCounts
                    pure (count, Map.insert state count counted)

    countTransitions _ counts [] = Right ([], counts)
    countTransitions visiting counts (transition : rest) = do
        (count, withChildren) <- countChildren visiting counts $ transitionChildren transition
        (restCounts, finished) <- countTransitions visiting withChildren rest
        pure (count : restCounts, finished)

    countChildren _ counts [] = Right (1, counts)
    countChildren visiting counts (state : rest) = do
        (count, withState) <- countState visiting counts state
        (restCount, finished) <- countChildren visiting withState rest
        pure (count * restCount, finished)

{- | Reject an automaton whose ranks would denote accepting runs rather than
distinct terms.

For an acyclic FTA, two alternatives overlap exactly when their liquid symbols
match and every corresponding pair of child-state languages intersects.
-}
ensureUnambiguous :: EqualityAutomaton -> [State] -> Either GeneratorError ()
ensureUnambiguous automaton = go
  where
    table = automatonTransitions automaton

    go [] = Right ()
    go (state : rest)
        | any (uncurry transitionsOverlap) $ distinctPairs $ transitions state =
            Left $ AmbiguousAutomaton state
        | otherwise = go rest

    transitions state = Map.findWithDefault [] state table

    stateLanguagesOverlap left right
        | Set.disjoint (rootSymbols left) (rootSymbols right) = False
        | otherwise =
            or
                [ transitionsOverlap leftTransition rightTransition
                | leftTransition <- transitions left
                , rightTransition <- transitions right
                ]

    transitionsOverlap left right =
        transitionSymbol left == transitionSymbol right
            && transitionRefinement left == transitionRefinement right
            && length leftChildren == length rightChildren
            && and
                ( zipWith
                    (\leftChild rightChild -> not $ Set.disjoint (rootSymbols leftChild) (rootSymbols rightChild))
                    leftChildren
                    rightChildren
                )
            && and (zipWith stateLanguagesOverlap leftChildren rightChildren)
      where
        leftChildren = transitionChildren left
        rightChildren = transitionChildren right

    rootSymbols state =
        Set.fromList
            [ (transitionSymbol transition, transitionRefinement transition)
            | transition <- transitions state
            ]

-- | Every unordered pair of distinct list elements.
distinctPairs :: [a] -> [(a, a)]
distinctPairs [] = []
distinctPairs (value : rest) = map (\other -> (value, other)) rest <> distinctPairs rest

-- | Decode one valid accepting-run rank into its concrete annotated term.
generatedAtWith ::
    (Symbol -> Refinement -> [a] -> a) ->
    EqualityAutomaton ->
    Map.Map State Integer ->
    Integer ->
    Generated a
generatedAtWith buildValue automaton counts rank =
    Generated
        1
        (decodeValue (automatonInitial automaton) rank)
        (decodeTerm (automatonInitial automaton) rank)
  where
    table = automatonTransitions automaton

    decodeValue state stateRank =
        case selectTransition stateRank $ Map.findWithDefault [] state table of
            Just (transition, transitionRank) ->
                buildValue
                    (transitionSymbol transition)
                    (transitionRefinement transition)
                    (decodeChildrenWith decodeValue transitionRank $ transitionChildren transition)
            Nothing -> error "generatedAt: rank outside the counted LTA"

    decodeTerm state stateRank =
        case selectTransition stateRank $ Map.findWithDefault [] state table of
            Just (transition, transitionRank) ->
                LiquidTerm
                    (transitionSymbol transition)
                    (transitionRefinement transition)
                    (decodeChildrenWith decodeTerm transitionRank $ transitionChildren transition)
            Nothing -> error "generatedAt: rank outside the counted LTA"

    selectTransition _ [] = Nothing
    selectTransition remaining (transition : rest)
        | remaining < count = Just (transition, remaining)
        | otherwise = selectTransition (remaining - count) rest
      where
        count = transitionCount transition

    transitionCount transition =
        product
            [ Map.findWithDefault 0 child counts
            | child <- transitionChildren transition
            ]

    decodeChildrenWith :: (State -> Integer -> b) -> Integer -> [State] -> [b]
    decodeChildrenWith _ _ [] = []
    decodeChildrenWith decode remaining (child : rest) =
        let suffixCount =
                product
                    [ Map.findWithDefault 0 state counts
                    | state <- rest
                    ]
            (childRank, restRank) = remaining `quotRem` suffixCount
         in decode child childRank : decodeChildrenWith decode restRank rest

{- | Cache exact refinement queries for one compilation run.

Applicative generator products repeat the same local liquid obligations across
many complete witnesses. The entailment boundary is deterministic for a fixed
solver environment, so one verdict can safely serve every identical request
during this compile without making the cache part of the public API.
-}
cacheEntailment :: Entailment -> IO Entailment
cacheEntailment (Entailment decide) = do
    verdicts <- newIORef Map.empty
    pure $ Entailment $ \antecedent consequent -> do
        cache <- readIORef verdicts
        let obligation = (antecedent, consequent)
        case Map.lookup obligation cache of
            Just verdict -> pure verdict
            Nothing -> do
                verdict <- decide antecedent consequent
                modifyIORef' verdicts $ Map.insert obligation verdict
                pure verdict

-- | Exact number of accepted, replayable outcomes.
cardinality :: Compiled a -> Integer
cardinality = Tree.cardinality . compiledRanked

-- | Select one accepted outcome by its stable zero-based rank.
select :: Integer -> Compiled a -> Either GeneratorError (Generated a)
select rank = first fromRankedError . flip Tree.unrank rank . compiledRanked

-- | Direct valid shrinks of one accepted rank.
shrinkRank :: Compiled a -> Integer -> [Integer]
shrinkRank compiled rank
    | rank < 0 || rank >= cardinality compiled = []
    | otherwise =
        nub $
            Map.findWithDefault [] rank (compiledShrinkRanks compiled)
                <> compiledPlanShrinks compiled rank

-- | All transitively smaller accepted members reachable from one rank.
smallerMembers :: Compiled a -> Integer -> [(Integer, Generated a)]
smallerMembers compiled rank =
    [ (candidate, generated)
    | candidate <- allShrinks compiled rank
    , Right generated <- [select candidate compiled]
    ]

data Outcome a = Outcome
    { outcomeWeight :: !Integer
    , outcomeValue :: a
    , outcomeWitness :: !Witness
    }

data Witness = Witness
    { witnessSymbol :: !Symbol
    , witnessRefinement :: !Refinement
    , witnessConstraint :: !LiquidConstraint
    , witnessChildren :: ![Witness]
    }

data ShrinkCandidate = ShrinkCandidate
    { shrinkCandidateIndex :: !Integer
    , shrinkCandidateCondition :: !ShrinkCondition
    }

data ShrinkCondition
    = AlwaysShrink
    | WeakenRefinement !Refinement !Refinement !Bool

liftShrink :: (Integer -> Integer) -> ShrinkCandidate -> ShrinkCandidate
liftShrink transform candidate =
    candidate{shrinkCandidateIndex = transform $ shrinkCandidateIndex candidate}

withOffsets :: [(Integer, LTAGen a)] -> [(Integer, Integer, LTAGen a, Integer)]
withOffsets = go 0
  where
    go _ [] = []
    go offset ((weight, generator) : rest) =
        let count = finiteCardinality $ generatorOutcomes generator
         in (offset, weight, generator, count) : go (offset + count) rest

shrinkChoice :: [(Integer, Integer, LTAGen a, Integer)] -> Integer -> [ShrinkCandidate]
shrinkChoice branches index = go [] branches
  where
    go _ [] = []
    go earlier (branch@(offset, _, generator, count) : rest)
        | index < offset + count =
            [ ShrinkCandidate earlierOffset AlwaysShrink
            | (earlierOffset, _, _, earlierCount) <- earlier
            , earlierCount > 0
            ]
                <> [ liftShrink (offset +) candidate
                   | candidate <- generatorShrinks generator (index - offset)
                   ]
        | otherwise = go (earlier <> [branch]) rest

type Accepted a = (Integer, Outcome a, Generated a)

acceptedGenerated :: Accepted a -> Generated a
acceptedGenerated (_, _, generated) = generated

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

{- | Check one generated witness directly against its own liquid guards.

The old path first expanded every witness into a singleton automaton, then
recognized the same tree through that automaton. Generated witnesses already
fix every transition and child, so the structural recognition work is
tautological; only child validity and guards can reject them.
-}
checkWitness :: Entailment -> Witness -> IO Verdict
checkWitness entailment witness = do
    childrenVerdict <- checkChildren (witnessChildren witness)
    case childrenVerdict of
        No -> pure No
        _ -> do
            constraintVerdict <- evaluateConstraint entailment (witnessConstraint witness) (witnessTerm witness)
            pure $ andVerdicts childrenVerdict constraintVerdict
  where
    checkChildren [] = pure Yes
    checkChildren (child : rest) = do
        childVerdict <- checkWitness entailment child
        case childVerdict of
            No -> pure No
            _ -> andVerdicts childVerdict <$> checkChildren rest

    andVerdicts No _ = No
    andVerdicts _ No = No
    andVerdicts Unknown _ = Unknown
    andVerdicts _ Unknown = Unknown
    andVerdicts Yes Yes = Yes

{- | Preserve singleton-automaton arity validation without constructing one.

All states allocated from a finite witness are present and acyclic, leaving
inconsistent reuse of one ranked symbol as the only possible structural error.
-}
validateWitness :: Witness -> Either GeneratorError ()
validateWitness rootWitness = go Map.empty [rootWitness]
  where
    go _ [] = Right ()
    go arities (witness : rest) =
        let symbol = witnessSymbol witness
            actual = length $ witnessChildren witness
         in case Map.lookup symbol arities of
                Nothing ->
                    go
                        (Map.insert symbol actual arities)
                        (witnessChildren witness <> rest)
                Just expected
                    | expected == actual -> go arities (witnessChildren witness <> rest)
                    | otherwise ->
                        Left . InvalidSupport $
                            InconsistentArity symbol expected actual

compileAccepted ::
    [Accepted a] ->
    Either GeneratorError (EqualityAutomaton, Tree.Ranked (Generated a))
compileAccepted accepted = do
    constrainedSupport <-
        compileWitnesses
            [ outcomeWitness outcome
            | (_, outcome, _) <- accepted
            ]
    ranked <-
        first fromRankedError $
            Tree.fromWeighted
                [ (generatedWeight generated, generated)
                | (_, _, generated) <- accepted
                ]
    pure (FTA.mapGuards constraintEqualities constrainedSupport, ranked)

fromRankedError :: Tree.RankedError -> GeneratorError
fromRankedError Tree.EmptyRanked = EmptyGenerator
fromRankedError (Tree.NonPositiveRankedWeight weight) = NonPositiveWeight weight
fromRankedError (Tree.NegativeRankedRank rank) = NegativeRank rank
fromRankedError (Tree.RankedSelectionOutOfRange rank total) =
    SelectionOutOfRange rank total

type ImplicationTable = [((Refinement, Refinement), Bool)]

requiredImplications :: LTAGen a -> [(Refinement, Refinement)]
requiredImplications generator =
    nub $
        concatMap
            conditionPairs
            [ shrinkCandidateCondition candidate
            | source <- finiteRanks $ generatorOutcomes generator
            , candidate <- generatorShrinks generator source
            ]
  where
    conditionPairs AlwaysShrink = []
    conditionPairs (WeakenRefinement source candidate _) =
        [(source, candidate), (candidate, source)]

evaluateImplications ::
    Entailment ->
    [(Refinement, Refinement)] ->
    IO (Either GeneratorError ImplicationTable)
evaluateImplications entailment = go []
  where
    go table [] = pure (Right $ reverse table)
    go table ((antecedent, consequent) : rest) = do
        verdict <- entails entailment antecedent consequent
        case verdict of
            Yes -> go (((antecedent, consequent), True) : table) rest
            No -> go (((antecedent, consequent), False) : table) rest
            Unknown -> pure (Left SolverUnknown)

conditionHolds :: ImplicationTable -> ShrinkCondition -> Bool
conditionHolds _ AlwaysShrink = True
conditionHolds table (WeakenRefinement source candidate equivalentEarlier) =
    implied source candidate
        && (not (implied candidate source) || equivalentEarlier)
  where
    implied antecedent consequent =
        lookup (antecedent, consequent) table == Just True

buildShrinkTable ::
    LTAGen a ->
    [Accepted a] ->
    ImplicationTable ->
    Map.Map Integer [Integer]
buildShrinkTable generator accepted implications =
    Map.fromList
        [ (acceptedRank, nearestAccepted (Set.singleton sourceIndex) candidates)
        | (acceptedRank, (sourceIndex, _, _)) <- zip [0 ..] accepted
        , let candidates = generatorShrinks generator sourceIndex
        ]
  where
    acceptedRanks =
        Map.fromList
            [ (sourceIndex, toInteger acceptedRank)
            | (acceptedRank, (sourceIndex, _, _)) <- zip [0 :: Int ..] accepted
            ]

    nearestAccepted visited candidates =
        orderedNub $ direct <> indirect
      where
        eligible =
            [ candidate
            | candidate <- candidates
            , let target = shrinkCandidateIndex candidate
            , Set.notMember target visited
            , conditionHolds implications (shrinkCandidateCondition candidate)
            ]
        direct =
            [ acceptedRank
            | candidate <- eligible
            , Just acceptedRank <- [Map.lookup (shrinkCandidateIndex candidate) acceptedRanks]
            ]
        indirect =
            concat
                [ nearestAccepted
                    (Set.insert target visited)
                    (generatorShrinks generator target)
                | candidate <- eligible
                , let target = shrinkCandidateIndex candidate
                , Map.notMember target acceptedRanks
                ]

orderedNub :: [Integer] -> [Integer]
orderedNub = go Set.empty
  where
    go _ [] = []
    go seen (value : rest)
        | Set.member value seen = go seen rest
        | otherwise = value : go (Set.insert value seen) rest

allShrinks :: Compiled a -> Integer -> [Integer]
allShrinks compiled start = go Set.empty (shrinkRank compiled start)
  where
    go _ [] = []
    go visited (rank : rest)
        | Set.member rank visited = go visited rest
        | otherwise =
            rank
                : go
                    (Set.insert rank visited)
                    (shrinkRank compiled rank <> rest)

compileWitnesses :: [Witness] -> Either GeneratorError Automaton
compileWitnesses [] = Left EmptyGenerator
compileWitnesses witnesses =
    first InvalidSupport . mkAutomaton root . Map.toList . buildRows $
        foldl (flip $ addWitnessAt root) initialBuild witnesses
  where
    root = State 0
    initialBuild = Build 1 (Map.singleton root [])

data Build = Build
    { buildNextState :: !Int
    , buildRows :: !(Map.Map State [Transition])
    }

addWitnessAt :: State -> Witness -> Build -> Build
addWitnessAt state witness build =
    let (childStates, withChildren) = addChildren (witnessChildren witness) build
        transition =
            Transition
                (witnessSymbol witness)
                (witnessRefinement witness)
                childStates
                (witnessConstraint witness)
     in withChildren
            { buildRows =
                Map.insertWith
                    (flip (<>))
                    state
                    [transition]
                    (buildRows withChildren)
            }

addChildren :: [Witness] -> Build -> ([State], Build)
addChildren [] build = ([], build)
addChildren (witness : rest) build =
    let child = State (buildNextState build)
        allocated =
            build
                { buildNextState = buildNextState build + 1
                , buildRows = Map.insert child [] (buildRows build)
                }
        withChild = addWitnessAt child witness allocated
        (childStates, finished) = addChildren rest withChild
     in (child : childStates, finished)

witnessTerm :: Witness -> LiquidTerm
witnessTerm Witness{witnessSymbol, witnessRefinement, witnessChildren} =
    LiquidTerm
        witnessSymbol
        witnessRefinement
        (map witnessTerm witnessChildren)
