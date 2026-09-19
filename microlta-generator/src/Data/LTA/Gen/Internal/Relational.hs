{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}

{- | Group a recipe by the observations its guards need.

Each child language is grouped by the finite observations that its parent
guard reads. The solver decides one tuple of groups at a time, and the
accepted tuples are lowered to native ECTA joins. This keeps the plan compact,
because no complete candidate is built to decide a guard.
-}
module Data.LTA.Gen.Internal.Relational (
    ObservationKey,
    RelationalValue,
    RecipeGroups,
    acceptedAlphabet,
    acceptedSources,
    ensureConsistentArities,
    compileRecipe,
    compileRelational,
) where

import Data.Bifunctor (bimap, first)
import qualified Data.IntMap.Strict as IntMap
import Data.List (mapAccumL, nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.CFTA.Equality.Constraints (EqConstraints (EmptyConstraints))
import Data.CFTA.Refinement
import Data.ECTA.Gen.Internal.Symbolic (symbolicGroupsWith)
import qualified Data.ECTA.Gen.QuickCheck as ECTA
import Data.LTA.Gen.Internal.AutomatonCompile (constraintTerms, countAutomaton, ensureUnconstrained, symbolicGraph)
import qualified Data.LTA.Gen.Internal.AutomatonSource as AutomatonSource
import Data.LTA.Gen.Internal.Error (GeneratorError (..), fromRankedError)
import Data.LTA.Gen.Internal.IndexedGroup (indexedGroup)
import Data.LTA.Gen.Internal.Recipe (
    childRecipeArity,
    knownEmptyChild,
    knownEmptyRecipe,
    rawRecipeCount,
    uniformlyWeightedRecipe,
 )
import Data.LTA.Gen.Internal.Replay (cardinality, unrank)
import qualified Data.LTA.Gen.Internal.SourceIndex as Source
import Data.LTA.Gen.Internal.Surface (prepareGenerator)
import Data.LTA.Gen.Internal.Types
import Data.LTA.Gen.Internal.Witness (Witness (..), cacheEntailment, termWitness, witnessTerm)
import qualified Data.Ranked as Tree

-- | Sparse observations and leaf flags that identify one relational group.
newtype ObservationKey = ObservationKey
    { unObservationKey :: Map.Map Path (RootObservation, Bool)
    }
    deriving (Eq, Ord, Show)

-- | A domain value paired lazily with the witness selected at the same rank.
data RelationalValue a = RelationalValue a Witness

-- | One applicative result and its ordered child witnesses.
data RelationalForest a = RelationalForest a [Witness]

-- | Accepted alphabet and source occurrences for one observation group.
data GroupInfo = GroupInfo
    { groupAlphabet :: !(Map.Map Symbol (Set.Set Int))
    , groupSources :: !Source.SourceIndex
    }

-- | Raw source count and the groups that survive their constraints.
data RecipeGroups = RecipeGroups
    { rawSourceCount :: !Integer
    , acceptedGroups :: !(Map.Map ObservationKey GroupInfo)
    }

-- | Combine disjoint source occurrences with the same observed key.
mergeGroupInfo :: GroupInfo -> GroupInfo -> GroupInfo
mergeGroupInfo left right =
    GroupInfo
        (Map.unionWith Set.union (groupAlphabet left) (groupAlphabet right))
        (Source.union (groupSources left) (groupSources right))

-- | Collect the alphabet of accepted groups without observing their values.
acceptedAlphabet :: RecipeGroups -> Map.Map Symbol (Set.Set Int)
acceptedAlphabet = Map.unionsWith Set.union . map groupAlphabet . Map.elems . acceptedGroups

-- | Look up metadata for a key produced by the corresponding grouped plan.
groupAt :: ObservationKey -> RecipeGroups -> GroupInfo
groupAt key groups =
    case Map.lookup key $ acceptedGroups groups of
        Just info -> info
        Nothing -> error "microlta-generator bug in Data.LTA.Gen.Internal.Relational: missing source group"

-- | Retain all accepted source occurrences in their original order.
acceptedSources :: RecipeGroups -> Source.SourceIndex
acceptedSources groups =
    foldr
        (Source.union . groupSources)
        (Source.empty $ rawSourceCount groups)
        (Map.elems $ acceptedGroups groups)

-- | Reject inconsistent symbol arities without decoding group members.
ensureConsistentArities :: Map.Map Symbol (Set.Set Int) -> Either GeneratorError ()
ensureConsistentArities arities =
    case [(symbol, expected, actual) | (symbol, sizes) <- Map.toAscList arities, expected : actual : _ <- [Set.toAscList sizes]] of
        (symbol, expected, actual) : _ -> Left $ InvalidSupport $ InconsistentArity symbol expected actual
        [] -> Right ()

-- | Compile one retained recipe, grouped by the observations its parent needs.
compileRecipe ::
    Entailment ->
    [Path] ->
    Recipe a ->
    IO (Either GeneratorError (ECTA.Grouped ObservationKey (RelationalValue a), RecipeGroups))
compileRecipe _ _ recipe
    | knownEmptyRecipe recipe = pure $ Right (ECTA.frequencies [], RecipeGroups (rawRecipeCount recipe) Map.empty)
compileRecipe _ requested (PoolRecipe entries) =
    pure . Right $
        ( ECTA.frequencies
            [ ( 1
              , ECTA.keyed
                    (leafObservationKey requested symbol refinement)
                    (ECTA.elements [RelationalValue value $ Witness symbol refinement unconstrainedConstraint []])
              )
            | Refined value symbol refinement <- entries
            ]
        , RecipeGroups total $
            Map.fromListWith
                mergeGroupInfo
                [ ( leafObservationKey requested symbol refinement
                  , GroupInfo
                        (Map.singleton symbol $ Set.singleton 0)
                        (Source.singleton total sourceRank 1)
                  )
                | (sourceRank, Refined _ symbol refinement) <- zip [0 ..] entries
                ]
        )
  where
    total = toInteger $ length entries
compileRecipe entailment requested (MapRecipe transform recipe) =
    fmap (fmap $ first $ ECTA.mapWithKey mapValue) $
        compileRecipe entailment requested recipe
  where
    mapValue _ (RelationalValue value witness) =
        RelationalValue (transform value) witness
compileRecipe entailment requested (ChoiceRecipe alternatives) = do
    compiled <-
        traverse
            ( \(weight, recipe) ->
                fmap (fmap (weight,)) $
                    compileRecipe entailment requested recipe
            )
            alternatives
    pure $ merge <$> sequence compiled
  where
    liveGroup (_, (grouped, _)) = ECTA.sizes grouped /= Left ECTA.EmptyGenerator
    merge branches =
        let (total, indexed) = mapAccumL locate 0 branches
            locate offset (weight, (_, groups)) =
                (offset + rawSourceCount groups, (offset, weight, groups))
            adjust offset weight info =
                info
                    { groupSources =
                        Source.withDomain total
                            $ Source.shift offset
                            $ Source.scale weight
                            $ groupSources info
                    }
         in ( ECTA.frequencies [(weight, grouped) | (weight, (grouped, _)) <- filter liveGroup branches]
            , RecipeGroups total $
                Map.unionsWith
                    mergeGroupInfo
                    [ Map.map (adjust offset weight) $ acceptedGroups groups
                    | (offset, weight, groups) <- indexed
                    ]
            )
compileRecipe _ _ (AutomatonRecipe _ _) = pure $ Left SourceRequiresCompilation
compileRecipe _ requested (CompiledRecipe compiled) =
    pure $ compileSourceGroups requested compiled
compileRecipe _ _ (NodeRecipe symbol (ComputedRefinement _) _ _) =
    pure $ Left $ RelationalComputedRefinement symbol
compileRecipe entailment requested (NodeRecipe symbol nodeRefinement constraint childRecipe) = do
    let arity = childRecipeArity childRecipe
        needsChildRoots = case nodeRefinement of
            RootComputedRefinement _ -> True
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
        Right (childGroups, childArities) -> do
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
                    ( \retained ->
                        ( ECTA.regroupBy closeKey $ ECTA.mapWithKey closeValue retained
                        , RecipeGroups (product $ map rawSourceCount childArities) $
                            Map.fromListWith
                                mergeGroupInfo
                                [ ( closeKey childKeys
                                  , let infos = zipWith groupAt childKeys childArities
                                     in GroupInfo
                                            ( Map.insertWith Set.union symbol (Set.singleton arity)
                                                $ Map.unionsWith Set.union
                                                $ map groupAlphabet infos
                                            )
                                            (foldr (Source.product . groupSources) (Source.full 1) infos)
                                  )
                                | childKeys <- either (const []) Map.keys $ ECTA.sizes retained
                                ]
                        )
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

-- | Observe an imported term set through its graph whenever possible.
compileSourceGroups ::
    [Path] ->
    Compiled a ->
    Either GeneratorError (ECTA.Grouped ObservationKey (RelationalValue a), RecipeGroups)
compileSourceGroups requested compiled = do
    groups <- case compiledSupport compiled of
        EqualitySupport automaton | Right () <- ensureUnconstrained automaton -> do
            counts <- countAutomaton automaton
            pure $
                Map.fromList
                    [ ( ObservationKey $ Map.map toObservation observations
                      , GroupInfo alphabet sources
                      )
                    | (observations, (alphabet, sources)) <- Map.toList $ AutomatonSource.groupAutomaton requested automaton counts
                    ]
        SymbolicSupport automaton -> do
            (root, labels) <- symbolicGraph automaton
            let interpret constraint = case constraintTerms constraint of
                    Right terms -> terms
                    Left _ -> error "compileSourceGroups: unsupported guard in a compiled symbolic source"
                alphabet =
                    Map.fromListWith
                        Set.union
                        [ (transitionSymbol transition, Set.singleton $ length $ transitionChildren transition)
                        | transitions <- Map.elems $ automatonTransitions automaton
                        , transition <- transitions
                        ]
            pure $
                Map.fromList
                    [ ( ObservationKey $ Map.map (\(identifier, isLeaf) -> toObservation (labels IntMap.! identifier, isLeaf)) observations
                      , GroupInfo alphabet $ Source.fromPrefix total count prefixAt
                      )
                    | (observations, (count, prefixAt)) <- Map.toList $ symbolicGroupsWith interpret requested root
                    ]
        _ -> Left RelationalPlanUnavailable
    pure
        ( ECTA.frequencies
            [ (1, ECTA.keyed key $ indexedGroup (Source.cardinality sources) $ memberAt sources)
            | (key, info) <- Map.toList groups
            , let sources = groupSources info
            ]
        , RecipeGroups total groups
        )
  where
    total = cardinality compiled
    toObservation (LiquidSymbol symbol refinement, isLeaf) = (RootObservation symbol refinement, isLeaf)
    memberAt sources index =
        case Source.select sources index >>= either (const Nothing) Just . (unrank compiled) of
            Just member -> RelationalValue (generatedValue member) $ termWitness $ generatedTerm member
            Nothing -> error "microlta-generator bug in Data.LTA.Gen.Internal.Relational: invalid imported group rank"

-- | Result refinement known for one tuple of direct child groups.
refinementForChildren :: NodeRefinement a -> [ObservationKey] -> Refinement
refinementForChildren (FixedRefinement refinement) _ = refinement
refinementForChildren (RootComputedRefinement project) childKeys =
    project $ map observationKeyRoot childKeys
refinementForChildren (ComputedRefinement _) _ =
    error
        "microlta-generator bug in Data.LTA.Gen.Internal.Relational.refinementForChildren: a value-computed refinement reached relational compilation"

-- | Root observation retained by every relational group.
observationKeyRoot :: ObservationKey -> RootObservation
observationKeyRoot (ObservationKey observations) =
    case Map.lookup (path []) observations of
        Just (rootObservation, _) -> rootObservation
        Nothing ->
            error
                "microlta-generator bug in Data.LTA.Gen.Internal.Relational.compileRelational: child group has no root observation"

-- | Root refinement retained by every relational group.
observationKeyRefinement :: ObservationKey -> Refinement
observationKeyRefinement = observedRefinement . observationKeyRoot

-- | Preserve the raw dimensions of child sources skipped in an empty product.
emptyChildGroups :: ChildRecipe a -> [RecipeGroups]
emptyChildGroups (PureChildRecipe _) = []
emptyChildGroups (OneChildRecipe recipe) = [RecipeGroups (rawRecipeCount recipe) Map.empty]
emptyChildGroups (ApplyChildRecipe functions arguments) = emptyChildGroups functions <> emptyChildGroups arguments

-- | Compile a heterogeneous child spine while retaining its observation tuple.
compileChildRecipe ::
    Entailment ->
    [[Path]] ->
    ChildRecipe a ->
    IO (Either GeneratorError (ECTA.Grouped [ObservationKey] (RelationalForest a), [RecipeGroups]))
compileChildRecipe _ _ recipe
    | knownEmptyChild recipe = pure $ Right (ECTA.frequencies [], emptyChildGroups recipe)
compileChildRecipe _ _ (PureChildRecipe value) =
    pure . Right $
        (ECTA.keyed [] $ ECTA.elements [RelationalForest value []], [])
compileChildRecipe entailment requirements (OneChildRecipe recipe) = do
    compiled <- compileRecipe entailment (firstRequirements requirements) recipe
    pure $
        fmap
            ( bimap
                ( ECTA.regroupBy pure
                    . ECTA.mapWithKey
                        (\_ (RelationalValue value witness) -> RelationalForest value [witness])
                )
                pure
            )
            compiled
  where
    firstRequirements (requirementsAtChild : _) = requirementsAtChild
    firstRequirements [] = []
compileChildRecipe entailment requirements (ApplyChildRecipe (PureChildRecipe function) arguments) = do
    compiled <- compileChildRecipe entailment requirements arguments
    pure $
        fmap
            ( first $ ECTA.mapWithKey $ \_ (RelationalForest argument witnesses) ->
                RelationalForest (function argument) witnesses
            )
            compiled
compileChildRecipe entailment requirements (ApplyChildRecipe functions arguments) = do
    let functionArity = childRecipeArity functions
        (functionRequirements, argumentRequirements) = splitAt functionArity requirements
    compiledFunctions <- compileChildRecipe entailment functionRequirements functions
    case compiledFunctions of
        Left err -> pure $ Left err
        Right (functionGroups, functionArities)
            | ECTA.sizes functionGroups == Left ECTA.EmptyGenerator ->
                pure $ Right (ECTA.frequencies [], functionArities <> emptyChildGroups arguments)
            | otherwise -> do
                compiledArguments <- compileChildRecipe entailment argumentRequirements arguments
                case compiledArguments of
                    Left err -> pure $ Left err
                    Right (argumentGroups, argumentArities) -> do
                        related <-
                            ECTA.relateGroupsM
                                (\_ _ -> pure $ Right True)
                                (<>)
                                functionGroups
                                argumentGroups
                        pure $
                            fmap
                                ( \joined ->
                                    ( ECTA.mapWithKey
                                        ( \_ (RelationalForest function functionWitnesses, RelationalForest argument argumentWitnesses) ->
                                            RelationalForest
                                                (function argument)
                                                (functionWitnesses <> argumentWitnesses)
                                        )
                                        joined
                                    , functionArities <> argumentArities
                                    )
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
constraintDecision entailment symbol refinement constraint childKeys = do
    verdict <-
        evaluateGuardWithShape
            entailment
            ( \target -> do
                (RootObservation observedSymbol observedRefinement, _) <- Map.lookup target observations
                pure (observedSymbol, observedRefinement)
            )
            (\target -> snd <$> Map.lookup target observations)
            (constraintAsGuard constraint)
    pure $ case verdict of
        Yes -> Right True
        No -> Right False
        Unknown
            | constraintEqualities constraint /= EmptyConstraints ->
                Left $ RelationalEqualityUnsupported $ constraintEqualities constraint
            | containsSyntacticEquality (constraintGuard constraint) ->
                Left $ RelationalSyntacticEqualityUnsupported $ constraintGuard constraint
            | otherwise -> Left SolverUnknown
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
    ObservationKey
        $ Map.restrictKeys observations
        $ Set.insert (path [])
        $ Set.fromList requested
  where
    ObservationKey observations = completeObservationKey symbol refinement childKeys

-- | Root plus the sparse observations retained by every direct child group.
completeObservationKey ::
    Symbol ->
    Refinement ->
    [ObservationKey] ->
    ObservationKey
completeObservationKey symbol refinement childKeys =
    ObservationKey
        $ Map.fromList
        $ (path [], (RootObservation symbol refinement, null childKeys))
            : [ (path $ childIndex : unPath target, observed)
              | (childIndex, ObservationKey childObservations) <- zip [0 ..] childKeys
              , (target, observed) <- Map.toList childObservations
              ]

-- | Available observations for one nullary source.
leafObservationKey :: [Path] -> Symbol -> Refinement -> ObservationKey
leafObservationKey requested symbol refinement =
    ObservationKey $
        if path [] `elem` requested
            then Map.singleton (path []) (RootObservation symbol refinement, True)
            else Map.empty

-- | Decode a valid ECTA rank into the public generated-member view.
relationalGeneratedAt :: ECTA.ECTAGen (RelationalValue a) -> Integer -> Generated a
relationalGeneratedAt generator rank =
    case ECTA.unrank generator rank of
        Left err ->
            error $
                "microlta-generator bug in Data.LTA.Gen.Internal.Relational.compileRelational: invalid retained rank: " <> show err
        Right (RelationalValue value witness) ->
            Generated 1 value (witnessTerm witness)

{- | Compile a compositional LTA generator as solver-approved ECTA joins.

This explicit path uses native grouped ranks and structural shrinking. It
retains qualified-do child structure, groups each child language by
the finite observations used by its parent guard, asks the solver once per live
observation tuple, and lowers accepted tuples through
'ECTA.relateGroupsM'. Fixed result refinements are known at that boundary;
'refinedNodeBy' remains on the general witness compiler because an arbitrary
Haskell projection may vary inside one relational group.
-}
compileRelational :: Entailment -> LTAGen a -> IO (Either GeneratorError (Compiled a))
compileRelational uncachedEntailment generator = do
    entailment <- cacheEntailment uncachedEntailment
    prepared <- prepareGenerator entailment generator
    case prepared >>= generatorRecipe of
        Left err -> pure $ Left err
        Right recipe
            | not $ uniformlyWeightedRecipe recipe -> pure $ Left RelationalPlanUnavailable
            | otherwise -> do
                compiled <- compileRecipe entailment [path []] recipe
                pure $ do
                    (grouped, groups) <- compiled
                    let flattened = ECTA.ungroup grouped
                    total <- first InvalidECTAGenerator $ ECTA.cardinality flattened
                    ensureConsistentArities $ acceptedAlphabet groups
                    ectaSupport <- first InvalidECTAGenerator $ ECTA.support flattened
                    ranked <- first fromRankedError $ Tree.fromIndexedOnDemand $ Tree.Indexed total (relationalGeneratedAt flattened)
                    pure $ Compiled (RelationalSupport ectaSupport) ranked (ECTA.shrinkRank flattened)
