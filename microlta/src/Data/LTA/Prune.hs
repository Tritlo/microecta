{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}

{- | Semantic pruning, ECTA lowering, and the complete reduction phase.

Pruning discharges a transition guard by splitting the states below it until
every observed position is homogeneous in what the guard reads. Combinations
that fail, and the states they strand, are removed to a fixed point.
-}
module Data.LTA.Prune (
    PruneError (..),
    prune,
    pruneToECTA,
    lowerToEqualityAutomaton,
    ReductionError (..),
    reduce,
) where

import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Strict (StateT, get, modify', runStateT)
import Data.Bifunctor (first)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe)
import qualified Data.Set as Set

import qualified Data.CFTA as FTA
import Data.CFTA.Path (statesAt)
import Data.ECTA.Paths (
    EqConstraints (EmptyConstraints),
    Path,
    combineEqConstraints,
    constraintsAreContradictory,
    mkEqConstraints,
    unPath,
 )

import Data.LTA.Automaton (
    Automaton,
    AutomatonError,
    EqualityAutomaton,
    Transition,
    atIndex,
    automatonInitial,
    automatonTransitions,
    fromFTAError,
    mkAutomaton,
    replaceTransitionChildren,
    reserveState,
    transitionChildren,
    transitionConstraint,
    transitionEqualities,
    transitionLiquidSymbol,
    transitionRefinement,
    transitionSymbol,
    unusedStates,
    pattern Transition,
 )
import Data.LTA.Constraint (
    Guard (..),
    LiquidConstraint (..),
    combineConstraints,
    equalityPathPairs,
    guardPaths,
    splitGuard,
    symbolSensitivePaths,
 )
import Data.LTA.Evaluate (evaluateGuardWithShape, substitutionValues)
import Data.LTA.Minimize (
    MinimizeError,
    SimilarityError,
    Subtyping,
    minimize,
    similarity,
 )
import Data.LTA.Types (LiquidSymbol (LiquidSymbol), Refinement, State)
import Data.LTA.Verdict (Entailment, Verdict (..))

-- | A semantic obstacle encountered while pruning guarded transitions.
data PruneError
    = -- | The solver could not decide a transition guard.
      PruneUnknown !State
    | -- | Product construction violated an FTA invariant.
      InvalidSyntacticIntersection
    | -- | ECTA lowering was requested while a non-equality LTA guard remained.
      ResidualLTAConstraint !State !Guard
    | -- | Pruning exposed an invalid automaton structure.
      InvalidPrunedAutomaton !AutomatonError
    deriving (Eq, Show)

{- | Remove semantically impossible transitions and lower the result to ECTA.

This is the transition-level boundary used by generated LTAs. A guard is
discharged by partitioning the transition sets at every finite position it
observes. A partition is homogeneous in the refinement needed by ordinary
entailment, or in both symbol and refinement where substitution names a value.
Successful combinations become specialized states; failed combinations and
newly dead states are removed to a fixed point. The returned automaton retains
only normalized ECTA equality classes. This is the paper's semantic-intersection
rule, expressed as explicit state splitting without materializing an accepted
tree.

For a required syntactic equality, the paper's ordinary FTA product intersection
narrows the first position to terms also admitted at the second. The equality
class remains on the returned ECTA: intersection can discard disjoint
sub-languages, but equality between two independently chosen arbitrary subtrees
is not in general a regular tree language.
-}
pruneToECTA :: Entailment -> Automaton -> IO (Either PruneError EqualityAutomaton)
pruneToECTA entailment automaton = do
    reduced <- prune entailment automaton
    pure $ reduced >>= lowerToEqualityAutomaton

{- | Lower a reduced LTA to ECTA when every residual guard is positive equality.

This is an optimization, not LTA semantics. It succeeds for 'Top', 'Same', and
conjunctions of those atoms, combining them with any already-normalized
'EqConstraints'. Negated, disjunctive, or semantic guards remain LTAs and cause
an explicit failure.
-}
lowerToEqualityAutomaton :: Automaton -> Either PruneError EqualityAutomaton
lowerToEqualityAutomaton automaton = do
    rows <- traverse lowerRow $ Map.toList $ automatonTransitions automaton
    case FTA.mkFTA (automatonInitial automaton) rows of
        Left err -> Left $ InvalidPrunedAutomaton $ fromFTAError err
        Right lowered -> Right lowered
  where
    lowerRow (state, transitions) =
        fmap (state,) $ traverse (lowerTransition state) transitions

    lowerTransition state transition@(FTA.Transition symbol children _) = do
        equalities <- constraintEqualitiesOnly automaton state transition
        pure $ FTA.Transition symbol children equalities

-- | Extract positive equality only when its paths exist before normalization.
constraintEqualitiesOnly :: Automaton -> State -> Transition -> Either PruneError EqConstraints
constraintEqualitiesOnly automaton state transition =
    combineEqConstraints constraintEqualities <$> guardEqualities constraintGuard
  where
    LiquidConstraint{constraintEqualities, constraintGuard} = transitionConstraint transition
    guardEqualities Top = Right EmptyConstraints
    guardEqualities (Same left right)
        | exists left && exists right = Right $ mkEqConstraints [[left, right]]
    guardEqualities (And guards) = foldr combine (Right EmptyConstraints) guards
    guardEqualities residual = Left $ ResidualLTAConstraint state residual

    combine guard rest = combineEqConstraints <$> guardEqualities guard <*> rest

    exists target = case unPath target of
        [] -> True
        index : rest -> case atIndex index $ transitionChildren transition of
            Nothing -> False
            Just child -> descend rest $ Set.singleton child

    descend [] _ = True
    descend (index : rest) states =
        case traverse (atIndex index . transitionChildren) outgoing of
            Nothing -> False
            Just children -> descend rest $ Set.fromList children
      where
        outgoing = concatMap (\child -> Map.findWithDefault [] child $ automatonTransitions automaton) $ Set.toList states

-- | Apply the paper's pruning rules and retain the resulting LTA.
prune :: Entailment -> Automaton -> IO (Either PruneError Automaton)
prune = pruneConstrained

-- | Internal fixed-point pruning while both constraint fields are available.
pruneConstrained :: Entailment -> Automaton -> IO (Either PruneError Automaton)
pruneConstrained entailment automaton = do
    syntactic <- pruneSyntacticEqualities automaton
    case syntactic of
        Left err -> pure $ Left err
        Right narrowed -> loop $ automatonTransitions narrowed
  where
    initial = automatonInitial automaton

    loop table = do
        (checked, split) <-
            runStateT
                (traverseRows table $ Map.toList table)
                (emptySplitBuild table)
        case checked of
            Left err -> pure $ Left err
            Right rows -> do
                let withSplits = Map.union (Map.fromList rows) (splitRows split)
                    next = FTA.trimTable initial withSplits
                if next == table
                    then
                        pure
                            $ first InvalidPrunedAutomaton
                            $ mkAutomaton initial (Map.toList next)
                    else loop next

    traverseRows _ [] = pure $ Right []
    traverseRows table ((state, transitions) : rest) = do
        row <- pruneRow table state transitions
        case row of
            Left err -> pure $ Left err
            Right retained ->
                fmap ((state, retained) :) <$> traverseRows table rest

    pruneRow _ _ [] = pure $ Right []
    pruneRow table state (transition : rest)
        | any (null . transitionsFromTable table) $ transitionChildren transition =
            pruneRow table state rest
        | otherwise = do
            decision <- pruneTransition entailment table state transition
            case decision of
                Left err -> pure $ Left err
                Right retained ->
                    fmap (retained <>) <$> pruneRow table state rest

    transitionsFromTable table state = Map.findWithDefault [] state table

-- | Apply the paper's P-Syn-Eq narrowing once before semantic pruning.
pruneSyntacticEqualities :: Automaton -> IO (Either PruneError Automaton)
pruneSyntacticEqualities automaton = do
    (checked, build) <-
        runStateT
            (traverseRows $ Map.toList original)
            (emptySplitBuild original)
    pure $ do
        rows <- checked
        first InvalidPrunedAutomaton $
            mkAutomaton
                (automatonInitial automaton)
                (Map.toList $ Map.union (Map.fromList rows) (splitRows build))
  where
    original = automatonTransitions automaton

    traverseRows [] = pure $ Right []
    traverseRows ((state, transitions) : rest) = do
        row <- traverseTransitions transitions
        case row of
            Left err -> pure $ Left err
            Right narrowed ->
                fmap ((state, narrowed) :) <$> traverseRows rest

    traverseTransitions [] = pure $ Right []
    traverseTransitions (transition : rest) = do
        if constraintsAreContradictory $ transitionEqualities transition
            then traverseTransitions rest
            else do
                narrowed <- applyEqualities [transition] $ requiredConstraintEqualities $ transitionConstraint transition
                case narrowed of
                    Left err -> pure $ Left err
                    Right retained ->
                        fmap (retained <>) <$> traverseTransitions rest

    applyEqualities transitions [] = pure $ Right transitions
    applyEqualities transitions ((left, right) : rest)
        | left == right = applyEqualities transitions rest
        | otherwise = do
            narrowed <- traverse (pruneEquality original left right) transitions
            case sequence narrowed of
                Left err -> pure $ Left err
                Right retained -> applyEqualities (concat retained) rest

-- | Positive syntactic equalities eligible for the paper's P-Syn-Eq rule.
requiredConstraintEqualities :: LiquidConstraint -> [(Path, Path)]
requiredConstraintEqualities LiquidConstraint{constraintEqualities, constraintGuard} =
    fromMaybe [] (equalityPathPairs constraintEqualities) <> positiveEqualities constraintGuard
  where
    positiveEqualities Top = []
    positiveEqualities (Same left right) = [(left, right)]
    positiveEqualities (And guards) = concatMap positiveEqualities guards
    positiveEqualities _ = []

-- | Narrow one transition at the left side of a required equality.
pruneEquality ::
    Map.Map State [Transition] ->
    Path ->
    Path ->
    Transition ->
    StateT SplitBuild IO (Either PruneError [Transition])
pruneEquality original left right transition = do
    current <- effectiveTable original
    rightStates <- statesAtTransitionPath current transition right
    if Set.null rightStates
        then pure $ Right []
        else case unPath left of
            [] -> intersectRoot rightStates
            leftPath -> intersectBelow current leftPath rightStates
  where
    intersectRoot rightStates = do
        leftState <- allocateRow [transition]
        narrowed <- intersectWithStates original leftState rightStates
        case narrowed of
            Left err -> pure $ Left err
            Right state -> do
                table <- effectiveTable original
                pure $ Right $ Map.findWithDefault [] state table

    intersectBelow current leftPath rightStates =
        case Set.fromList $ statesAt (\state -> Map.findWithDefault [] state current) transition left of
            leftStates
                | Set.null leftStates -> pure $ Right []
                | otherwise -> do
                    replacements <- traverse replacement $ Set.toAscList leftStates
                    case sequence replacements of
                        Left err -> pure $ Left err
                        Right pairs -> do
                            rewritten <- rewriteTransitionPath original leftPath (Map.fromList pairs) transition
                            pure $ Right $ maybe [] pure rewritten
      where
        replacement leftState = do
            narrowed <- intersectWithStates original leftState rightStates
            pure $ fmap (leftState,) narrowed

-- | Intersect one state with the union of the supplied right-hand states.
intersectWithStates ::
    Map.Map State [Transition] ->
    State ->
    Set.Set State ->
    StateT SplitBuild IO (Either PruneError State)
intersectWithStates original leftState rightStates = do
    intersections <- traverse (intersectStatePair original leftState) $ Set.toAscList rightStates
    case sequence intersections of
        Left err -> pure $ Left err
        Right states -> Right <$> unionStates original states

-- | Construct and install a structural product rooted at two LTA states.
intersectStatePair ::
    Map.Map State [Transition] ->
    State ->
    State ->
    StateT SplitBuild IO (Either PruneError State)
intersectStatePair original leftState rightState = do
    table <- effectiveTable original
    case (FTA.mkFTA leftState $ Map.toList table, FTA.mkFTA rightState $ Map.toList table) of
        (Right left, Right right) ->
            case FTA.intersectWith matchSymbol combineConstraints left right of
                Left _ -> pure $ Left InvalidSyntacticIntersection
                Right productAutomaton -> Right <$> installProduct productAutomaton
        _ -> pure $ Left InvalidSyntacticIntersection
  where
    matchSymbol left right
        | left == right = Just left
        | otherwise = Nothing

-- | Install reachable product rows, reusing any pair already constructed.
installProduct ::
    FTA.FTA (FTA.ProductState State State) LiquidSymbol LiquidConstraint ->
    StateT SplitBuild IO State
installProduct productAutomaton = do
    build <- get
    let productStates = FTA.states productAutomaton
        missing = filter (`Map.notMember` splitProducts build) productStates
    fresh <- traverse (const allocateState) missing
    let allocated = Map.fromList $ zip missing fresh
        products = Map.union (splitProducts build) allocated
        installed =
            Map.fromList
                [ (stateFor productState products, map (mapTransition products) $ FTA.transitionsFrom productAutomaton productState)
                | productState <- missing
                ]
    modify' $ \updated ->
        updated
            { splitRows = Map.union installed $ splitRows updated
            , splitProducts = products
            }
    pure $ stateFor (FTA.initialState productAutomaton) products
  where
    stateFor productState products = products Map.! productState

    mapTransition products (FTA.Transition symbol children guard) =
        FTA.Transition symbol (map (`stateFor` products) children) guard

-- | Form a union state without copying descendants.
unionStates :: Map.Map State [Transition] -> [State] -> StateT SplitBuild IO State
unionStates original states =
    case Set.toAscList $ Set.fromList states of
        [state] -> pure state
        unique -> do
            table <- effectiveTable original
            allocateRow $ concatMap (\state -> Map.findWithDefault [] state table) unique

-- | Allocate one fresh state with the supplied outgoing row.
allocateRow :: [Transition] -> StateT SplitBuild IO State
allocateRow transitions = do
    state <- allocateState
    modify' $ \updated ->
        updated
            { splitRows = Map.insert state transitions $ splitRows updated
            }
    pure state

-- | Reserve a state that differs from all original and allocated states.
allocateState :: StateT SplitBuild IO State
allocateState = do
    build <- get
    let (state, remaining) = reserveState $ splitFreshStates build
    modify' $ \updated -> updated{splitFreshStates = remaining}
    pure state

-- | Include all rows allocated earlier in this syntactic pruning phase.
effectiveTable :: Map.Map State [Transition] -> StateT SplitBuild IO (Map.Map State [Transition])
effectiveTable original = do
    build <- get
    pure $ Map.union (splitRows build) original

-- | States reached at one path under a particular transition.
statesAtTransitionPath ::
    Map.Map State [Transition] ->
    Transition ->
    Path ->
    StateT SplitBuild IO (Set.Set State)
statesAtTransitionPath table transition target
    | null (unPath target) = Set.singleton <$> allocateRow [transition]
    | otherwise = pure $ Set.fromList $ statesAt (\state -> Map.findWithDefault [] state table) transition target

-- | Clone the context above a path and replace each endpoint state.
rewriteTransitionPath ::
    Map.Map State [Transition] ->
    [Int] ->
    Map.Map State State ->
    Transition ->
    StateT SplitBuild IO (Maybe Transition)
rewriteTransitionPath _ [] _ transition = pure $ Just transition
rewriteTransitionPath original (index : rest) replacements transition =
    case atIndex index $ transitionChildren transition of
        Nothing -> pure Nothing
        Just child -> do
            rewritten <- rewriteStatePath original rest replacements child
            pure $ fmap (replaceChild index transition) rewritten

-- | Clone all viable transitions on one path down to a replacement endpoint.
rewriteStatePath ::
    Map.Map State [Transition] ->
    [Int] ->
    Map.Map State State ->
    State ->
    StateT SplitBuild IO (Maybe State)
rewriteStatePath _ [] replacements state = pure $ Map.lookup state replacements
rewriteStatePath original components replacements state = do
    table <- effectiveTable original
    rewritten <- traverse (rewriteTransitionPath original components replacements) $ Map.findWithDefault [] state table
    Just <$> allocateRow (catMaybes rewritten)

-- | Replace one known-valid child position.
replaceChild :: Int -> Transition -> State -> Transition
replaceChild index transition child =
    replaceTransitionChildren
        (take index children <> [child] <> drop (index + 1) children)
        transition
  where
    children = transitionChildren transition

-- | How precisely one observed position must be partitioned.
data ObservationNeed
    = RefinementNeed
    | LiquidSymbolNeed
    deriving (Eq, Ord, Show)

-- | Trie of the finite term positions inspected by one semantic guard.
data PathPlan = PathPlan
    { planObservation :: !(Maybe ObservationNeed)
    , planChildren :: !(Map.Map Int PathPlan)
    }
    deriving (Eq, Ord, Show)

-- | One partition value. Symbol observations also record whether the term is a leaf.
data Observation
    = RefinementObservation !Refinement
    | LiquidSymbolObservation !LiquidSymbol !Bool
    deriving (Eq, Ord, Show)

-- | One state whose language is homogeneous at every planned position.
data StateVariant = StateVariant
    { variantState :: !State
    , variantSignature :: !(Map.Map [Int] Observation)
    , variantSymbols :: !(Map.Map [Int] (LiquidSymbol, Bool))
    }

-- | One candidate transition before equal observation signatures are regrouped.
data TransitionVariant = TransitionVariant
    { transitionVariantSignature :: !(Map.Map [Int] Observation)
    , transitionVariantSymbols :: !(Map.Map [Int] (LiquidSymbol, Bool))
    , transitionVariantValue :: !Transition
    }

-- | Transitions that form one homogeneous split state.
data VariantGroup = VariantGroup
    { groupSignature :: !(Map.Map [Int] Observation)
    , groupSymbols :: !(Map.Map [Int] (LiquidSymbol, Bool))
    , groupTransitions :: ![Transition]
    }

-- | Fresh states and memoized state partitions constructed during one pruning round.
data SplitBuild = SplitBuild
    { splitFreshStates :: [State]
    , splitRows :: !(Map.Map State [Transition])
    , splitMemo :: !(Map.Map (State, PathPlan) [StateVariant])
    , splitProducts :: !(Map.Map (FTA.ProductState State State) State)
    }

-- | Initial state for one splitting round.
emptySplitBuild :: Map.Map State [Transition] -> SplitBuild
emptySplitBuild table = SplitBuild (unusedStates table) Map.empty Map.empty Map.empty

-- | Compile one transition's semantic guard by partitioning only its observed paths.
pruneTransition ::
    Entailment ->
    Map.Map State [Transition] ->
    State ->
    Transition ->
    StateT SplitBuild IO (Either PruneError [Transition])
pruneTransition entailment table parent transition
    | semanticGuard == Top = pure $ Right [setTransitionGuard residualGuard transition]
    | otherwise = do
        candidates <- transitionSpecializations table semanticGuard transition
        check [] candidates
  where
    (semanticGuard, residualGuard) = splitGuard $ constraintGuard $ transitionConstraint transition

    check retained [] = pure $ Right $ reverse retained
    check retained ((specialized, resolved) : rest) = do
        verdict <-
            liftIO $
                evaluateGuardWithShape
                    entailment
                    (lookupResolved resolved)
                    (lookupLeaf resolved)
                    semanticGuard
        case verdict of
            Yes -> check (setTransitionGuard residualGuard specialized : retained) rest
            No -> check retained rest
            Unknown
                | hasAmbiguousActuals resolved -> pure $ Right [transition]
                | otherwise -> pure $ Left $ PruneUnknown parent

    hasAmbiguousActuals resolved =
        not . Set.null . snd $
            substitutionValues
                (lookupResolved resolved)
                (lookupLeaf resolved)
                (\_ _ -> Nothing)
                semanticGuard

    lookupResolved resolved target = do
        (LiquidSymbol symbol refinement, _) <- Map.lookup (unPath target) resolved
        pure (symbol, refinement)

    lookupLeaf resolved target = snd <$> Map.lookup (unPath target) resolved

-- | Replace a transition's guard without changing its ranked symbol or states.
setTransitionGuard :: Guard -> Transition -> Transition
setTransitionGuard guard transition =
    Transition
        (transitionSymbol transition)
        (transitionRefinement transition)
        (transitionChildren transition)
        (transitionConstraint transition){constraintGuard = guard}

-- | Every homogeneous child-state specialization required to evaluate one guard.
transitionSpecializations ::
    Map.Map State [Transition] ->
    Guard ->
    Transition ->
    StateT SplitBuild IO [(Transition, Map.Map [Int] (LiquidSymbol, Bool))]
transitionSpecializations table guard transition = do
    children <- specializeChildren table (planChildren plan) $ transitionChildren transition
    pure
        [ ( replaceTransitionChildren specializedChildren transition
          , rootSymbols `Map.union` childSymbols
          )
        | (specializedChildren, _, childSymbols) <- children
        ]
  where
    plan = planGuard guard
    rootSymbols = case planObservation plan of
        Nothing -> Map.empty
        Just _ -> Map.singleton [] (transitionLiquidSymbol transition, null $ transitionChildren transition)

-- | Partition one state's language by the observations in a path plan.
specializeState ::
    Map.Map State [Transition] ->
    State ->
    PathPlan ->
    StateT SplitBuild IO [StateVariant]
specializeState table state plan = do
    build <- get
    case Map.lookup (state, plan) $ splitMemo build of
        Just variants -> pure variants
        Nothing -> do
            candidates <-
                concat
                    <$> traverse
                        (specializeStateTransition table plan)
                        (Map.findWithDefault [] state table)
            variants <- traverse allocateVariant $ groupVariants candidates
            modify' $ \updated ->
                updated
                    { splitMemo = Map.insert (state, plan) variants $ splitMemo updated
                    }
            pure variants

-- | Specialize one transition inside a state being partitioned.
specializeStateTransition ::
    Map.Map State [Transition] ->
    PathPlan ->
    Transition ->
    StateT SplitBuild IO [TransitionVariant]
specializeStateTransition table plan transition = do
    children <- specializeChildren table (planChildren plan) $ transitionChildren transition
    pure
        [ TransitionVariant
            (rootSignature `Map.union` childSignature)
            (rootSymbols `Map.union` childSymbols)
            (replaceTransitionChildren specializedChildren transition)
        | (specializedChildren, childSignature, childSymbols) <- children
        ]
  where
    liquidSymbol = transitionLiquidSymbol transition
    rootSignature = case planObservation plan of
        Nothing -> Map.empty
        Just need -> Map.singleton [] $ observe need transition
    rootSymbols = case planObservation plan of
        Nothing -> Map.empty
        Just _ -> Map.singleton [] (liquidSymbol, null $ transitionChildren transition)

-- | Cartesian product of child variants, sharing every unobserved child state.
specializeChildren ::
    Map.Map State [Transition] ->
    Map.Map Int PathPlan ->
    [State] ->
    StateT SplitBuild IO [([State], Map.Map [Int] Observation, Map.Map [Int] (LiquidSymbol, Bool))]
specializeChildren table plans children = go 0 children
  where
    go _ [] = pure [([], Map.empty, Map.empty)]
    go index (child : rest) = do
        variants <- case Map.lookup index plans of
            Nothing -> pure [StateVariant child Map.empty Map.empty]
            Just plan -> specializeState table child plan
        suffixes <- go (index + 1) rest
        pure
            [ ( variantState variant : suffixStates
              , prefixMap index (variantSignature variant) `Map.union` suffixSignature
              , prefixMap index (variantSymbols variant) `Map.union` suffixSymbols
              )
            | variant <- variants
            , (suffixStates, suffixSignature, suffixSymbols) <- suffixes
            ]

-- | Prefix every relative observation path by one child index.
prefixMap :: Int -> Map.Map [Int] value -> Map.Map [Int] value
prefixMap index = Map.mapKeysMonotonic (index :)

-- | Allocate one fresh state for a homogeneous transition group.
allocateVariant :: VariantGroup -> StateT SplitBuild IO StateVariant
allocateVariant VariantGroup{groupSignature, groupSymbols, groupTransitions} = do
    state <- allocateRow groupTransitions
    pure $ StateVariant state groupSignature groupSymbols

-- | Regroup transition candidates without disturbing first-seen rank order.
groupVariants :: [TransitionVariant] -> [VariantGroup]
groupVariants = foldl' insertVariant []
  where
    insertVariant [] variant = [singletonGroup variant]
    insertVariant (group : rest) variant
        | groupSignature group == transitionVariantSignature variant =
            group
                { groupTransitions =
                    groupTransitions group <> [transitionVariantValue variant]
                }
                : rest
        | otherwise = group : insertVariant rest variant

    singletonGroup TransitionVariant{transitionVariantSignature, transitionVariantSymbols, transitionVariantValue} =
        VariantGroup
            transitionVariantSignature
            transitionVariantSymbols
            [transitionVariantValue]

-- | Observation used to partition a state's transitions.
observe :: ObservationNeed -> Transition -> Observation
observe RefinementNeed transition = RefinementObservation $ transitionRefinement transition
observe LiquidSymbolNeed transition =
    LiquidSymbolObservation (transitionLiquidSymbol transition) (null $ transitionChildren transition)

-- | Construct the observation trie for every position read by a semantic guard.
planGuard :: Guard -> PathPlan
planGuard guard =
    foldl'
        (flip $ uncurry insertPlan)
        emptyPlan
        observations
  where
    sensitive = Set.fromList $ symbolSensitivePaths guard
    observations =
        [ ( unPath target
          , if Set.member target sensitive then LiquidSymbolNeed else RefinementNeed
          )
        | target <- Set.toList $ Set.fromList $ guardPaths guard
        ]

-- | An observation plan containing no positions.
emptyPlan :: PathPlan
emptyPlan = PathPlan Nothing Map.empty

-- | Insert or strengthen one observed position in a path trie.
insertPlan :: [Int] -> ObservationNeed -> PathPlan -> PathPlan
insertPlan [] need plan =
    plan{planObservation = Just $ maybe need (max need) $ planObservation plan}
insertPlan (index : rest) need plan =
    plan
        { planChildren =
            Map.alter
                (Just . insertPlan rest need . fromMaybe emptyPlan)
                index
                (planChildren plan)
        }

-- | Failure in the paper's prune-similarity-minimize reduction phase.
data ReductionError
    = ReductionPrune !PruneError
    | ReductionSimilarity !SimilarityError
    | ReductionMinimize !MinimizeError
    deriving (Eq, Show)

{- | Apply one complete LTA reduction phase to a static automaton.

This keeps the paper's reduction order: semantic pruning, similarity inference,
then minimization.
-}
reduce :: Entailment -> Subtyping -> Automaton -> IO (Either ReductionError Automaton)
reduce entailment subtyping automaton = do
    pruned <- prune entailment automaton
    case pruned of
        Left err -> pure $ Left $ ReductionPrune err
        Right reduced -> do
            inferred <- similarity subtyping reduced
            pure $ do
                related <- first ReductionSimilarity inferred
                first ReductionMinimize $ minimize reduced related
