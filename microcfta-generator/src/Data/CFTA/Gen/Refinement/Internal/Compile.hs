{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

{- | Compile a refinement generator with a solver, and check candidates explicitly.

'compile' folds the recipe of a generator whose constructors carry guards.
Each child language is grouped by the finite observations its parent guard
reads: the label at the child's root, and at deeper requested paths. The
solver decides a guard once per tuple of child groups, the accepted tuples
become one join per constructor, and an imported automaton is pruned and
split by the same observations without enumerating its terms. The result is
an ordinary generator of the engine, finite or, for a recursive import,
recursive, with exact counts, ranks, and structural shrinking. 'validOutcomes' is the explicit oracle: it enumerates
every candidate and checks each complete witness.
-}
module Data.CFTA.Gen.Refinement.Internal.Compile (
    compile,
    validOutcomes,
    reportTimeLimit,
    spineArity,
) where

import Control.Exception (handle)
import Data.Bifunctor (first)
import qualified Data.IntMap.Strict as IntMap
import Data.List (nub, sortOn)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import Data.Ratio (denominator, numerator)
import qualified Data.Set as Set
import qualified Data.Tree as Tree

import Data.CFTA.Equality.Constraint (EqConstraints (EmptyConstraints))
import Data.CFTA.Gen
import qualified Data.CFTA.Gen.Internal.Flat as Flat
import Data.CFTA.Gen.Internal.Grouped (groupKeys)
import Data.CFTA.Gen.Internal.Static (
    Outcome (outcomeMass, outcomeTerm),
    OutcomeIndex (outcomeCardinality, outcomeSelect),
    Static (staticOutcomes),
 )
import Data.CFTA.Gen.Internal.Types (Gen (..), Grouped (..), Language (..), Recipe (..))
import Data.CFTA.Gen.Label (ChoiceIndex)
import Data.CFTA.Gen.Refinement.Internal.Witness
import Data.CFTA.Index (
    Arity (..),
    Depth (..),
    Weight (..),
    childIndexes,
    countWeight,
    everyRank,
 )
import Data.CFTA.Refinement
import Data.CFTA.Refinement.LiquidFixpoint (TimeLimitReached (..))

-- | A generator over liquid tree automata.
type LTAGen = Gen Symbol

-- | A grouped generator over liquid tree automata.
type LTAGrouped key = Grouped Symbol key

{- | The observations that identify one group: the label at each observed
path, and whether that node is a leaf. A path that a member does not have is
absent. The position orders the groups of one language by the first member
that has their observations, so ranks follow source order.
-}
data ObservationKey = ObservationKey
    { keyPosition :: !Int
    , keyObservations :: !Observations
    }
    deriving (Eq, Ord, Show)

-- | The key of a group that nothing observes.
noObservations :: ObservationKey
noObservations = ObservationKey 0 Map.empty

{- | Regroup by observations, positioned by first appearance.

The keys of the given groups are in source order. Groups with the same
observations merge, and the merged group takes the position of the first.
-}
reposition :: (key -> Observations) -> LTAGrouped key a -> LTAGrouped ObservationKey a
reposition observationsOf grouped = regroupOn rekey grouped
  where
    positions =
        Map.fromListWith (\_ earlier -> earlier) $
            zip (map observationsOf $ groupKeys grouped) [0 ..]
    rekey key = ObservationKey (positions Map.! observationsOf key) (observationsOf key)

-- | The number of child positions in an applicative spine.
spineArity :: Gen symbol a -> Arity
spineArity generator = case genRecipe generator of
    Lifted _ -> 0
    Mapped _ inner -> spineArity inner
    Applied functions arguments -> spineArity functions + spineArity arguments
    _ -> 1

-- TODO: Consider positions that look through a choice whose alternatives all
-- give the same number of children, so that a guard can read the children of
-- a choice of products such as @oneof [pair1, pair2]@. That changes
-- 'spineArity', the observations, and 'candidatesOf'. A built child that gives
-- several terms, such as a join, or no term, such as 'fromIndexed', has the
-- same problem, and 'alignedSpine' refuses it in the same way.

{- | Whether each part of an applicative spine gives its constructor one
child, as 'spineArity' counts it. 'rootCount' gives the number of children of
each part. When a part gives another number, a guard that reads the children
by position reads the wrong ones.
-}
alignedSpine :: Gen symbol a -> Bool
alignedSpine generator = case genRecipe generator of
    Lifted _ -> True
    Mapped _ inner -> alignedSpine inner
    Applied functions arguments -> alignedSpine functions && alignedSpine arguments
    _ -> rootCount generator == Just 1

{- | The number of children that each member of a generator gives its
constructor, when all members give the same number. The children are the
roots that 'surface' gives for the term of the member, and 'validOutcomes'
reads the same children.

A constructor, an import, and an integer leaf give one child, and @pure@
gives none. A choice removes its own wrapper, so a choice of products gives
several children, and a choice of @pure@ values gives none. A built language
gives the number that its members give: a source without symbols, such as
'fromIndexed' and the pools of @freeze@ and @samplePool@, gives none, and a
join gives one for each side. A language without members gives one, so that
it does not refuse a guard. The result is 'Nothing' when two members give
different numbers, and for a recursive or opaque built language.
-}
rootCount :: Gen symbol a -> Maybe Int
rootCount generator = case genRecipe generator of
    Lifted _ -> Just 0
    Mapped _ inner -> rootCount inner
    Applied functions arguments -> (+) <$> rootCount functions <*> rootCount arguments
    Chosen alternatives -> common $ map (rootCount . snd) alternatives
    Uniform alternatives -> common $ map rootCount alternatives
    Closed{} -> Just 1
    ClosedBy{} -> Just 1
    Imported{} -> Just 1
    Built -> case genLanguage generator of
        TransparentLanguage (Right static) ->
            let outcomes = staticOutcomes static
             in common
                    [ either (const Nothing) (Just . length . surface . outcomeTerm) $ outcomeSelect outcomes rank
                    | rank <- everyRank $ outcomeCardinality outcomes
                    ]
        TransparentLanguage (Left _) -> Just 1
        CyclicLanguage (Left _) -> Just 1
        _ -> Nothing
  where
    -- The number that every member gives. A list without members gives one.
    common counts = case counts of
        [] -> Just 1
        count : rest | all (== count) rest -> count
        _ -> Nothing

-- | Whether a generator waits for 'compile'.
deferred :: Gen symbol a -> Bool
deferred generator = case genLanguage generator of
    TransparentLanguage (Left SourceRequiresCompilation) -> True
    _ -> False

{- | Compile a generator whose guards need the solver.

A generator that the engine built at construction is returned unchanged. All
solver work finishes here, so the result samples, replays, and shrinks
without the solver. A guard the compiler cannot decide from its observations,
a solver that cannot decide a guard, a solver query that reaches its time
limit, and a guard the symbolic counter cannot count are compile failures; an
empty language is not.
-}
compile :: Entailment -> LTAGen a -> IO (Either GenError (LTAGen a))
compile uncachedEntailment generator
    | not (deferred generator) = pure $ Right generator
    | otherwise = reportTimeLimit $ do
        entailment <- cacheEntailment uncachedEntailment
        fmap ungroup <$> compileGen entailment [path []] generator

-- | Compile one generator, grouped by the observations its parent needs.
compileGen :: Entailment -> [Path] -> LTAGen a -> IO (Either GenError (LTAGrouped ObservationKey a))
compileGen entailment requested generator
    | not (deferred generator) && null requested = pure $ Right $ keyed noObservations generator
    | otherwise = case genRecipe generator of
        Built -> pure $ groupBuilt requested generator
        Lifted value -> pure $ Right $ keyed noObservations $ pure value
        Mapped transform inner -> fmap (mapWithKey (const transform)) <$> compileGen entailment requested inner
        Applied _ _ ->
            fmap (regroupOn (const noObservations))
                <$> compileSpine entailment (replicate (fromEnum $ spineArity generator) []) generator
        Chosen alternatives -> do
            compiled <- traverse (compileGen entailment requested . snd) alternatives
            pure $ choose (map fst alternatives) <$> sequence compiled
        Uniform alternatives -> do
            compiled <- traverse (compileGen entailment requested) alternatives
            pure $ (\groups -> choose (uniformWeights groups) groups) <$> sequence compiled
        Closed symbol constraint child -> compileNode entailment requested (const $ Right symbol) False constraint child
        ClosedBy symbolOf constraint child -> compileNode entailment requested (fmap symbolOf . traverse rootOf) True constraint child
        Imported bound order automaton -> compileImport entailment requested bound order automaton
  where
    -- A choice of the compiled alternatives, with one weight for each.
    choose weights groups =
        reposition (keyObservations . snd) $
            frequencies
                [ (weight, regroupOn (index,) grouped)
                | (index :: ChoiceIndex, (weight, grouped)) <- zip [0 ..] $ zip weights groups
                , not $ emptyGroups grouped
                ]
    -- The weights of 'uniformly': each finite alternative weighs its members,
    -- and a recursive alternative makes the choice equal.
    uniformWeights groups
        | any recursiveGroup groups = map (const 1) groups
        | otherwise = map (either (const 1) (countWeight . sum) . sizes) groups
    recursiveGroup (CyclicGrouped _) = True
    recursiveGroup _ = False
    -- The root label retained by a group, which a root-computed constructor needs.
    rootOf :: ObservationKey -> Either GenError Symbol
    rootOf key =
        maybe (Left MissingRootObservation) (\(Observed label _) -> Right label) $ Map.lookup (path []) $ keyObservations key

-- | Whether a grouped generator has no member.
emptyGroups :: LTAGrouped key a -> Bool
emptyGroups grouped = case sizes grouped of
    Left EmptyGenerator -> True
    Right groups -> all (== 0) groups
    Left _ -> False

{- | Group a language the engine built by the requested observations.

Without observations the language is one group. With observations every
member is read back with its term; a member's term is the user's part of the
engine's labelled term.
-}
groupBuilt :: [Path] -> LTAGen a -> Either GenError (LTAGrouped ObservationKey a)
groupBuilt requested generator
    | deferred generator = Left SourceRequiresCompilation
    | null requested = Right $ keyed noObservations generator
    | otherwise = do
        total <- cardinality generator
        members <- traverse member $ everyRank total
        let scale = foldr (\(mass, _, _) -> lcm (denominator mass)) 1 members
        pure
            $ reposition keyObservations
            $ frequencies
                [ (Weight $ numerator (mass * fromInteger scale), keyed (ObservationKey rank $ observe forest) (rebuild forest value))
                | (rank, (mass, value, forest)) <- zip [0 ..] members
                ]
  where
    -- Each member keeps its own mass, so an 'atomic' choice keeps its distribution.
    member rank = (,,) <$> massAt rank <*> unrank generator rank <*> (surface <$> termAt generator rank)
    massAt rank = case genLanguage generator of
        TransparentLanguage result -> do
            static <- result
            outcomeMass <$> outcomeSelect (staticOutcomes static) rank
        _ -> Left UnboundedGenerator
    observe [term] = Map.fromList [(target, observation) | target <- requested, Just observation <- [labelAt target term]]
    observe _ = Map.empty
    rebuild [Tree.Node label children] value = node label $ withChildren children value
    rebuild forest value = withChildren forest value

    -- The label at one path of a term, and whether it is a leaf.
    labelAt :: Path -> Tree.Tree Symbol -> Maybe Observed
    labelAt target = go (unPath target)
      where
        go [] (Tree.Node label children) = Just $ Observed label $ leafnessOf children
        go (ChildIndex index : rest) (Tree.Node _ children) = case drop index children of
            child : _ -> go rest child
            [] -> Nothing

-- | A generator of one value whose term has the given children.
withChildren :: [Tree.Tree Symbol] -> a -> LTAGen a
withChildren children value = foldl (\prefix child -> prefix <* rebuild child) (pure value) children
  where
    rebuild (Tree.Node label grandchildren) = node label $ withChildren grandchildren ()

{- | Compile a child description as one group per tuple of child observations.

Each position of the applicative spine is compiled with the observations its
parent requests at that position, and the positions are joined left to
right. An empty position empties the product without compiling the rest.
-}
compileSpine :: Entailment -> [[Path]] -> LTAGen a -> IO (Either GenError (LTAGrouped [ObservationKey] a))
compileSpine entailment requirements generator = case genRecipe generator of
    Lifted value -> pure $ Right $ keyed [] $ pure value
    Mapped transform inner -> fmap (mapWithKey (const transform)) <$> compileSpine entailment requirements inner
    Applied functions arguments -> do
        let (functionRequirements, argumentRequirements) = splitAt (fromEnum $ spineArity functions) requirements
        compiledFunctions <- compileSpine entailment functionRequirements functions
        case compiledFunctions of
            Left err -> pure $ Left err
            Right functionGroups
                | emptyGroups functionGroups -> pure $ Right $ frequencies []
                | otherwise -> do
                    compiledArguments <- compileSpine entailment argumentRequirements arguments
                    case compiledArguments of
                        Left err -> pure $ Left err
                        Right argumentGroups -> do
                            related <- relateGroupsM (\_ _ -> pure $ Right True) (<>) functionGroups argumentGroups
                            pure $ mapWithKey (\_ (function, argument) -> function argument) <$> related
    _ -> fmap (regroupOn pure) <$> compileGen entailment (concat $ take 1 requirements) generator

{- | Compile one guarded constructor.

The children are grouped by the paths the guard reads below each position,
by what the parent requests, and by their roots when the constructor's label
depends on them. The solver decides the guard once per tuple of child
groups; the accepted tuples are closed with the constructor and regrouped by
the parent's observations.
-}
compileNode ::
    Entailment ->
    [Path] ->
    ([ObservationKey] -> Either GenError Symbol) ->
    Bool ->
    Constraint ->
    LTAGen a ->
    IO (Either GenError (LTAGrouped ObservationKey a))
compileNode entailment requested labelOf needsRoots constraint child
    | not (all null childRequirements) && not (alignedSpine child) = pure $ Left ChildNotOneTerm
    | otherwise = do
        compiledChild <- compileSpine entailment childRequirements child
        case compiledChild of
            Left err -> pure $ Left err
            Right childGroups -> do
                retained <- filterGroupsM decide childGroups
                pure $ reposition closeObservations . nodeWithKey closeLabel <$> retained
  where
    arity = spineArity child
    -- The term of the constructor is a leaf when its child description gives no
    -- term. When 'rootCount' gives no number, the leafness is 'Mixed', which an
    -- observer reads as not known.
    leafness = case rootCount child of
        Just 0 -> Leaf
        Just _ -> Inner
        Nothing -> Mixed
    observed = nub $ requested <> constraintPaths constraint <> roots
      where
        roots
            | needsRoots = [path [index] | index <- childIndexes arity]
            | otherwise = []
    childRequirements =
        [ nub [path suffix | target <- observed, index : suffix <- [unPath target], index == childIndex]
        | childIndex <- childIndexes arity
        ]
    decide childKeys = case labelOf childKeys of
        Left err -> pure $ Left err
        Right label -> constraintDecision entailment label leafness constraint childKeys
    -- Only accepted tuples are closed, and their labels were computed to accept them.
    closeLabel childKeys = case labelOf childKeys of
        Right label -> label
        Left _ ->
            error
                "microcfta-generator bug in Data.CFTA.Gen.Refinement.Internal.Compile.compileNode: \
                \an accepted group lost its root observation"
    closeObservations childKeys = parentObservations requested (closeLabel childKeys) leafness childKeys

-- | Decide one guard from the leafness of the constructor and the already-grouped child observations.
constraintDecision :: Entailment -> Symbol -> Leafness -> Constraint -> [ObservationKey] -> IO (Either GenError Bool)
constraintDecision entailment label leafness constraint childKeys = do
    verdict <- decide $ constraintAsGuard constraint
    case verdict of
        Yes -> pure $ Right True
        No -> pure $ Right False
        -- Sparse observations cannot decide an equality of complete subtrees.
        -- Report that only when the rest of the guard is decided: otherwise
        -- the solver could not decide the rest.
        Unknown -> do
            semantic <- decide $ fst $ splitGuard $ constraintGuard constraint
            -- With a solver that answers every query, the guard is decided when
            -- the observations decide its equalities: then only the solver left
            -- it undecided. This also covers an equality under 'Or' or 'Not'.
            answered <- traverse (\answer -> decideWith (Entailment $ \_ _ -> pure answer) $ constraintAsGuard constraint) [Yes, No]
            pure $ case semantic of
                Unknown -> Left SolverUnknown
                _
                    | Unknown `notElem` answered -> Left SolverUnknown
                    -- An equality reads a node whose members are leaves and non-leaves.
                    | any unknownLeaf $ guardPaths $ snd $ splitGuard $ constraintGuard constraint ->
                        Left ChildNotOneTerm
                    | constraintEqualities constraint /= EmptyConstraints ->
                        Left $ RelationalEqualityUnsupported $ constraintEqualities constraint
                    | containsSame (constraintGuard constraint) ->
                        Left $ RelationalSyntacticEqualityUnsupported $ constraintGuard constraint
                    | otherwise -> Left SolverUnknown
  where
    observations = completeObservations label leafness childKeys
    unknownLeaf target = case Map.lookup target observations of
        Just (Observed _ Mixed) -> True
        _ -> False
    decide = decideWith entailment
    decideWith entailment' = evaluateGuardWithShape entailment' (`Map.lookup` observations)

-- | The observations a parent requests above one accepted node.
parentObservations :: [Path] -> Symbol -> Leafness -> [ObservationKey] -> Observations
parentObservations requested label leafness childKeys =
    Map.restrictKeys (completeObservations label leafness childKeys) $ Set.insert (path []) $ Set.fromList requested

{- | The root, with its label and leafness, plus the sparse observations
retained by every direct child group.
-}
completeObservations :: Symbol -> Leafness -> [ObservationKey] -> Observations
completeObservations label leafness childKeys =
    Map.fromList $
        (path [], Observed label leafness)
            : [ (path $ childIndex : unPath target, observed)
              | (childIndex, childKey) <- zip [0 ..] childKeys
              , (target, observed) <- Map.toList $ keyObservations childKey
              ]

{- | Compile an imported automaton.

The automaton is bounded, pruned with the solver, and split into one
sub-automaton per tuple of requested observations. Each part is read by the
engine, which counts it symbolically where alternatives overlap or guards of
Boolean equality remain. A guard the symbolic counter cannot count is
reported before any part is read.
-}
compileImport ::
    (Ord key) =>
    Entailment ->
    [Path] ->
    Maybe Depth ->
    (Symbol -> key) ->
    Automaton ->
    IO (Either GenError (LTAGrouped ObservationKey (Tree.Tree Symbol)))
compileImport entailment requested bound order automaton
    | Just depth <- bound, depth < 0 = pure $ Right $ frequencies []
    | otherwise = do
        pruned <- prune entailment $ maybe id boundDepth bound automaton
        pure $ do
            reduced <- first pruningError pruned
            mapM_ (first ResidualGuard . constraintIndicators . edgeConstraint) $ concat $ IntMap.elems $ reachable reduced
            -- The parts are sorted by their observations, which order by
            -- symbol text and refinement, so the ranks do not depend on the
            -- order in which the process interned the edges.
            pure $
                uniformlyGrouped
                    [ keyed (ObservationKey position observations) $ Flat.fromAutomaton order part
                    | (position, (observations, part)) <- zip [0 ..] $ sortOn fst $ splitByObservations requested reduced
                    ]
  where
    pruningError (PruneUnknown _) = SolverUnknown
    pruningError err = InvalidPruning err

{- | Partition the language of an automaton by the labels at the requested paths.

Each part accepts exactly the terms with one tuple of observations, and the
parts share their unobserved subgraphs. The parts are in the order of their
first transition. A recursive node is unfolded once per requested level.
-}
splitByObservations :: [Path] -> Automaton -> [(Observations, Automaton)]
splitByObservations [] root = [(Map.empty, root)]
splitByObservations requested root = case root of
    Node edges -> mergeParts $ concatMap splitEdge edges
    Mu _ -> splitByObservations requested $ unfoldOuterRec root
    _ -> []
  where
    observesRoot = path [] `elem` requested
    childRequests = Map.fromListWith (<>) [(index, [path rest]) | target <- requested, index : rest <- [unPath target]]

    splitEdge (Transition symbol refinement children constraint) =
        [ (Map.unions (rootObservation : childObservations), Node [Transition symbol refinement parts constraint])
        | (childObservations, parts) <- combinations $ zipWith splitChild [0 ..] children
        ]
      where
        rootObservation
            | observesRoot = Map.singleton (path []) $ Observed (RefinedSymbol symbol refinement) $ leafnessOf children
            | otherwise = Map.empty

        splitChild index child =
            [ (Map.mapKeys (path . (index :) . unPath) observations, part)
            | (observations, part) <- splitByObservations (Map.findWithDefault [] index childRequests) child
            ]

    combinations =
        foldr
            (\options rest -> [(observations : more, part : parts) | (observations, part) <- options, (more, parts) <- rest])
            [([], [])]

-- | Merge the parts with equal observations, keeping the order of first appearance.
mergeParts :: [(Observations, Automaton)] -> [(Observations, Automaton)]
mergeParts parts =
    [ (observations, union [part | (candidate, part) <- parts, candidate == observations])
    | observations <- nub $ map fst parts
    ]

-- | Report a solver query that reached its time limit as 'SolverTimeLimit'.
reportTimeLimit :: IO (Either GenError a) -> IO (Either GenError a)
reportTimeLimit = handle $ \(TimeLimitReached milliseconds) -> pure $ Left $ SolverTimeLimit milliseconds

{- | Check every candidate explicitly and keep the accepted values in order.

Every combination the recipe describes is a candidate. Each complete witness
is checked with the solver, guard by guard. An imported automaton is pruned
first and contributes its accepted terms.
-}
validOutcomes :: Entailment -> LTAGen a -> IO (Either GenError [a])
validOutcomes uncachedEntailment generator = reportTimeLimit $ do
    entailment <- cacheEntailment uncachedEntailment
    candidates <- candidatesOf entailment generator
    case candidates of
        Left err -> pure $ Left err
        Right members -> fmap catMaybes . sequence <$> traverse (accept entailment) members
  where
    -- The value of an accepted candidate.
    accept :: Entailment -> (a, [Witness]) -> IO (Either GenError (Maybe a))
    accept entailment (value, witnesses) = go witnesses
      where
        go [] = pure $ Right $ Just value
        go (witness : rest) = do
            verdict <- checkWitness entailment witness
            case verdict of
                Yes -> go rest
                No -> pure $ Right Nothing
                Unknown -> pure $ Left SolverUnknown

-- | Every candidate of a recipe with the witnesses of its positions.
candidatesOf :: Entailment -> LTAGen a -> IO (Either GenError [(a, [Witness])])
candidatesOf entailment generator = case genRecipe generator of
    Built -> pure $ builtCandidates generator
    Lifted value -> pure $ Right [(value, [])]
    Mapped transform inner -> fmap (map (first transform)) <$> candidatesOf entailment inner
    Applied functions arguments -> do
        functionCandidates <- candidatesOf entailment functions
        argumentCandidates <- candidatesOf entailment arguments
        pure $
            ( \fs xs ->
                [ (function argument, functionWitnesses <> argumentWitnesses)
                | (function, functionWitnesses) <- fs
                , (argument, argumentWitnesses) <- xs
                ]
            )
                <$> functionCandidates
                <*> argumentCandidates
    Chosen alternatives -> fmap concat . sequence <$> traverse (candidatesOf entailment . snd) alternatives
    Uniform alternatives -> fmap concat . sequence <$> traverse (candidatesOf entailment) alternatives
    Closed label constraint child -> fmap (close (const label) constraint) <$> candidatesOf entailment child
    ClosedBy labelOf constraint child -> fmap (close (labelOf . map witnessLabel) constraint) <$> candidatesOf entailment child
    Imported bound order automaton -> do
        imported <- compileImport entailment [] bound order automaton
        pure $ imported >>= builtCandidates . ungroup
  where
    close labelOf constraint = map $ \(value, witnesses) -> (value, [Witness (labelOf witnesses) constraint witnesses])

-- | The members of a built language, each with the witnesses of its term.
builtCandidates :: LTAGen a -> Either GenError [(a, [Witness])]
builtCandidates generator
    | deferred generator = Left SourceRequiresCompilation
    | otherwise = do
        total <- cardinality generator
        traverse member $ everyRank total
  where
    member rank = (\value term -> (value, map termWitness $ surface term)) <$> unrank generator rank <*> termAt generator rank
