{-# LANGUAGE ExistentialQuantification #-}
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
an ordinary finite generator of the engine, with exact counts, ranks, and
structural shrinking. 'validOutcomes' is the explicit oracle: it enumerates
every candidate and checks each complete witness.
-}
module Data.CFTA.Gen.Refinement.Internal.Compile (
    compile,
    validOutcomes,
    spineArity,
    liquidOrder,
) where

import Control.Monad ((<=<))
import Data.Bifunctor (first)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import qualified Data.IntMap.Strict as IntMap
import Data.List (mapAccumL, nub, partition)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, isJust, listToMaybe)
import qualified Data.Set as Set
import Data.String (fromString)
import Data.Text (Text)
import qualified Data.Tree as Tree
import System.Mem.StableName (StableName, eqStableName, hashStableName, makeStableName)
import Unsafe.Coerce (unsafeCoerce)

import Data.CFTA.Equality.Constraint (EqConstraints (EmptyConstraints))
import Data.CFTA.Gen
import Data.CFTA.Gen.Internal.Bucket (KeyedBucket (..), mergeComponentsByKey)
import qualified Data.CFTA.Gen.Internal.Flat as Flat
import Data.CFTA.Gen.Internal.Static (labelledLeavesStatic, pointsStatic)
import Data.CFTA.Gen.Internal.Types (Gen (..), Grouped (..), Language (..), Recipe (..))
import Data.CFTA.Gen.Refinement.Internal.Witness
import Data.CFTA.Refinement
import Data.CFTA.Refinement.Expression (literal, refinementFormula, substitute, true, variable, (.&&), (.==))
import Data.CFTA.Refinement.Lattice (onlyPoint, pointAt, pointCount, points)

-- | A generator over liquid tree automata.
type LTAGen = Gen LiquidSymbol LiquidConstraint

-- | A grouped generator over liquid tree automata.
type LTAGrouped key = Grouped LiquidSymbol LiquidConstraint key

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

-- | The label and leaf flag at each observed path of a term.
type Observations = Map.Map Path Observed

-- | One observed node: its label, and whether it is a leaf.
data Observed = Observed !LiquidSymbol !Bool
    deriving (Eq, Show)

instance Ord Observed where
    compare (Observed leftLabel leftLeaf) (Observed rightLabel rightLeaf) =
        compare (liquidOrder leftLabel, leftLeaf) (liquidOrder rightLabel, rightLeaf)

-- | The key of a group that nothing observes.
noObservations :: ObservationKey
noObservations = ObservationKey 0 Map.empty

{- | Regroup by observations, positioned by first appearance.

The keys of the given groups are in source order. Groups with the same
observations merge, and the merged group takes the position of the first.
-}
reposition :: (key -> Observations) -> LTAGrouped key a -> LTAGrouped ObservationKey a
reposition observationsOf grouped = regroupBy rekey grouped
  where
    positions =
        Map.fromListWith (\_ earlier -> earlier) $
            zip (map observationsOf $ either (const []) Map.keys $ sizes grouped) [0 ..]
    rekey key = ObservationKey (positions Map.! observationsOf key) (observationsOf key)

-- | Rank symbolic counts by symbol text and refinement, not by interning order.
liquidOrder :: LiquidSymbol -> (Text, Formula)
liquidOrder (LiquidSymbol (Symbol name) refinement) = (name, refinement)

-- | The number of child positions in an applicative spine.
spineArity :: Gen symbol constraint a -> Int
spineArity generator = case genRecipe generator of
    Lifted _ -> 0
    Mapped _ inner -> spineArity inner
    Applied functions arguments -> spineArity functions + spineArity arguments
    _ -> 1

-- | What one compilation shares: the cached solver, and the groups compiled so far.
data Compiler = Compiler
    { compilerEntailment :: !Entailment
    , compilerMemo :: !(IORef (IntMap.IntMap [Compiled]))
    }

{- | One compiled generator: its stable name, the paths requested of it, and
its groups. A stable name identifies one heap object, so the groups have the
type of that object.
-}
data Compiled = forall a. Compiled !(StableName (LTAGen a)) ![Path] !(Either GenError (LTAGrouped ObservationKey a))

-- | Whether a generator waits for 'compile'.
deferred :: Gen symbol constraint a -> Bool
deferred generator = case genLanguage generator of
    TransparentLanguage (Left SourceRequiresCompilation) -> True
    _ -> False

{- | Compile a generator whose guards need the solver.

A generator that the engine built at construction is returned unchanged. All
solver work finishes here, so the result samples, replays, and shrinks
without the solver. A guard the compiler cannot decide from its observations,
a solver that cannot decide a guard, and a guard the symbolic counter cannot
count are compile failures; an empty language is not.
-}
compile :: Entailment -> LTAGen a -> IO (Either GenError (LTAGen a))
compile uncachedEntailment generator
    | not (deferred generator) = pure $ Right generator
    | otherwise = do
        entailment <- cacheEntailment uncachedEntailment
        memo <- newIORef IntMap.empty
        fmap ungroup <$> compileGen (Compiler entailment memo) [path []] generator

-- | Compile one generator, grouped by the observations its parent needs.
compileGen :: Compiler -> [Path] -> LTAGen a -> IO (Either GenError (LTAGrouped ObservationKey a))
compileGen compiler requested generator = do
    name <- makeStableName $! generator
    known <- readIORef $ compilerMemo compiler
    case [ unsafeCoerce result
         | Compiled other paths result <- IntMap.findWithDefault [] (hashStableName name) known
         , eqStableName name other
         , paths == requested
         ] of
        result : _ -> pure result
        [] -> do
            result <- compileGenOnce compiler requested generator
            modifyIORef' (compilerMemo compiler) $ IntMap.insertWith (<>) (hashStableName name) [Compiled name requested result]
            pure result

-- | Compile one generator that the memo does not hold.
compileGenOnce :: Compiler -> [Path] -> LTAGen a -> IO (Either GenError (LTAGrouped ObservationKey a))
compileGenOnce compiler requested generator
    | not (deferred generator) && null requested = pure $ Right $ keyed noObservations generator
    | otherwise = case genRecipe generator of
        Built -> pure $ groupBuilt requested generator
        Lifted value -> pure $ Right $ keyed noObservations $ pure value
        Mapped transform inner -> fmap (mapWithKey (const transform)) <$> compileGen compiler requested inner
        Applied _ _ ->
            fmap (regroupBy (const noObservations))
                <$> compileSpine compiler (replicate (spineArity generator) []) generator
        Chosen alternatives -> do
            compiled <-
                traverse (\(weight, alternative) -> fmap (weight,) <$> compileGen compiler requested alternative) alternatives
            pure $ do
                weighted <- sequence compiled
                pure
                    $ reposition (keyObservations . snd)
                    $ frequencies
                        [ (weight, regroupBy (index,) grouped)
                        | (index :: Int, (weight, grouped)) <- zip [0 ..] weighted
                        , not $ emptyGroups grouped
                        ]
        Closed symbol constraint child -> compileNode compiler requested (const $ Right symbol) False constraint child
        ClosedBy symbolOf constraint child -> compileNode compiler requested (symbolOf <=< traverse rootOf) True constraint child
        Imported bound automaton -> compileImport (compilerEntailment compiler) requested bound automaton
        Integers constraint -> pure $ compileIntegers constraint

{- | Count the integers that the conditions of an integer leaf admit.

The group carries no observation, so a guard cannot read the leaf as one
refinement. Each member is a leaf refined as its integer.
-}
compileIntegers :: LiquidConstraint -> Either GenError (LTAGrouped ObservationKey Integer)
compileIntegers constraint = case points [valueName] (integerDomain constraint) of
    Left err -> Left $ UncountableIntegers err
    Right found
        | pointCount found == 0 -> Right $ frequencies []
        | otherwise ->
            Right
                $ keyed noObservations
                $ Gen Built
                $ TransparentLanguage
                $ Right
                $ labelledLeavesStatic
                    (LiquidSymbol (fromString "integers") $ integerDomain constraint)
                    (integerSymbol . valueAt found)
                    (Indexed (pointCount found) (valueAt found))
  where
    valueAt found rank = case pointAt found rank of
        [value] -> value
        _ ->
            error
                "microcfta-generator bug in Data.CFTA.Gen.Refinement.Internal.Compile.compileIntegers: \
                \a point of one variable has another dimension"

-- | The name of the value in a refinement.
valueName :: String
valueName = "v"

-- | The leaf of one integer, refined as itself.
integerSymbol :: Integer -> LiquidSymbol
integerSymbol value = LiquidSymbol (fromString $ show value) $ refinementFormula (.== literal value)

-- | The conjunction of the conditions on an integer leaf.
integerDomain :: LiquidConstraint -> Formula
integerDomain constraint = foldr (.&&) true $ conditions $ constraintAsGuard constraint
  where
    conditions Top = []
    conditions (And guards) = concatMap conditions guards
    conditions (Satisfies target formula) | target == path [] = [formula]
    conditions guard =
        error $
            "microcfta-generator bug in Data.CFTA.Gen.Refinement.Internal.Compile.integerDomain: \
            \an integer leaf carries the guard "
                <> show guard

-- | Whether a grouped generator has no member.
emptyGroups :: LTAGrouped key a -> Bool
emptyGroups grouped = case sizes grouped of
    Left EmptyGenerator -> True
    Right groups -> all (== 0) groups
    Left _ -> False

-- | The root label retained by a group, which a root-computed constructor needs.
rootOf :: ObservationKey -> Either GenError LiquidSymbol
rootOf key =
    maybe (Left MissingRootObservation) (\(Observed label _) -> Right label) $ Map.lookup (path []) $ keyObservations key

{- | Group a language the engine built by the requested observations.

Without observations the language is one group. With observations every
member is read back with its term; a member's term is the user's part of the
engine's labelled term.
-}
groupBuilt :: [Path] -> LTAGen a -> Either GenError (LTAGrouped ObservationKey a)
groupBuilt requested generator
    | deferred generator = Left SourceRequiresCompilation
    | null requested = Right $ keyed noObservations generator
    | Left EmptyGenerator <- cardinality generator = Right $ frequencies []
    | otherwise = do
        total <- cardinality generator
        members <- traverse member [0 .. total - 1]
        pure
            $ reposition keyObservations
            $ uniformlyGrouped
                [ keyed (ObservationKey rank $ observe forest) (rebuild forest value)
                | (rank, (value, forest)) <- zip [0 ..] members
                ]
  where
    member rank = (\value term -> (value, surface term)) <$> unrank generator rank <*> termAt generator rank
    observe [term] = Map.fromList [(target, observation) | target <- requested, Just observation <- [labelAt target term]]
    observe _ = Map.empty
    rebuild [Tree.Node label children] value = node label $ withChildren children value
    rebuild forest value = withChildren forest value

-- | A generator of one value whose term has the given children.
withChildren :: [Tree.Tree LiquidSymbol] -> a -> LTAGen a
withChildren children value = foldl (\prefix child -> prefix <* rebuild child) (pure value) children
  where
    rebuild (Tree.Node label grandchildren) = node label $ withChildren grandchildren ()

-- | The label at one path of a term, and whether it is a leaf.
labelAt :: Path -> Tree.Tree LiquidSymbol -> Maybe Observed
labelAt target = go (unPath target)
  where
    go [] (Tree.Node label children) = Just $ Observed label $ null children
    go (index : rest) (Tree.Node _ children) = case drop index children of
        child : _ -> go rest child
        [] -> Nothing

{- | Compile a child description as one group per tuple of child observations.

Each position of the applicative spine is compiled with the observations its
parent requests at that position, and the positions are joined left to
right. An empty position empties the product without compiling the rest.
-}
compileSpine :: Compiler -> [[Path]] -> LTAGen a -> IO (Either GenError (LTAGrouped [ObservationKey] a))
compileSpine compiler requirements generator = case genRecipe generator of
    Lifted value -> pure $ Right $ keyed [] $ pure value
    Mapped transform inner -> fmap (mapWithKey (const transform)) <$> compileSpine compiler requirements inner
    Applied functions arguments -> do
        let (functionRequirements, argumentRequirements) = splitAt (spineArity functions) requirements
        compiledFunctions <- compileSpine compiler functionRequirements functions
        case compiledFunctions of
            Left err -> pure $ Left err
            Right functionGroups
                | emptyGroups functionGroups -> pure $ Right $ frequencies []
                | otherwise -> do
                    compiledArguments <- compileSpine compiler argumentRequirements arguments
                    case compiledArguments of
                        Left err -> pure $ Left err
                        Right argumentGroups -> do
                            related <- relateGroupsM (\_ _ -> pure $ Right True) (<>) functionGroups argumentGroups
                            pure $ mapWithKey (\_ (function, argument) -> function argument) <$> related
    _ -> fmap (regroupBy pure) <$> compileGen compiler (concat $ take 1 requirements) generator

{- | Compile one guarded constructor.

The children are grouped by the paths the guard reads below each position,
by what the parent requests, and by their roots when the constructor's label
depends on them. The solver decides the guard once per tuple of child
groups; the accepted tuples are closed with the constructor and regrouped by
the parent's observations.
-}
compileNode ::
    Compiler ->
    [Path] ->
    ([ObservationKey] -> Either GenError LiquidSymbol) ->
    Bool ->
    LiquidConstraint ->
    LTAGen a ->
    IO (Either GenError (LTAGrouped ObservationKey a))
compileNode compiler requested labelOf needsRoots constraint child
    | any isJust positions = compileIntegerNode compiler requested labelOf needsRoots constraint child positions
  where
    positions = integerPositions child
compileNode compiler requested labelOf needsRoots constraint child = do
    compiledChild <- compileSpine compiler childRequirements child
    case compiledChild of
        Left err -> pure $ Left err
        Right childGroups -> do
            retained <- filterGroupsM decide childGroups
            pure $ reposition closeObservations . nodeWithKey closeLabel <$> retained
  where
    arity = spineArity child
    roots
        | needsRoots = [path [index] | index <- [0 .. arity - 1]]
        | otherwise = []
    observed = nub $ requested <> constraintPaths constraint <> roots
    childRequirements =
        [ nub [path suffix | target <- observed, index : suffix <- [unPath target], index == childIndex]
        | childIndex <- [0 .. arity - 1]
        ]
    decide childKeys = case labelOf childKeys of
        Left err -> pure $ Left err
        Right label -> constraintDecision (compilerEntailment compiler) label constraint childKeys
    -- Only accepted tuples are closed, and their labels were computed to accept them.
    closeLabel childKeys = case labelOf childKeys of
        Right label -> label
        Left _ ->
            error
                "microcfta-generator bug in Data.CFTA.Gen.Refinement.Internal.Compile.compileNode: \
                \an accepted group lost its root observation"
    closeObservations childKeys = parentObservations requested (closeLabel childKeys) childKeys

{- | Compile one constructor with integer children.

Each integer child becomes a placeholder leaf. The other children are
compiled and decided as usual, without the parts of the guard that read an
integer child. For each accepted tuple of child groups, those parts, the
conditions of the integer children, and the exact values of the other
children that the parts name give one linear formula. Its integer points,
counted without enumeration, fill the placeholders.
-}
compileIntegerNode ::
    Compiler ->
    [Path] ->
    ([ObservationKey] -> Either GenError LiquidSymbol) ->
    Bool ->
    LiquidConstraint ->
    LTAGen a ->
    [Maybe LiquidConstraint] ->
    IO (Either GenError (LTAGrouped ObservationKey a))
compileIntegerNode compiler requested labelOf needsRoots constraint child positions
    | needsRoots || any readsInteger requested || any readsInteger equalityPaths =
        pure $ Left $ IntegerLeafRead Nothing
    | reader : _ <- filter (not . countable) integerParts = pure $ Left $ IntegerLeafRead $ Just reader
    | otherwise = do
        compiledChild <- compileSpine compiler childRequirements $ placeholderSpine child
        case compiledChild of
            Left err -> pure $ Left err
            Right childGroups -> do
                retained <- filterGroupsM decide childGroups
                pure $ do
                    groups <- retained
                    expanded <- expandGroups joint fill $ nodeWithKey closeLabel groups
                    pure $ reposition closeObservations expanded
  where
    arity = spineArity child
    integerIndices = Map.fromList $ zip [position | (position, Just _) <- zip [0 ..] positions] [0 :: Int ..]
    names = ["__microcfta_integer_" <> show index | index <- [0 .. Map.size integerIndices - 1]]
    readsInteger target = case unPath target of
        position : _ -> Map.member position integerIndices
        [] -> False
    equalityPaths = constraintPaths $ equalityConstraint $ constraintEqualities constraint
    (integerParts, finiteParts) = partition (any readsInteger . guardPaths) $ conjuncts $ constraintGuard constraint
    finiteConstraint = constraint{constraintGuard = if null finiteParts then Top else And finiteParts}
    countable (Holds targets _) = all direct targets
    countable (Satisfies target _) = direct target
    countable _ = False
    direct target = length (unPath target) == 1
    observed =
        nub $
            requested
                <> constraintPaths finiteConstraint
                <> [target | Holds targets _ <- integerParts, target <- targets, not $ readsInteger target]
    childRequirements =
        [ nub [path suffix | target <- observed, index : suffix <- [unPath target], index == childIndex]
        | childIndex <- [0 .. arity - 1]
        ]
    decide childKeys = case labelOf childKeys of
        Left err -> pure $ Left err
        Right label -> constraintDecision (compilerEntailment compiler) label finiteConstraint childKeys
    -- Only accepted tuples are closed, and their labels were computed to accept them.
    closeLabel childKeys = case labelOf childKeys of
        Right label -> label
        Left _ ->
            error
                "microcfta-generator bug in Data.CFTA.Gen.Refinement.Internal.Compile.compileIntegerNode: \
                \an accepted group lost its label"
    closeObservations childKeys = parentObservations requested (closeLabel childKeys) childKeys
    domains =
        [ substitute [(valueName, variable name)] $ integerDomain condition
        | (name, Just condition) <- zip names [position | position@(Just _) <- positions]
        ]
    joint childKeys = do
        formulas <- traverse (partFormula childKeys) integerParts
        found <- first UncountableIntegers $ points names $ foldr (.&&) true $ domains <> formulas
        pure (pointCount found, pointAt found)
    partFormula childKeys part = case part of
        Satisfies target formula -> do
            term <- termOf childKeys part target
            Right $ substitute [(valueName, term)] formula
        Holds targets formula -> do
            named <- traverse (termOf childKeys part) targets
            Right $ substitute (zip (map contractTermName [0 ..]) named) formula
        _ -> Left $ IntegerLeafRead $ Just part
    termOf childKeys part target = case unPath target of
        [position]
            | Just index <- Map.lookup position integerIndices -> Right $ variable $ names !! index
            | Just value <- exactValue =<< listToMaybe (drop position childKeys) -> Right $ literal value
        _ -> Left $ IntegerLeafRead $ Just part
    -- The user's children of the closed root are its labelled descendants
    -- through private nodes, in order, as 'surface' reads them.
    fill point (Tree.Node root children) = Tree.Node root $ snd $ mapAccumL (visit point) 0 children
    visit point position term@(Tree.Node (Label _) _) =
        ( position + 1
        , maybe term (\index -> Tree.Node (Label $ integerSymbol $ point !! index) []) $ Map.lookup position integerIndices
        )
    visit point position (Tree.Node private children) = Tree.Node private <$> mapAccumL (visit point) position children

-- | The top-level conjuncts of a guard.
conjuncts :: Guard -> [Guard]
conjuncts Top = []
conjuncts (And guards) = concatMap conjuncts guards
conjuncts guard = [guard]

-- | The integer that the root refinement of a child group fixes, if it fixes one.
exactValue :: ObservationKey -> Maybe Integer
exactValue key = do
    Observed (LiquidSymbol _ refinement) _ <- Map.lookup (path []) $ keyObservations key
    onlyPoint valueName refinement

{- | Fill the placeholders of each group with the integer points of its key.

A group whose key admits no point is dropped. The mass of a group grows with
its number of points, so the members stay uniform.
-}
expandGroups ::
    ([ObservationKey] -> Either GenError (Integer, Integer -> [Integer])) ->
    ([Integer] -> Tree.Tree (Label LiquidSymbol) -> Tree.Tree (Label LiquidSymbol)) ->
    LTAGrouped [ObservationKey] ([Integer] -> a) ->
    Either GenError (LTAGrouped [ObservationKey] a)
expandGroups _ _ (CyclicGrouped _) = Right $ Grouped $ Left UnboundedGenerator
expandGroups _ _ (Grouped (Left err)) = Right $ Grouped $ Left err
expandGroups joint fill (Grouped (Right buckets)) = do
    components <- traverse expand $ Map.toList buckets
    pure $ Grouped $ mergeComponentsByKey $ catMaybes components
  where
    expand (key, KeyedBucket mass static) = do
        (count, pointAt') <- joint key
        pure $
            if count == 0
                then Nothing
                else Just (key, mass * fromInteger count, pointsStatic fill (Indexed count pointAt') static)

-- | The integer leaf at each position of an applicative spine, with its conditions.
integerPositions :: LTAGen a -> [Maybe LiquidConstraint]
integerPositions generator = case integerLeaf generator of
    Just (constraint, _) -> [Just constraint]
    Nothing -> case genRecipe generator of
        Lifted _ -> []
        Mapped _ inner -> integerPositions inner
        Applied functions arguments -> integerPositions functions <> integerPositions arguments
        _ -> [Nothing]

-- | The conditions of an integer leaf, and the map from its integer to its value.
integerLeaf :: LTAGen a -> Maybe (LiquidConstraint, Integer -> a)
integerLeaf generator = case genRecipe generator of
    Integers constraint -> Just (constraint, id)
    Mapped transform inner -> fmap (transform .) <$> integerLeaf inner
    _ -> Nothing

{- | The child description with each integer leaf replaced by a placeholder
leaf, as a function of the integers of those leaves, in order.
-}
placeholderSpine :: LTAGen a -> LTAGen ([Integer] -> a)
placeholderSpine = fst . go 0
  where
    go :: Int -> LTAGen b -> (LTAGen ([Integer] -> b), Int)
    go next generator = case integerLeaf generator of
        Just (constraint, decode) ->
            ( node (LiquidSymbol (fromString "integers") $ integerDomain constraint) $ pure $ \integers' -> decode $ integers' !! next
            , next + 1
            )
        Nothing -> case genRecipe generator of
            Lifted value -> (pure $ const value, next)
            Mapped transform inner ->
                let (reader, after) = go next inner
                 in ((transform .) <$> reader, after)
            Applied functions arguments ->
                let (readFunctions, middle) = go next functions
                    (readArguments, after) = go middle arguments
                 in ((\function argument integers' -> function integers' $ argument integers') <$> readFunctions <*> readArguments, after)
            _ -> (const <$> generator, next)

-- | Decide one guard from the already-grouped child observations.
constraintDecision :: Entailment -> LiquidSymbol -> LiquidConstraint -> [ObservationKey] -> IO (Either GenError Bool)
constraintDecision entailment label constraint childKeys = do
    verdict <-
        evaluateGuardWithShape
            entailment
            (\target -> (\(Observed (LiquidSymbol symbol refinement) _) -> (symbol, refinement)) <$> Map.lookup target observations)
            (\target -> (\(Observed _ isLeaf) -> isLeaf) <$> Map.lookup target observations)
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
    observations = completeObservations label childKeys

-- | Sparse root observations cannot decide equality of complete subtrees.
containsSyntacticEquality :: Guard -> Bool
containsSyntacticEquality Top = False
containsSyntacticEquality Bottom = False
containsSyntacticEquality (Same _ _) = True
containsSyntacticEquality (Entails _ _) = False
containsSyntacticEquality (Satisfies _ _) = False
containsSyntacticEquality (Holds _ _) = False
containsSyntacticEquality (Substitute _ nested) = containsSyntacticEquality nested
containsSyntacticEquality (Not nested) = containsSyntacticEquality nested
containsSyntacticEquality (And guards) = any containsSyntacticEquality guards
containsSyntacticEquality (Or guards) = any containsSyntacticEquality guards

-- | The observations a parent requests above one accepted node.
parentObservations :: [Path] -> LiquidSymbol -> [ObservationKey] -> Observations
parentObservations requested label childKeys =
    Map.restrictKeys (completeObservations label childKeys) $ Set.insert (path []) $ Set.fromList requested

-- | The root plus the sparse observations retained by every direct child group.
completeObservations :: LiquidSymbol -> [ObservationKey] -> Observations
completeObservations label childKeys =
    Map.fromList $
        (path [], Observed label $ null childKeys)
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
    Entailment ->
    [Path] ->
    Maybe Int ->
    Automaton ->
    IO (Either GenError (LTAGrouped ObservationKey (Tree.Tree LiquidSymbol)))
compileImport entailment requested bound automaton
    | Just depth <- bound, depth < 0 = pure $ Right $ frequencies []
    | otherwise = do
        pruned <- prune entailment $ maybe id boundDepth bound automaton
        pure $ do
            reduced <- first pruningError pruned
            mapM_ (first ResidualGuard . constraintIndicators . edgeConstraint) $ concat $ IntMap.elems $ reachable reduced
            pure $
                uniformlyGrouped
                    [ keyed (ObservationKey position observations) $ Flat.fromAutomaton liquidOrder part
                    | (position, (observations, part)) <- zip [0 ..] $ splitByObservations requested reduced
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
            | observesRoot = Map.singleton (path []) $ Observed (LiquidSymbol symbol refinement) $ null children
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

{- | Check every candidate explicitly and keep the accepted values in order.

Every combination the recipe describes is a candidate. Each complete witness
is checked with the solver, guard by guard. An imported automaton is pruned
first and contributes its accepted terms.
-}
validOutcomes :: Entailment -> LTAGen a -> IO (Either GenError [a])
validOutcomes uncachedEntailment generator = do
    entailment <- cacheEntailment uncachedEntailment
    candidates <- candidatesOf entailment generator
    case candidates of
        Left err -> pure $ Left err
        Right members -> fmap catMaybes . sequence <$> traverse (accept entailment) members

-- | The value of an accepted candidate.
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
    Closed label constraint child -> (>>= close (const $ Right label) constraint) <$> candidatesOf entailment child
    ClosedBy labelOf constraint child -> (>>= close (labelOf . map witnessLabel) constraint) <$> candidatesOf entailment child
    Imported bound automaton -> do
        imported <- compileImport entailment [] bound automaton
        pure $ imported >>= builtCandidates . ungroup
    Integers constraint -> pure $ integerCandidates constraint
  where
    close labelOf constraint = traverse $ \(value, witnesses) -> (\label -> (value, [Witness label constraint witnesses])) <$> labelOf witnesses

{- | Every integer between the least and the greatest counted integer of a
leaf, each with a witness that checks the leaf's conditions.
-}
integerCandidates :: LiquidConstraint -> Either GenError [(Integer, [Witness])]
integerCandidates constraint = case points [valueName] (integerDomain constraint) of
    Left err -> Left $ UncountableIntegers err
    Right found
        | pointCount found == 0 -> Right []
        | otherwise ->
            Right
                [ (value, [Witness (integerSymbol value) constraint []])
                | value <- [least .. greatest]
                ]
      where
        least = head' $ pointAt found 0
        greatest = head' $ pointAt found $ pointCount found - 1
        head' point = case point of
            [value] -> value
            _ ->
                error
                    "microcfta-generator bug in Data.CFTA.Gen.Refinement.Internal.Compile.integerCandidates: a point of one variable has another dimension"

-- | The members of a built language, each with the witnesses of its term.
builtCandidates :: LTAGen a -> Either GenError [(a, [Witness])]
builtCandidates generator
    | deferred generator = Left SourceRequiresCompilation
    | otherwise = do
        total <- cardinality generator
        traverse member [0 .. total - 1]
  where
    member rank = (\value term -> (value, map termWitness $ surface term)) <$> unrank generator rank <*> termAt generator rank
