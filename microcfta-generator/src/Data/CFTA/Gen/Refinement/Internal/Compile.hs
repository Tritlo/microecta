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
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import qualified Data.IntMap.Strict as IntMap
import Data.List (mapAccumL, nub, partition, sortOn)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, isJust, listToMaybe)
import Data.Ratio (denominator, numerator)
import qualified Data.Set as Set
import Data.String (fromString)
import qualified Data.Tree as Tree
import System.Mem.StableName (StableName, eqStableName, hashStableName, makeStableName)
import Unsafe.Coerce (unsafeCoerce)

import Data.CFTA.Equality.Constraint (EqConstraints (EmptyConstraints))
import Data.CFTA.Gen
import Data.CFTA.Gen.Internal.Bucket (KeyedBucket (..), mergeComponentsByKey)
import qualified Data.CFTA.Gen.Internal.Flat as Flat
import Data.CFTA.Gen.Internal.Grouped (groupKeys)
import Data.CFTA.Gen.Internal.Static (
    Outcome (outcomeMass),
    OutcomeIndex (outcomeSelect),
    RootCount (..),
    Static (staticOutcomes, staticRootCount),
    addRootCounts,
    commonRootCount,
    labelledLeavesStatic,
    pointsStatic,
 )
import Data.CFTA.Gen.Internal.Types (Gen (..), Grouped (..), Language (..), Recipe (..))
import Data.CFTA.Gen.Label (ChoiceIndex)
import Data.CFTA.Gen.Refinement.Internal.Witness
import Data.CFTA.Index (
    Arity (..),
    Cardinality (..),
    Depth (..),
    Rank (..),
    Weight (..),
    childIndexes,
    countWeight,
    everyRank,
 )
import Data.CFTA.Refinement
import Data.CFTA.Refinement.Expression (literal, refinementFormula, substitute, true, variable, (.&&), (.==))
import Data.CFTA.Refinement.Lattice (pointAt, pointCount, points)
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
    _ -> rootCount generator == RootCount 1

-- | The 'rootCount' of each position of an applicative spine, as 'spineArity' counts the positions.
spineRootCounts :: Gen symbol a -> [RootCount]
spineRootCounts generator = case genRecipe generator of
    Lifted _ -> []
    Mapped _ inner -> spineRootCounts inner
    Applied functions arguments -> spineRootCounts functions <> spineRootCounts arguments
    _ -> [rootCount generator]

{- | The number of children that each member of a generator gives its
constructor, when all members give the same number. The children are the
roots that 'surface' gives for the term of the member, and 'validOutcomes'
reads the same children.

A constructor, an import, and an integer leaf give one child, and @pure@
gives none. A choice removes its own wrapper, so a choice of products gives
several children, and a choice of @pure@ values gives none. A built language
gives the number that its members give, which 'staticRootCount' keeps: a
source without symbols, such as 'fromIndexed' and the pools of @freeze@ and
@samplePool@, gives none, and a join gives one for each side. A language
without members gives one, so that it does not refuse a guard. The result is
'NoCommonCount' when two members give different numbers, and for a recursive
or opaque built language, whose number is not known.
-}
rootCount :: Gen symbol a -> RootCount
rootCount generator = case genRecipe generator of
    Lifted _ -> RootCount 0
    Mapped _ inner -> rootCount inner
    Applied functions arguments -> addRootCounts (rootCount functions) (rootCount arguments)
    Chosen alternatives -> commonRootCount $ map (rootCount . snd) alternatives
    Uniform alternatives -> commonRootCount $ map rootCount alternatives
    Closed{} -> RootCount 1
    ClosedBy{} -> RootCount 1
    Imported{} -> RootCount 1
    Integers _ -> RootCount 1
    Built -> case genLanguage generator of
        TransparentLanguage (Right static) -> staticRootCount static
        TransparentLanguage (Left _) -> RootCount 1
        CyclicLanguage (Left _) -> RootCount 1
        _ -> NoCommonCount

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
        Applied _ _
            -- A product whose one term comes from one part, such as @elements [2] <* pure ()@,
            -- answers the requested paths of that part. Another product observes nothing.
            | not (null requested)
            , counts <- spineRootCounts generator
            , all (`elem` [RootCount 0, RootCount 1]) counts
            , [position] <- [index | (index, RootCount 1) <- zip [0 ..] counts] ->
                fmap (regroupOn (!! position))
                    <$> compileSpine compiler [if index == position then requested else [] | index <- [0 .. length counts - 1]] generator
            | otherwise ->
                fmap (regroupOn (const noObservations))
                    <$> compileSpine compiler (replicate (fromEnum $ spineArity generator) []) generator
        Chosen alternatives -> do
            compiled <- traverse (compileGen compiler requested . snd) alternatives
            pure $ choose (map fst alternatives) <$> sequence compiled
        Uniform alternatives -> do
            compiled <- traverse (compileGen compiler requested) alternatives
            pure $ (\groups -> choose (uniformWeights groups) groups) <$> sequence compiled
        Closed symbol constraint child -> compileNode compiler requested (FixedLabel symbol) constraint child
        ClosedBy symbolOf constraint child -> compileNode compiler requested (ComputedLabel (Right . symbolOf)) constraint child
        Imported bound order automaton -> compileImport (compilerEntailment compiler) requested bound order automaton
        Integers constraint -> pure $ compileIntegers constraint
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

{- | Count the integers that the conditions of an integer leaf admit.

The group carries no observation, so a guard cannot read the leaf as one
refinement. Each member is a leaf refined as its integer.
-}
compileIntegers :: Constraint -> Either GenError (LTAGrouped ObservationKey Integer)
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
                    (RefinedSymbol (fromString "integers") $ integerDomain constraint)
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
integerSymbol :: Integer -> Symbol
integerSymbol value = RefinedSymbol (fromString $ show value) $ refinementFormula (.== literal value)

-- | The conjunction of the conditions on an integer leaf.
integerDomain :: Constraint -> Formula
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

{- | Group a language the engine built by the requested observations.

Without observations the language is one group, and so is a language whose
members have no root, such as 'fromIndexed'. With observations every member
is read back with its term; a member's term is the user's part of the
engine's labelled term.
-}
groupBuilt :: [Path] -> LTAGen a -> Either GenError (LTAGrouped ObservationKey a)
groupBuilt requested generator
    | deferred generator = Left SourceRequiresCompilation
    | null requested = Right $ keyed noObservations generator
    -- A member without a root has no observation, so all members form one group.
    | rootCount generator == RootCount 0 = Right $ keyed noObservations generator
    | Left EmptyGenerator <- cardinality generator = Right $ frequencies []
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
compileSpine :: Compiler -> [[Path]] -> LTAGen a -> IO (Either GenError (LTAGrouped [ObservationKey] a))
compileSpine compiler requirements generator = case genRecipe generator of
    Lifted value -> pure $ Right $ keyed [] $ pure value
    Mapped transform inner -> fmap (mapWithKey (const transform)) <$> compileSpine compiler requirements inner
    Applied functions arguments -> do
        let (functionRequirements, argumentRequirements) = splitAt (fromEnum $ spineArity functions) requirements
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
    _ -> fmap (regroupOn pure) <$> compileGen compiler (concat $ take 1 requirements) generator

{- | How a constructor gets its label: a fixed label, or a label that a
function computes from the root labels of the children.
-}
data Labelling
    = FixedLabel !Symbol
    | ComputedLabel ([Symbol] -> Either GenError Symbol)

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
    Labelling ->
    Constraint ->
    LTAGen a ->
    IO (Either GenError (LTAGrouped ObservationKey a))
compileNode compiler requested labelling constraint child
    | any isJust positions = compileIntegerNode compiler requested labelling constraint child positions
  where
    positions = integerPositions child
compileNode compiler requested labelling constraint child
    | not (all null childRequirements) && not (alignedSpine child) = pure $ Left ChildNotOneTerm
    | otherwise = do
        compiledChild <- compileSpine compiler childRequirements child
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
        RootCount 0 -> Leaf
        RootCount _ -> Inner
        NoCommonCount -> Mixed
    observed = nub $ requested <> constraintPaths constraint <> roots
      where
        roots = case labelling of
            FixedLabel _ -> []
            ComputedLabel _ -> [path [index] | index <- childIndexes arity]
    childRequirements =
        [ nub [path suffix | target <- observed, index : suffix <- [unPath target], index == childIndex]
        | childIndex <- childIndexes arity
        ]
    labelOf childKeys = case labelling of
        FixedLabel label -> Right label
        ComputedLabel symbolOf -> traverse rootOf childKeys >>= symbolOf
    -- The root label retained by a group, which a computed label needs.
    rootOf :: ObservationKey -> Either GenError Symbol
    rootOf key =
        maybe (Left MissingRootObservation) (\(Observed label _) -> Right label) $ Map.lookup (path []) $ keyObservations key
    decide childKeys = case labelOf childKeys of
        Left err -> pure $ Left err
        Right label -> constraintDecision (compilerEntailment compiler) label leafness constraint childKeys
    -- Only accepted tuples are closed, and their labels were computed to accept them.
    closeLabel childKeys = case labelOf childKeys of
        Right label -> label
        Left _ ->
            error
                "microcfta-generator bug in Data.CFTA.Gen.Refinement.Internal.Compile.compileNode: \
                \an accepted group lost its root observation"
    closeObservations childKeys = parentObservations requested (closeLabel childKeys) leafness childKeys

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
    Labelling ->
    Constraint ->
    LTAGen a ->
    [Maybe Constraint] ->
    IO (Either GenError (LTAGrouped ObservationKey a))
compileIntegerNode compiler requested labelling constraint child positions
    | not (all null childRequirements) && not (alignedSpine child) = pure $ Left ChildNotOneTerm
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
    -- The term of the constructor is a leaf when its child description gives no
    -- term. When 'rootCount' gives no number, the leafness is 'Mixed', which an
    -- observer reads as not known.
    leafness = case rootCount child of
        RootCount 0 -> Leaf
        RootCount _ -> Inner
        NoCommonCount -> Mixed
    needsRoots = case labelling of
        FixedLabel _ -> False
        ComputedLabel _ -> True
    labelOf childKeys = case labelling of
        FixedLabel label -> Right label
        ComputedLabel symbolOf -> traverse rootOf childKeys >>= symbolOf
    -- The root label retained by a group, which a computed label needs.
    rootOf :: ObservationKey -> Either GenError Symbol
    rootOf key =
        maybe (Left MissingRootObservation) (\(Observed label _) -> Right label) $ Map.lookup (path []) $ keyObservations key
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
    childRequirements =
        [ nub [path suffix | target <- observed, index : suffix <- [unPath target], index == childIndex]
        | childIndex <- childIndexes arity
        ]
      where
        arity = spineArity child

        observed =
            nub $
                requested
                    <> constraintPaths finiteConstraint
                    <> [target | Holds targets _ <- integerParts, target <- targets, not $ readsInteger target]
    decide childKeys = case labelOf childKeys of
        Left err -> pure $ Left err
        Right label -> constraintDecision (compilerEntailment compiler) label leafness finiteConstraint childKeys
    -- Only accepted tuples are closed, and their labels were computed to accept them.
    closeLabel childKeys = case labelOf childKeys of
        Right label -> label
        Left _ ->
            error
                "microcfta-generator bug in Data.CFTA.Gen.Refinement.Internal.Compile.compileIntegerNode: \
                \an accepted group lost its label"
    closeObservations childKeys = parentObservations requested (closeLabel childKeys) leafness childKeys
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
            | Just value <- exactValue =<< listToMaybe (drop (fromEnum position) childKeys) -> Right $ literal value
        _ -> Left $ IntegerLeafRead $ Just part
      where
        -- The integer that the root refinement of a child group fixes, if it fixes one.
        exactValue :: ObservationKey -> Maybe Integer
        exactValue key = do
            Observed (RefinedSymbol _ refinement) _ <- Map.lookup (path []) $ keyObservations key
            found <- either (const Nothing) Just $ points [valueName] refinement
            if pointCount found == 1
                then case pointAt found 0 of
                    [value] -> Just value
                    _ -> Nothing
                else Nothing
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

{- | Fill the placeholders of each group with the integer points of its key.

A group whose key admits no point is dropped. The mass of a group grows with
its number of points, so the members stay uniform.
-}
expandGroups ::
    ([ObservationKey] -> Either GenError (Cardinality, Rank -> [Integer])) ->
    ([Integer] -> Tree.Tree (Label Symbol) -> Tree.Tree (Label Symbol)) ->
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
                else Just (key, mass * toRational count, pointsStatic fill (Indexed count pointAt') static)

-- | The integer leaf at each position of an applicative spine, with its conditions.
integerPositions :: LTAGen a -> [Maybe Constraint]
integerPositions generator = case integerLeaf generator of
    Just (constraint, _) -> [Just constraint]
    Nothing -> case genRecipe generator of
        Lifted _ -> []
        Mapped _ inner -> integerPositions inner
        Applied functions arguments -> integerPositions functions <> integerPositions arguments
        _ -> [Nothing]

-- | The conditions of an integer leaf, and the map from its integer to its value.
integerLeaf :: LTAGen a -> Maybe (Constraint, Integer -> a)
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
            ( node (RefinedSymbol (fromString "integers") $ integerDomain constraint) $ pure $ \integers' -> decode $ integers' !! next
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
    Integers constraint -> pure $ integerCandidates constraint
  where
    close labelOf constraint = map $ \(value, witnesses) -> (value, [Witness (labelOf witnesses) constraint witnesses])

{- | Every integer between the least and the greatest counted integer of a
leaf, each with a witness that checks the leaf's conditions.
-}
integerCandidates :: Constraint -> Either GenError [(Integer, [Witness])]
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
        greatest = let Cardinality count = pointCount found in head' $ pointAt found $ Rank $ count - 1
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
        traverse member $ everyRank total
  where
    member rank = (\value term -> (value, map termWitness $ surface term)) <$> unrank generator rank <*> termAt generator rank
