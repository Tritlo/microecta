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
    isIntegerName,
) where

import Control.Applicative ((<|>))
import Control.Exception (handle)
import Data.Bifunctor (first)
import Data.Either (fromLeft)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import qualified Data.IntMap.Strict as IntMap
import Data.List (isPrefixOf, mapAccumL, nub, sortOn)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isNothing, listToMaybe)
import Data.Ratio (denominator, numerator)
import qualified Data.Set as Set
import Data.String (fromString)
import qualified Data.Text as Text
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
    holeStatic,
    mapStatic,
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
    VarIndex (..),
    Weight (..),
    childIndexes,
    countWeight,
    everyRank,
 )
import Data.CFTA.Refinement
import Data.CFTA.Refinement.Expression (
    definingTerm,
    freeNames,
    literal,
    refinementFormula,
    substitute,
    true,
    variable,
    (.&&),
    (.==),
 )
import Data.CFTA.Refinement.Lattice (LatticeError (UnboundedVariable), Points, onlyPoint, pointAt, pointCount, points)
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

{- | What one compilation shares: the cached solver, the groups compiled so
far, and which generators contain integer leaves.
-}
data Compiler = Compiler
    { compilerEntailment :: !Entailment
    , compilerClosed :: !(Memo ClosedGroups)
    , compilerOpen :: !(Memo OpenGroups)
    , compilerIntegers :: !(Memo Contains)
    }

-- | The groups of a generator that leaves no variable open.
newtype ClosedGroups a = ClosedGroups (Either GenError (LTAGrouped ObservationKey a))

-- | The groups of a generator whose members can leave integer variables open.
newtype OpenGroups a = OpenGroups (Either GenError (LTAGrouped OpenKey ([Integer] -> a)))

-- | Whether a generator contains an integer leaf.
newtype Contains a = Contains Bool

-- | Results by the stable name of a generator and the paths requested of it.
type Memo f = IORef (IntMap.IntMap [Entry f])

{- | One result for one generator. A stable name identifies one heap object,
so the result has the type of that object.
-}
data Entry f = forall a. Entry !(StableName (LTAGen a)) ![Path] (f a)

-- | The recorded result for a generator and requested paths, or the computed one, recorded.
memoized :: Memo f -> [Path] -> LTAGen a -> IO (f a) -> IO (f a)
memoized memo requested generator compute = do
    name <- makeStableName $! generator
    known <- readIORef memo
    case [ unsafeCoerce result
         | Entry other paths result <- IntMap.findWithDefault [] (hashStableName name) known
         , eqStableName name other
         , paths == requested
         ] of
        result : _ -> pure result
        [] -> do
            result <- compute
            modifyIORef' memo $ IntMap.insertWith (<>) (hashStableName name) [Entry name requested result]
            pure result

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
        closedMemo <- newIORef IntMap.empty
        openMemo <- newIORef IntMap.empty
        integersMemo <- newIORef IntMap.empty
        fmap ungroup <$> compileGen (Compiler entailment closedMemo openMemo integersMemo) [path []] generator

-- | Compile one generator, grouped by the observations its parent needs.
compileGen :: Compiler -> [Path] -> LTAGen a -> IO (Either GenError (LTAGrouped ObservationKey a))
compileGen compiler requested generator =
    fmap (\(ClosedGroups groups) -> groups) $
        memoized (compilerClosed compiler) requested generator $
            ClosedGroups <$> do
                open <- containsIntegers compiler generator
                if open
                    then (>>= closeOpen) <$> compileOpen compiler requested generator
                    else compileGenOnce compiler requested generator

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
        ClosedBy symbolOf constraint child -> compileNode compiler requested (ComputedLabel symbolOf) constraint child
        Imported bound order automaton -> compileImport (compilerEntailment compiler) requested bound order automaton
        Integers constraint -> pure $ integerGroup constraint >>= closeOpen
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

{- | Whether a generator contains an integer leaf outside an imported
automaton. Only such a generator compiles through open groups.
-}
containsIntegers :: Compiler -> LTAGen a -> IO Bool
containsIntegers compiler generator =
    fmap (\(Contains found) -> found) $
        memoized (compilerIntegers compiler) [] generator $
            Contains <$> case genRecipe generator of
                Integers _ -> pure True
                Mapped _ inner -> containsIntegers compiler inner
                Applied functions arguments -> (||) <$> containsIntegers compiler functions <*> containsIntegers compiler arguments
                Chosen alternatives -> or <$> traverse (containsIntegers compiler . snd) alternatives
                Uniform alternatives -> or <$> traverse (containsIntegers compiler) alternatives
                Closed _ _ child -> containsIntegers compiler child
                ClosedBy _ _ child -> containsIntegers compiler child
                _ -> pure False

{- | The key of a group whose members can leave integer variables open: what
the parent observes, the number of open variables, the formula over them
that the members satisfy, and the number of its points. The variables are
named by 'integerName', and a root label that names them is a term of them.

The mass of a group is the mass of all its points, as for a group of pools:
one point has the product of the masses of the children, divided by their point
counts, and a constructor multiplies this by the share of the points that it
keeps. A pool group sums the masses of its members in the same unit.
The number of points is 'Nothing' when the conditions of an integer leaf do
not bound it and only a contract does.
-}
data OpenKey = OpenKey
    { openObservations :: !ObservationKey
    , openCount :: !Int
    , openFormula :: !Formula
    , openPoints :: !(Maybe Cardinality)
    }
    deriving (Eq, Ord, Show)

-- | The key of a group that leaves no variable open.
closedKey :: ObservationKey -> OpenKey
closedKey key = OpenKey key 0 true (Just 1)

-- | The name of one open integer variable.
integerName :: VarIndex -> String
integerName index = "__microcfta_integer_" <> show index

-- | Whether a name is the name of an open integer variable.
isIntegerName :: String -> Bool
isIntegerName = isPrefixOf "__microcfta_integer_"

{- | Compile one generator whose members can leave integer variables open.

A generator without integers compiles with 'compileGen', and its members read
no variable. An integer leaf leaves its one variable open. A constructor joins
the variables of its children, and closes them when its label names none of
them.
-}
compileOpen :: Compiler -> [Path] -> LTAGen a -> IO (Either GenError (LTAGrouped OpenKey ([Integer] -> a)))
compileOpen compiler requested generator =
    fmap (\(OpenGroups groups) -> groups) $
        memoized (compilerOpen compiler) requested generator $
            OpenGroups <$> do
                open <- containsIntegers compiler generator
                if not open
                    then fmap (regroupOn closedKey . mapWithKey (const const)) <$> compileGen compiler requested generator
                    else case genRecipe generator of
                        Integers constraint -> pure $ integerGroup constraint
                        Mapped transform inner -> fmap (mapWithKey (const (transform .))) <$> compileOpen compiler requested inner
                        Applied _ _ ->
                            fmap joinPositioned <$> compileOpenSpine compiler (replicate (fromEnum $ spineArity generator) []) generator
                        Chosen alternatives -> do
                            compiled <-
                                traverse (\(weight, alternative) -> fmap (weight,) <$> compileOpen compiler requested alternative) alternatives
                            pure $ do
                                weighted <- sequence compiled
                                -- A choice weighs the mass of each alternative, which an unbounded leaf does not have.
                                case [key | (_, grouped) <- weighted, not $ emptyGroups grouped, key <- openKeys grouped] of
                                    keys
                                        | length (filter (not . emptyGroups . snd) weighted) > 1
                                        , key : _ <- filter (isNothing . openPoints) keys ->
                                            Left $ fromLeft UnboundedGenerator $ countPoints integerLabel (openCount key) (openFormula key)
                                    _ -> Right ()
                                pure
                                    $ repositionOpen
                                    $ frequencies
                                        [ (weight, regroupOn (index,) grouped)
                                        | (index :: ChoiceIndex, (weight, grouped)) <- zip [0 ..] weighted
                                        , not $ emptyGroups grouped
                                        ]
                        Closed symbol constraint child -> compileOpenNode compiler requested (FixedLabel symbol) constraint child
                        ClosedBy symbolOf constraint child -> compileOpenNode compiler requested (ComputedLabel symbolOf) constraint child
                        _ -> pure $ Left SourceRequiresCompilation

{- | One integer leaf as an open group: one variable, which the conditions of
the leaf bound. A leaf without values is empty.
-}
integerGroup :: Constraint -> Either GenError (LTAGrouped OpenKey ([Integer] -> Integer))
integerGroup constraint = case points [valueName] domain of
    Right found | pointCount found == 0 -> Right $ Grouped $ Left EmptyGenerator
    Right found -> Right $ group $ Just $ pointCount found
    Left (UnboundedVariable _) -> Right $ group Nothing
    Left err -> Left $ UncountableIntegers err
  where
    group count =
        keyed (OpenKey (ObservationKey 0 $ Map.singleton (path []) $ Observed root Leaf) 1 bounded count)
            $ Gen Built
            $ TransparentLanguage
            $ Right
            $ holeStatic (RefinedSymbol (fromString "integers") domain) firstInteger
      where
        firstInteger point = case point of
            value : _ -> value
            [] ->
                error
                    "microcfta-generator bug in Data.CFTA.Gen.Refinement.Internal.Compile.integerGroup: \
                    \an integer leaf read an empty point"
    domain = integerDomain constraint
    root = RefinedSymbol (fromString "integers") $ refinementFormula (.== variable (integerName 0))
    bounded = substitute [(valueName, variable $ integerName 0)] domain

-- | Join the keys of each tuple of a bare spine, positioned by first appearance.
joinPositioned :: LTAGrouped [OpenKey] a -> LTAGrouped OpenKey a
joinPositioned grouped = regroupOn rekey grouped
  where
    identity keys = let joined = joinKeys keys in (openCount joined, openFormula joined)
    positions =
        Map.fromListWith (\_ earlier -> earlier) $
            zip (map identity $ either (const []) Map.keys $ sizes grouped) [0 :: Int ..]
    rekey keys =
        let joined = joinKeys keys
         in joined{openObservations = (openObservations joined){keyPosition = positions Map.! identity keys}}

    -- The key of a bare applicative spine: no observation, and the variables of its positions joined.
    joinKeys :: [OpenKey] -> OpenKey
    joinKeys keys =
        OpenKey
            noObservations
            (sum $ map openCount keys)
            (foldr (.&&) true $ renamedFormulas keys)
            (product <$> traverse openPoints keys)

{- | Count the points of a formula over the given number of open variables. On
a failure, count again with readable names for the variables, so that the
error names them.
-}
countPoints :: (VarIndex -> String) -> Int -> Formula -> Either GenError Points
countPoints nameOf count formula = case points (map integerName indexes) formula of
    Right found -> Right found
    Left err -> Left $ UncountableIntegers $ fromLeft err $ points (map nameOf indexes) readable
  where
    indexes = [0 .. VarIndex count - 1]
    readable = substitute [(integerName index, variable $ nameOf index) | index <- indexes] formula

-- | A readable name for an open variable of a group.
integerLabel :: VarIndex -> String
integerLabel index = "integer " <> show index

-- | A readable name for an open variable of a constructor: the child that holds it.
childLabel :: Symbol -> [OpenKey] -> VarIndex -> String
childLabel (RefinedSymbol (Symbol constructor) _) childKeys index =
    case [ (child, index - offset, key)
         | (child, offset, key) <- zip3 [0 :: Int ..] (offsets childKeys) childKeys
         , index >= offset
         , index < offset + VarIndex (openCount key)
         ] of
        (child, _, key) : _ | openCount key == 1 -> "child " <> show child <> " of " <> Text.unpack constructor
        (child, within, _) : _ -> "integer " <> show within <> " of child " <> show child <> " of " <> Text.unpack constructor
        [] -> integerLabel index

-- | The keys of the groups of a grouped generator.
openKeys :: LTAGrouped OpenKey a -> [OpenKey]
openKeys = either (const []) Map.keys . sizes

-- | The formula of each group of a tuple, with the variables of the tuple renamed apart.
renamedFormulas :: [OpenKey] -> [Formula]
renamedFormulas keys = [renameFrom offset key $ openFormula key | (offset, key) <- zip (offsets keys) keys]

-- | The first variable of each group of a tuple, once the variables are joined in order.
offsets :: [OpenKey] -> [VarIndex]
offsets = scanl (+) 0 . map (VarIndex . openCount)

-- | Rename the variables of one group so that they start at the given offset.
renameFrom :: VarIndex -> OpenKey -> Formula -> Formula
renameFrom offset key =
    substitute [(integerName index, variable $ integerName $ offset + index) | index <- [0 .. VarIndex (openCount key) - 1]]

-- | Regroup open groups by what the parent observes, positioned by first appearance.
repositionOpen :: LTAGrouped (ChoiceIndex, OpenKey) a -> LTAGrouped OpenKey a
repositionOpen grouped = regroupOn rekey grouped
  where
    identity (_, key) = (keyObservations $ openObservations key, openCount key, openFormula key)
    positions =
        Map.fromListWith (\_ earlier -> earlier) $
            zip (map identity $ either (const []) Map.keys $ sizes grouped) [0 :: Int ..]
    rekey indexed@(_, key) =
        key{openObservations = (openObservations key){keyPosition = positions Map.! identity indexed}}

{- | Compile a child description of open groups as one group per tuple of child
groups. The value of a tuple reads the variables of each position in turn.
-}
compileOpenSpine :: Compiler -> [[Path]] -> LTAGen a -> IO (Either GenError (LTAGrouped [OpenKey] ([Integer] -> a)))
compileOpenSpine compiler requirements generator = case genRecipe generator of
    Lifted value -> pure $ Right $ keyed [] $ pure $ const value
    Mapped transform inner -> fmap (mapWithKey (const (transform .))) <$> compileOpenSpine compiler requirements inner
    Applied functions arguments -> do
        let (functionRequirements, argumentRequirements) = splitAt (fromEnum $ spineArity functions) requirements
            applyReader keys (function, argument) =
                let split = sum $ map openCount $ take (fromEnum $ spineArity functions) keys
                 in \point -> function (take split point) (argument $ drop split point)
        compiledFunctions <- compileOpenSpine compiler functionRequirements functions
        case compiledFunctions of
            Left err -> pure $ Left err
            Right functionGroups
                | emptyGroups functionGroups -> pure $ Right $ frequencies []
                | otherwise -> do
                    compiledArguments <- compileOpenSpine compiler argumentRequirements arguments
                    case compiledArguments of
                        Left err -> pure $ Left err
                        Right argumentGroups -> do
                            related <- relateGroupsM (\_ _ -> pure $ Right True) (<>) functionGroups argumentGroups
                            pure $ mapWithKey applyReader <$> related
    _ -> fmap (regroupOn pure) <$> compileOpen compiler (concat $ take 1 requirements) generator

{- | Compile one constructor whose children can leave integer variables open.

The children are grouped as for 'compileNode'. For each tuple of child groups,
the variables of the children are renamed apart and joined. The solver decides
the parts of the guard that read no open child, as in 'compileNode'. The other
parts, the conditions of the constructor's own result, and the formulas of the
children form one linear formula over the joined variables; a child names its
value by its root label, as an exact integer or as a term of its variables.
When the constructor's label names no variable, the constructor closes them:
its members are the integer points of the formula, counted without
enumeration, and the points fill the placeholder leaves in order. Otherwise
the constructor leaves the variables open for its parent.
-}
compileOpenNode ::
    Compiler ->
    [Path] ->
    Labelling ->
    Constraint ->
    LTAGen a ->
    IO (Either GenError (LTAGrouped OpenKey ([Integer] -> a)))
compileOpenNode compiler requested labelling constraint child
    | not (all null childRequirements) && not (alignedSpine child) = pure $ Left ChildNotOneTerm
    | otherwise = do
        compiledChild <- compileOpenSpine compiler childRequirements child
        case compiledChild of
            Left err -> pure $ Left err
            Right childGroups -> do
                retained <- filterGroupsM decide childGroups
                pure $ retained >>= settleGroups settle . nodeWithKey closeLabel
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
    parts = conjuncts $ constraintGuard constraint
    open childKeys (ChildIndex index) = maybe False ((> 0) . openCount) $ listToMaybe $ drop index childKeys
    -- A parent reads only the root of a child that leaves variables open.
    readsInsideOpen childKeys target = case unPath target of
        index : _ : _ -> open childKeys index
        _ -> False
    equalityPaths = constraintPaths $ equalityConstraint $ constraintEqualities constraint
    renamedRoot childKeys (ChildIndex index) = do
        key <- listToMaybe $ drop index childKeys
        Observed (RefinedSymbol symbol refinement) _ <- Map.lookup (path []) $ keyObservations $ openObservations key
        pure $ RefinedSymbol symbol $ renameFrom (offsets childKeys !! index) key refinement
    labelOf childKeys = case labelling of
        FixedLabel label -> Right label
        ComputedLabel symbolOf ->
            traverse (maybe (Left MissingRootObservation) Right . renamedRoot childKeys) (childIndexes arity) >>= symbolOf
    symbolic (RefinedSymbol _ refinement) = any isIntegerName $ freeNames refinement
    readsOpen childKeys label part =
        flip any (guardPaths part) $ \target -> case unPath target of
            index : _ -> open childKeys index
            [] -> symbolic label
    decide childKeys
        | any (readsInsideOpen childKeys) (observed <> equalityPaths) || any (any (open childKeys) . firstIndex) equalityPaths =
            pure $ Left $ IntegerLeafRead Nothing
        | otherwise = case labelOf childKeys of
            Left err -> pure $ Left err
            Right label ->
                let finiteParts = filter (not . readsOpen childKeys label) parts
                    -- A closed child keeps the symbolic labels of its integer leaves until a point fills them.
                    readsSymbolic target = case Map.lookup target $ completeObservations label leafness $ map openObservations childKeys of
                        Just (Observed found _) -> symbolic found
                        Nothing -> False
                 in case filter (any readsSymbolic . guardPaths) finiteParts of
                        part : _ -> pure $ Left $ IntegerLeafRead $ Just part
                        []
                            | any readsSymbolic equalityPaths -> pure $ Left $ IntegerLeafRead Nothing
                            | null finiteParts && constraintEqualities constraint == EmptyConstraints -> pure $ Right True
                            | otherwise ->
                                constraintDecision
                                    (compilerEntailment compiler)
                                    label
                                    leafness
                                    constraint{constraintGuard = if null finiteParts then Top else And finiteParts}
                                    (map openObservations childKeys)
      where
        firstIndex target = take 1 $ unPath target
    -- Only accepted tuples are closed, and their labels were computed to accept them.
    closeLabel childKeys = case labelOf childKeys of
        Right label -> label
        Left _ ->
            error
                "microcfta-generator bug in Data.CFTA.Gen.Refinement.Internal.Compile.compileOpenNode: \
                \an accepted group lost its label"
    settle childKeys = do
        let label@(RefinedSymbol _ labelRefinement) = closeLabel childKeys
            total = sum $ map openCount childKeys
            termOf refinement = (literal <$> onlyPoint valueName refinement) <|> definingTerm refinement
            targetTerm part target = maybe (Left $ IntegerLeafRead $ Just part) Right $ case unPath target of
                [] -> termOf labelRefinement
                [index] -> termOf . (\(RefinedSymbol _ refinement) -> refinement) =<< renamedRoot childKeys index
                _ -> Nothing
            partFormula part = case part of
                Satisfies target formula -> (\term -> substitute [(valueName, term)] formula) <$> targetTerm part target
                Holds targets formula -> (\named -> substitute (zip (map contractTermName [0 ..]) named) formula) <$> traverse (targetTerm part) targets
                _ -> Left $ IntegerLeafRead $ Just part
        openFormulas <- traverse partFormula $ filter (readsOpen childKeys label) parts
        let formula = foldr (.&&) true $ renamedFormulas childKeys <> openFormulas
            observations = ObservationKey 0 $ parentObservations requested label leafness $ map openObservations childKeys
        found <- countPoints (childLabel label childKeys) total formula
        -- The share of the points of the children that the constructor keeps. An unbounded leaf is common to all tuples.
        let kept = toRational (pointCount found) / toRational (product $ map (fromMaybe 1 . openPoints) childKeys)
        pure $
            if pointCount found == 0
                then Nothing
                else
                    if symbolic label
                        then Just (OpenKey observations total formula (Just $ pointCount found), kept, Nothing)
                        else Just (closedKey observations, kept, Just (pointCount found, pointAt found))

{- | Settle each tuple of child groups: drop it, leave its variables open under
a new key, or close them by the integer points of its formula. The mass of a
tuple keeps the share of its points that the constructor keeps, as a guard
keeps the accepted tuples of pools. New keys are positioned by first
appearance.
-}
settleGroups ::
    ([OpenKey] -> Either GenError (Maybe (OpenKey, Rational, Maybe (Cardinality, Rank -> [Integer])))) ->
    LTAGrouped [OpenKey] ([Integer] -> a) ->
    Either GenError (LTAGrouped OpenKey ([Integer] -> a))
settleGroups _ (CyclicGrouped _) = Right $ Grouped $ Left UnboundedGenerator
settleGroups _ (Grouped (Left err)) = Right $ Grouped $ Left err
settleGroups settle (Grouped (Right buckets)) = do
    settled <- catMaybes <$> traverse one (Map.toAscList buckets)
    let identity key = (keyObservations $ openObservations key, openCount key, openFormula key)
        positions = Map.fromListWith (\_ earlier -> earlier) $ zip [identity key | (key, _, _) <- settled] [0 :: Int ..]
        positioned key = key{openObservations = (openObservations key){keyPosition = positions Map.! identity key}}
    pure $ Grouped $ mergeComponentsByKey [(positioned key, mass, static) | (key, mass, static) <- settled]
  where
    one (childKeys, KeyedBucket mass static) = fmap (build mass static) <$> settle childKeys
    build mass static (key, kept, Nothing) = (key, mass * kept, static)
    build mass static (key, kept, Just (count, decode)) =
        (key, mass * kept, mapStatic const $ pointsStatic fillHoles (Indexed count decode) static)

{- | Close every open group by the integer points of its formula, for a parent
that reads no variable.
-}
closeOpen :: LTAGrouped OpenKey ([Integer] -> a) -> Either GenError (LTAGrouped ObservationKey a)
closeOpen (CyclicGrouped _) = Right $ Grouped $ Left UnboundedGenerator
closeOpen (Grouped (Left err)) = Right $ Grouped $ Left err
closeOpen (Grouped (Right buckets)) = do
    closed <- catMaybes <$> traverse one (Map.toAscList buckets)
    pure $ Grouped $ mergeComponentsByKey closed
  where
    one (key, KeyedBucket mass static)
        | openCount key == 0 = Right $ Just (openObservations key, mass, mapStatic ($ []) static)
        | otherwise = do
            found <- countPoints integerLabel (openCount key) (openFormula key)
            pure $
                if pointCount found == 0
                    then Nothing
                    else Just (openObservations key, mass, pointsStatic fillHoles (Indexed (pointCount found) (pointAt found)) static)

{- | Replace the placeholder leaves of a term, in order, by the leaves of the
integers of a point, and make each label that names open variables exact.

The variables of a constructor are the placeholders of its subtree, in
order, so a label names them from the first placeholder below it.
-}
fillHoles :: [Integer] -> Tree.Tree (Label Symbol) -> Tree.Tree (Label Symbol)
fillHoles point = snd . fill point
  where
    fill (value : rest) (Tree.Node Placeholder _) = (rest, Tree.Node (Label $ integerSymbol value) [])
    fill remaining (Tree.Node (Label label) children) = Tree.Node (Label $ exactLabel remaining label) <$> mapAccumL fill remaining children
    fill remaining (Tree.Node private children) = Tree.Node private <$> mapAccumL fill remaining children
    exactLabel remaining label@(RefinedSymbol symbol refinement)
        | any isIntegerName $ freeNames refinement =
            let named = substitute [(integerName index, literal value) | (index, value) <- zip [0 ..] remaining] refinement
             in RefinedSymbol symbol $ maybe named (\value -> refinementFormula (.== literal value)) $ onlyPoint valueName named
        | otherwise = label

-- | The top-level conjuncts of a guard.
conjuncts :: Guard -> [Guard]
conjuncts Top = []
conjuncts (And guards) = concatMap conjuncts guards
conjuncts guard = [guard]

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
    Closed label constraint child -> (>>= close (const $ Right label) constraint) <$> candidatesOf entailment child
    ClosedBy labelOf constraint child -> (>>= close (labelOf . map witnessLabel) constraint) <$> candidatesOf entailment child
    Imported bound order automaton -> do
        imported <- compileImport entailment [] bound order automaton
        pure $ imported >>= builtCandidates . ungroup
    Integers constraint -> pure $ integerCandidates constraint
  where
    close labelOf constraint = traverse $ \(value, witnesses) -> (\label -> (value, [Witness label constraint witnesses])) <$> labelOf witnesses

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
    | Left EmptyGenerator <- cardinality generator = Right []
    | otherwise = do
        total <- cardinality generator
        traverse member $ everyRank total
  where
    member rank = (\value term -> (value, map termWitness $ surface term)) <$> unrank generator rank <*> termAt generator rank
