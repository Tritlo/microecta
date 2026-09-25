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

import Control.Applicative ((<|>))
import Control.Monad ((<=<))
import Data.Bifunctor (first)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import qualified Data.IntMap.Strict as IntMap
import Data.List (isPrefixOf, mapAccumL, nub)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, listToMaybe)
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
import Data.CFTA.Gen.Internal.Static (holeStatic, mapStatic, pointsStatic)
import Data.CFTA.Gen.Internal.Types (Gen (..), Grouped (..), Language (..), Recipe (..))
import Data.CFTA.Gen.Refinement.Internal.Witness
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
        Integers constraint -> pure $ closeOpen $ integerGroup constraint

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
                Closed _ _ child -> containsIntegers compiler child
                ClosedBy _ _ child -> containsIntegers compiler child
                _ -> pure False

{- | The key of a group whose members can leave integer variables open: what
the parent observes, the number of open variables, and the formula over them
that the members satisfy. The variables are named by 'integerName', and a
root label that names them is a term of them.
-}
data OpenKey = OpenKey
    { openObservations :: !ObservationKey
    , openCount :: !Int
    , openFormula :: !Formula
    }
    deriving (Eq, Ord, Show)

-- | The key of a group that leaves no variable open.
closedKey :: ObservationKey -> OpenKey
closedKey key = OpenKey key 0 true

-- | The name of one open integer variable.
integerName :: Int -> String
integerName index = "__microcfta_integer_" <> show index

-- | Whether a name is the name of an open integer variable.
isIntegerName :: String -> Bool
isIntegerName = isPrefixOf "__microcfta_integer_"

{- | Compile one generator whose members can leave integer variables open.

A generator without integers compiles as before, and its members read no
variable. An integer leaf leaves its one variable open. A constructor joins
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
                    then fmap (regroupBy closedKey . mapWithKey (const const)) <$> compileGen compiler requested generator
                    else case genRecipe generator of
                        Integers constraint -> pure $ Right $ integerGroup constraint
                        Mapped transform inner -> fmap (mapWithKey (const (transform .))) <$> compileOpen compiler requested inner
                        Applied _ _ ->
                            fmap (regroupBy joinKeys) <$> compileOpenSpine compiler (replicate (spineArity generator) []) generator
                        Chosen alternatives -> do
                            compiled <-
                                traverse (\(weight, alternative) -> fmap (weight,) <$> compileOpen compiler requested alternative) alternatives
                            pure $ do
                                weighted <- sequence compiled
                                pure
                                    $ repositionOpen
                                    $ frequencies
                                        [ (weight, regroupBy (index,) grouped)
                                        | (index :: Int, (weight, grouped)) <- zip [0 ..] weighted
                                        , not $ emptyGroups grouped
                                        ]
                        Closed symbol constraint child -> compileOpenNode compiler requested (Left symbol) constraint child
                        ClosedBy symbolOf constraint child -> compileOpenNode compiler requested (Right symbolOf) constraint child
                        _ -> pure $ Left SourceRequiresCompilation

-- | One integer leaf as an open group: one variable, which the conditions of the leaf bound.
integerGroup :: LiquidConstraint -> LTAGrouped OpenKey ([Integer] -> Integer)
integerGroup constraint =
    keyed (OpenKey (ObservationKey 0 $ Map.singleton (path []) $ Observed root True) 1 bounded)
        $ Gen Built
        $ TransparentLanguage
        $ Right
        $ holeStatic (LiquidSymbol (fromString "integers") domain) firstInteger
  where
    domain = integerDomain constraint
    root = LiquidSymbol (fromString "integers") $ refinementFormula (.== variable (integerName 0))
    bounded = substitute [(valueName, variable $ integerName 0)] domain
    firstInteger point = case point of
        value : _ -> value
        [] ->
            error
                "microcfta-generator bug in Data.CFTA.Gen.Refinement.Internal.Compile.integerGroup: \
                \an integer leaf read an empty point"

-- | The key of a bare applicative spine: no observation, and the variables of its positions joined.
joinKeys :: [OpenKey] -> OpenKey
joinKeys keys = OpenKey noObservations (sum $ map openCount keys) (foldr (.&&) true $ renamedFormulas keys)

-- | The formula of each group of a tuple, with the variables of the tuple renamed apart.
renamedFormulas :: [OpenKey] -> [Formula]
renamedFormulas keys = [renameFrom offset key $ openFormula key | (offset, key) <- zip (offsets keys) keys]

-- | The first variable of each group of a tuple, once the variables are joined in order.
offsets :: [OpenKey] -> [Int]
offsets = scanl (+) 0 . map openCount

-- | Rename the variables of one group so that they start at the given offset.
renameFrom :: Int -> OpenKey -> Formula -> Formula
renameFrom offset key =
    substitute [(integerName index, variable $ integerName $ offset + index) | index <- [0 .. openCount key - 1]]

-- | Regroup open groups by what the parent observes, positioned by first appearance.
repositionOpen :: LTAGrouped (Int, OpenKey) a -> LTAGrouped OpenKey a
repositionOpen grouped = regroupBy rekey grouped
  where
    identity (_, OpenKey key count formula) = (keyObservations key, count, formula)
    positions =
        Map.fromListWith (\_ earlier -> earlier) $
            zip (map identity $ either (const []) Map.keys $ sizes grouped) [0 :: Int ..]
    rekey indexed@(_, OpenKey key count formula) =
        OpenKey key{keyPosition = positions Map.! identity indexed} count formula

{- | Compile a child description of open groups as one group per tuple of child
groups. The value of a tuple reads the variables of each position in turn.
-}
compileOpenSpine :: Compiler -> [[Path]] -> LTAGen a -> IO (Either GenError (LTAGrouped [OpenKey] ([Integer] -> a)))
compileOpenSpine compiler requirements generator = case genRecipe generator of
    Lifted value -> pure $ Right $ keyed [] $ pure $ const value
    Mapped transform inner -> fmap (mapWithKey (const (transform .))) <$> compileOpenSpine compiler requirements inner
    Applied functions arguments -> do
        let (functionRequirements, argumentRequirements) = splitAt (spineArity functions) requirements
            applyReader keys (function, argument) =
                let split = sum $ map openCount $ take (spineArity functions) keys
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
    _ -> fmap (regroupBy pure) <$> compileOpen compiler (concat $ take 1 requirements) generator

{- | Compile one constructor whose children can leave integer variables open.

The children are grouped as for 'compileNode'. For each tuple of child
groups, the variables of the children are renamed apart and joined. The solver
decides the parts of the guard that read no open child, as before. The other
parts, the conditions of the constructor's own result, and the formulas of
the children form one linear formula over the joined variables; a child names
its value by its root label, as an exact integer or as a term of its
variables. When the constructor's label names no variable, the constructor
closes them: its members are the integer points of the formula, counted
without enumeration, and the points fill the placeholder leaves in order.
Otherwise the constructor leaves the variables open for its parent.
-}
compileOpenNode ::
    Compiler ->
    [Path] ->
    Either LiquidSymbol ([LiquidSymbol] -> Either GenError LiquidSymbol) ->
    LiquidConstraint ->
    LTAGen a ->
    IO (Either GenError (LTAGrouped OpenKey ([Integer] -> a)))
compileOpenNode compiler requested labelling constraint child = do
    compiledChild <- compileOpenSpine compiler childRequirements child
    case compiledChild of
        Left err -> pure $ Left err
        Right childGroups -> do
            retained <- filterGroupsM decide childGroups
            pure $ retained >>= settleGroups settle . nodeWithKey closeLabel
  where
    arity = spineArity child
    roots = case labelling of
        Left _ -> []
        Right _ -> [path [index] | index <- [0 .. arity - 1]]
    observed = nub $ requested <> constraintPaths constraint <> roots
    childRequirements =
        [ nub [path suffix | target <- observed, index : suffix <- [unPath target], index == childIndex]
        | childIndex <- [0 .. arity - 1]
        ]
    parts = conjuncts $ constraintGuard constraint
    open childKeys index = maybe False ((> 0) . openCount) $ listToMaybe $ drop index childKeys
    -- A parent reads only the root of a child that leaves variables open.
    readsInsideOpen childKeys target = case unPath target of
        index : _ : _ -> open childKeys index
        _ -> False
    equalityPaths = constraintPaths $ equalityConstraint $ constraintEqualities constraint
    renamedRoot childKeys index = do
        key <- listToMaybe $ drop index childKeys
        Observed (LiquidSymbol symbol refinement) _ <- Map.lookup (path []) $ keyObservations $ openObservations key
        pure $ LiquidSymbol symbol $ renameFrom (offsets childKeys !! index) key refinement
    labelOf childKeys = case labelling of
        Left fixed -> Right fixed
        Right symbolOf ->
            traverse (maybe (Left MissingRootObservation) Right . renamedRoot childKeys) [0 .. arity - 1] >>= symbolOf
    symbolic (LiquidSymbol _ refinement) = any isIntegerName $ freeNames refinement
    readsOpen childKeys label part =
        flip any (guardPaths part) $ \target -> case unPath target of
            index : _ -> open childKeys index
            [] -> symbolic label
    decide childKeys
        | any (readsInsideOpen childKeys) (observed <> equalityPaths) || any (any (open childKeys) . firstIndex) equalityPaths =
            pure $ Left $ IntegerLeafRead Nothing
        | otherwise = case labelOf childKeys of
            Left err -> pure $ Left err
            Right label -> case filter (not . readsOpen childKeys label) parts of
                [] | constraintEqualities constraint == EmptyConstraints -> pure $ Right True
                finiteParts ->
                    constraintDecision
                        (compilerEntailment compiler)
                        label
                        constraint{constraintGuard = if null finiteParts then Top else And finiteParts}
                        (map openObservations childKeys)
    firstIndex target = take 1 $ unPath target
    -- Only accepted tuples are closed, and their labels were computed to accept them.
    closeLabel childKeys = case labelOf childKeys of
        Right label -> label
        Left _ ->
            error
                "microcfta-generator bug in Data.CFTA.Gen.Refinement.Internal.Compile.compileOpenNode: \
                \an accepted group lost its label"
    settle childKeys = do
        let label@(LiquidSymbol _ labelRefinement) = closeLabel childKeys
            total = sum $ map openCount childKeys
            termOf refinement = (literal <$> onlyPoint valueName refinement) <|> definingTerm refinement
            targetTerm part target = maybe (Left $ IntegerLeafRead $ Just part) Right $ case unPath target of
                [] -> termOf labelRefinement
                [index] -> termOf . (\(LiquidSymbol _ refinement) -> refinement) =<< renamedRoot childKeys index
                _ -> Nothing
            partFormula part = case part of
                Satisfies target formula -> (\term -> substitute [(valueName, term)] formula) <$> targetTerm part target
                Holds targets formula -> (\named -> substitute (zip (map contractTermName [0 ..]) named) formula) <$> traverse (targetTerm part) targets
                _ -> Left $ IntegerLeafRead $ Just part
        openFormulas <- traverse partFormula $ filter (readsOpen childKeys label) parts
        let formula = foldr (.&&) true $ renamedFormulas childKeys <> openFormulas
            observations = ObservationKey 0 $ parentObservations requested label $ map openObservations childKeys
        found <- first UncountableIntegers $ points (map integerName [0 .. total - 1]) formula
        pure $
            if pointCount found == 0
                then Nothing
                else
                    if symbolic label
                        then Just (OpenKey observations total formula, Nothing)
                        else Just (closedKey observations, Just (pointCount found, pointAt found))

{- | Settle each tuple of child groups: drop it, leave its variables open under
a new key, or close them by the integer points of its formula. Closing grows
the mass of a group with its number of points, so the members stay uniform.
New keys are positioned by first appearance.
-}
settleGroups ::
    ([OpenKey] -> Either GenError (Maybe (OpenKey, Maybe (Integer, Integer -> [Integer])))) ->
    LTAGrouped [OpenKey] ([Integer] -> a) ->
    Either GenError (LTAGrouped OpenKey ([Integer] -> a))
settleGroups _ (CyclicGrouped _) = Right $ Grouped $ Left UnboundedGenerator
settleGroups _ (Grouped (Left err)) = Right $ Grouped $ Left err
settleGroups settle (Grouped (Right buckets)) = do
    settled <- catMaybes <$> traverse one (Map.toAscList buckets)
    let identity (OpenKey key count formula) = (keyObservations key, count, formula)
        positions = Map.fromListWith (\_ earlier -> earlier) $ zip [identity key | (key, _, _) <- settled] [0 :: Int ..]
        positioned key@(OpenKey observations count formula) =
            OpenKey observations{keyPosition = positions Map.! identity key} count formula
    pure $ Grouped $ mergeComponentsByKey [(positioned key, mass, static) | (key, mass, static) <- settled]
  where
    one (childKeys, KeyedBucket mass static) = fmap (build mass static) <$> settle childKeys
    build mass static (key, Nothing) = (key, mass, static)
    build mass static (key, Just (count, decode)) =
        (key, mass * fromInteger count, mapStatic const $ pointsStatic fillHoles (Indexed count decode) static)

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
    one (OpenKey key count formula, KeyedBucket mass static)
        | count == 0 = Right $ Just (key, mass, mapStatic ($ []) static)
        | otherwise = do
            found <- first UncountableIntegers $ points (map integerName [0 .. count - 1]) formula
            pure $
                if pointCount found == 0
                    then Nothing
                    else
                        Just
                            (key, mass * fromInteger (pointCount found), pointsStatic fillHoles (Indexed (pointCount found) (pointAt found)) static)

{- | Replace the placeholder leaves of a term, in order, by the leaves of the
integers of a point, and make each label that names open variables exact.

The variables of a constructor are the placeholders of its subtree, in
order, so a label names them from the first placeholder below it.
-}
fillHoles :: [Integer] -> Tree.Tree (Label LiquidSymbol) -> Tree.Tree (Label LiquidSymbol)
fillHoles point = snd . fill point
  where
    fill (value : rest) (Tree.Node Placeholder _) = (rest, Tree.Node (Label $ integerSymbol value) [])
    fill remaining (Tree.Node (Label label) children) = Tree.Node (Label $ exactLabel remaining label) <$> mapAccumL fill remaining children
    fill remaining (Tree.Node private children) = Tree.Node private <$> mapAccumL fill remaining children
    exactLabel remaining label@(LiquidSymbol symbol refinement)
        | any isIntegerName $ freeNames refinement =
            let named = substitute [(integerName index, literal value) | (index, value) <- zip [0 ..] remaining] refinement
             in LiquidSymbol symbol $ maybe named (\value -> refinementFormula (.== literal value)) $ onlyPoint valueName named
        | otherwise = label

-- | The top-level conjuncts of a guard.
conjuncts :: Guard -> [Guard]
conjuncts Top = []
conjuncts (And guards) = concatMap conjuncts guards
conjuncts guard = [guard]

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
    | Left EmptyGenerator <- cardinality generator = Right []
    | otherwise = do
        total <- cardinality generator
        traverse member [0 .. total - 1]
  where
    member rank = (\value term -> (value, map termWitness $ surface term)) <$> unrank generator rank <*> termAt generator rank
