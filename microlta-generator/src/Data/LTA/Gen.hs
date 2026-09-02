{- | Finite generators whose support is a liquid tree automaton.

'pool' supplies refined atoms. 'node' adds one constructor around an
applicatively-built child forest; "Data.LTA.Gen.Do" provides the corresponding
qualified-do syntax. 'compile' checks guards and refinement-shrink relations
once, then returns pure sampling, replay, and shrinking.
-}
module Data.LTA.Gen (
    LTAGen,
    Compiled,
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
    unary,
    binary,
    frequency,
    oneof,
    fromAutomatonUpToDepth,

    -- * Compilation and inspection
    support,
    validOutcomes,
    compile,
    compileAutomaton,
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

import Data.LTA
import Data.LTA.Guard (GuardBuilder, buildGuard)
import Data.LTA.Refinement (true)
import qualified Data.Tree.Gen as Tree

{- | A finite weighted language paired with guarded witness trees and shrinks.

The outcome language is an indexed rank plan. Applicative composition retains
products as mixed-radix decoders, so constructing a generator does not allocate
one 'Outcome' for every element of its Cartesian product.
-}
data LTAGen a = LTAGen
    { generatorOutcomes :: !(Finite (Outcome a))
    , generatorShrinks :: Integer -> [ShrinkCandidate]
    }

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
            [ Outcome 1 value (Witness symbol refinement Top [])
            | Refined value symbol refinement <- entries
            ]
        )
        shrinkFrom
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
        [ Transition symbol refinement [] Top
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
            }

instance Functor Children where
    fmap function childForest =
        childForest
            { childrenOutcomes =
                fmap
                    (\outcome -> outcome{forestValue = function (forestValue outcome)})
                    (childrenOutcomes childForest)
            }

instance Applicative Children where
    pure value = Children (pure $ ForestOutcome 1 value []) (const [])

    functions <*> arguments =
        Children
            (combine <$> functionOutcomes <*> argumentOutcomes)
            shrinkProduct
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
node symbol = refinedNodeBy symbol (const true)

-- | Add a constructor with an explicit result refinement and liquid guard.
refinedNode ::
    (NodeLayer layer, GuardBuilder guard) =>
    Symbol ->
    Refinement ->
    guard ->
    layer a ->
    LTAGen a
refinedNode symbol refinement = refinedNodeBy symbol (const refinement)

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
refinedNodeBy symbol refinementOf guardBuilder layer =
    LTAGen
        ( closeOutcome
            <$> childrenOutcomes childForest
        )
        (childrenShrinks childForest)
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
  where
    branches = withOffsets alternatives

    ensurePositive (weight, _)
        | weight > 0 = Right ()
        | otherwise = Left (NonPositiveWeight weight)

    weightedOutcomes (_, weight, generator, _) =
        fmap
            (\outcome -> outcome{outcomeWeight = weight * outcomeWeight outcome})
            (generatorOutcomes generator)

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
            (transitionGuard transition)
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

-- | Solver-checked support paired with its pure ranked language and shrinks.
data Compiled a = Compiled
    { compiledSupport :: !Automaton
    -- ^ The LTA containing only accepted witnesses.
    , compiledRanked :: !(Tree.Ranked (Generated a))
    -- ^ Pure sampling and replay after solver compilation.
    , compiledShrinkRanks :: !(Map.Map Integer [Integer])
    -- ^ Valid refinement and structural shrinks between accepted ranks.
    }

-- | A checked generator member and its relative sampling weight.
data Generated a = Generated
    { generatedWeight :: !Integer
    , generatedValue :: a
    , generatedTerm :: !LiquidTerm
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
    | ResidualGuard !State !Guard
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
                            acceptedSupport
                            ranked
                            (buildShrinkTable generator accepted table)

{- | Prune and rank a finite acyclic LTA without enumerating its terms.

The core discharges guards per transition. The adapter then counts accepting
runs by dynamic programming and builds a rank decoder over that table. Only
'select' materializes the chosen 'LiquidTerm'. Recursive automata should first
be unfolded to a finite state graph with the desired generation bound.
Ambiguous automata are rejected so ranks continue to identify distinct terms,
not accepting runs.
-}
compileAutomaton :: Entailment -> Automaton -> IO (Either GeneratorError (Compiled LiquidTerm))
compileAutomaton uncachedEntailment automaton = do
    entailment <- cacheEntailment uncachedEntailment
    reduced <- prune entailment automaton
    pure $ do
        acceptedSupport <- first InvalidPruning reduced
        ensureUnconstrained acceptedSupport
        counts <- countAutomaton acceptedSupport
        ensureUnambiguous acceptedSupport $ Map.keys counts
        let total = Map.findWithDefault 0 (automatonInitial acceptedSupport) counts
        ranked <-
            first fromRankedError $
                Tree.fromIndexedOnDemand $
                    Tree.Indexed
                        total
                        (generatedAt acceptedSupport counts)
        pure $ Compiled acceptedSupport ranked Map.empty

{- | Require the pruned automaton to be an ordinary FTA before multiplying
child cardinalities.

Semantic guards are eliminated by LTA state splitting. Syntactic equality may
remain because equality between arbitrary subtrees is not a regular tree
language; it needs the ECTA counting path instead of an FTA product count.
-}
ensureUnconstrained :: Automaton -> Either GeneratorError ()
ensureUnconstrained automaton =
    case [ (state, transitionGuard transition)
         | (state, transitions) <- Map.toList $ automatonTransitions automaton
         , transition <- transitions
         , transitionGuard transition /= Top
         ] of
        residual : _ -> Left $ uncurry ResidualGuard residual
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
countAutomaton :: Automaton -> Either GeneratorError (Map.Map State Integer)
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
ensureUnambiguous :: Automaton -> [State] -> Either GeneratorError ()
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
generatedAt :: Automaton -> Map.Map State Integer -> Integer -> Generated LiquidTerm
generatedAt automaton counts rank =
    let term = decodeState (automatonInitial automaton) rank
     in Generated 1 term term
  where
    table = automatonTransitions automaton

    decodeState state stateRank =
        case selectTransition stateRank $ Map.findWithDefault [] state table of
            Just (transition, transitionRank) ->
                LiquidTerm
                    (transitionSymbol transition)
                    (transitionRefinement transition)
                    (decodeChildren transitionRank $ transitionChildren transition)
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

    decodeChildren _ [] = []
    decodeChildren remaining (child : rest) =
        let suffixCount =
                product
                    [ Map.findWithDefault 0 state counts
                    | state <- rest
                    ]
            (childRank, restRank) = remaining `quotRem` suffixCount
         in decodeState child childRank : decodeChildren restRank rest

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
        Map.findWithDefault [] rank (compiledShrinkRanks compiled)

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
    , witnessGuard :: !Guard
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
            guardVerdict <- evaluateGuard entailment (witnessGuard witness) (witnessTerm witness)
            pure $ andVerdicts childrenVerdict guardVerdict
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
    Either GeneratorError (Automaton, Tree.Ranked (Generated a))
compileAccepted accepted = do
    acceptedSupport <-
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
    pure (acceptedSupport, ranked)

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
                (witnessGuard witness)
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
