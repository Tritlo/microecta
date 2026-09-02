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
import qualified Data.IntMap.Strict as IntMap
import Data.List (nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.LTA
import Data.LTA.Guard (GuardBuilder, buildGuard)
import Data.LTA.Refinement (true)
import qualified Data.Tree.Gen as Tree

-- | A finite weighted language paired with guarded witness trees and shrinks.
data LTAGen a = LTAGen
    { generatorOutcomes :: [Outcome a]
    , generatorShrinks :: Int -> [ShrinkCandidate]
    }

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
        [ Outcome 1 value (Witness symbol refinement Top [])
        | Refined value symbol refinement <- entries
        ]
        shrinkFrom
  where
    shrinkFrom source = case drop source entries of
        Refined _ _ sourceRefinement : _ ->
            [ ShrinkCandidate
                target
                ( WeakenRefinement
                    sourceRefinement
                    candidateRefinement
                    (target < source)
                )
            | (target, Refined _ _ candidateRefinement) <- zip [0 ..] entries
            , target /= source
            ]
        [] -> []

{- | Retain the most specific semantic representatives in each similarity
class, following the LTA paper's similarity minimisation rule.

The projection defines which values are candidates for merging. Within one
class, a strict subtype replaces its supertype; equivalent refinements keep the
earlier entry. Incomparable entries are all retained. This operation is opt-in:
ordinary QuickCheck pools should keep syntactically distinct values when broad
coverage matters more than semantic representative reduction.
-}
minimizePoolBy ::
    (Ord key) =>
    Entailment ->
    (a -> key) ->
    [Refined a] ->
    IO (Either GeneratorError (LTAGen a))
minimizePoolBy _ _ [] = pure $ Left EmptyGenerator
minimizePoolBy entailment similarityKey entries = do
    survivors <- traverse survives $ zip [0 :: Int ..] entries
    pure $ pool . map snd . filter fst <$> sequence survivors
  where
    survives indexed@(_, entry) = do
        dominated <- traverse (dominates indexed) $ zip [0 :: Int ..] entries
        pure $ do
            decisions <- sequence dominated
            pure (not $ or decisions, entry)

    dominates (index, Refined value _ refinement) (candidateIndex, Refined candidate _ candidateRefinement)
        | index == candidateIndex = pure $ Right False
        | similarityKey value /= similarityKey candidate = pure $ Right False
        | otherwise = do
            relation <- refinementRelation entailment candidateRefinement refinement
            pure $ case relation of
                StrictSubtype -> Right True
                Equivalent -> Right (candidateIndex < index)
                StrictSupertype -> Right False
                Incomparable -> Right False
                RelationUnknown -> Left SolverUnknown

-- | Build a singleton refined leaf.
leaf :: a -> Symbol -> Refinement -> LTAGen a
leaf value symbol refinement = pool [refined value symbol refinement]

-- | A generated child forest awaiting one root constructor.
data Children a = Children
    { childrenOutcomes :: [ForestOutcome a]
    , childrenShrinks :: Int -> [ShrinkCandidate]
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
                [ outcome{outcomeValue = function (outcomeValue outcome)}
                | outcome <- generatorOutcomes generator
                ]
            }

instance Functor Children where
    fmap function childForest =
        childForest
            { childrenOutcomes =
                [ outcome{forestValue = function (forestValue outcome)}
                | outcome <- childrenOutcomes childForest
                ]
            }

instance Applicative Children where
    pure value = Children [ForestOutcome 1 value []] (const [])

    functions <*> arguments =
        Children
            [ ForestOutcome
                (forestWeight function * forestWeight argument)
                (forestValue function $ forestValue argument)
                (forestWitnesses function <> forestWitnesses argument)
            | function <- functionOutcomes
            , argument <- argumentOutcomes
            ]
            shrinkProduct
      where
        functionOutcomes = childrenOutcomes functions
        argumentOutcomes = childrenOutcomes arguments
        argumentCount = length argumentOutcomes

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
        [ ForestOutcome
            (outcomeWeight outcome)
            (outcomeValue outcome)
            [outcomeWitness outcome]
        | outcome <- generatorOutcomes generator
        ]
        (generatorShrinks generator)

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
        [ Outcome
            (forestWeight outcome)
            (forestValue outcome)
            (Witness symbol (refinementOf $ forestValue outcome) guard $ forestWitnesses outcome)
        | outcome <- childrenOutcomes childForest
        ]
        (childrenShrinks childForest)
  where
    childForest = asChildren layer
    guard = buildGuard guardBuilder

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
            (concatMap weightedOutcomes branches)
            (shrinkChoice branches)
  where
    branches = withOffsets alternatives

    ensurePositive (weight, _)
        | weight > 0 = Right ()
        | otherwise = Left (NonPositiveWeight weight)

    weightedOutcomes (_, weight, generator, _) =
        [ outcome{outcomeWeight = weight * outcomeWeight outcome}
        | outcome <- generatorOutcomes generator
        ]

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
support = compileWitnesses . map outcomeWitness . generatorOutcomes

-- | Check every candidate, preserving weights for the accepted members.
validOutcomes :: Entailment -> LTAGen a -> IO (Either GeneratorError [Generated a])
validOutcomes entailment generator =
    fmap (fmap $ map acceptedGenerated) $
        checkedOutcomes entailment (generatorOutcomes generator)

-- | Solver-checked support paired with its pure ranked language and shrinks.
data Compiled a = Compiled
    { compiledSupport :: !Automaton
    -- ^ The LTA containing only accepted witnesses.
    , compiledRanked :: !(Tree.Ranked (Generated a))
    -- ^ Pure sampling and replay after solver compilation.
    , compiledShrinkRanks :: !(IntMap.IntMap [Integer])
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
    deriving (Eq, Show)

-- | Discharge guards and refinement ordering once, producing a pure language.
compile :: Entailment -> LTAGen a -> IO (Either GeneratorError (Compiled a))
compile entailment generator = do
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
        IntMap.findWithDefault [] (fromInteger rank) (compiledShrinkRanks compiled)

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
    { shrinkCandidateIndex :: !Int
    , shrinkCandidateCondition :: !ShrinkCondition
    }

data ShrinkCondition
    = AlwaysShrink
    | WeakenRefinement !Refinement !Refinement !Bool

liftShrink :: (Int -> Int) -> ShrinkCandidate -> ShrinkCandidate
liftShrink transform candidate =
    candidate{shrinkCandidateIndex = transform $ shrinkCandidateIndex candidate}

withOffsets :: [(Integer, LTAGen a)] -> [(Int, Integer, LTAGen a, Int)]
withOffsets = go 0
  where
    go _ [] = []
    go offset ((weight, generator) : rest) =
        let count = length $ generatorOutcomes generator
         in (offset, weight, generator, count) : go (offset + count) rest

shrinkChoice :: [(Int, Integer, LTAGen a, Int)] -> Int -> [ShrinkCandidate]
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

type Accepted a = (Int, Outcome a, Generated a)

acceptedGenerated :: Accepted a -> Generated a
acceptedGenerated (_, _, generated) = generated

checkedOutcomes ::
    Entailment ->
    [Outcome a] ->
    IO (Either GeneratorError [Accepted a])
checkedOutcomes entailment = go 0 []
  where
    go _ accepted [] = pure (Right $ reverse accepted)
    go sourceIndex accepted (outcome : rest) =
        case compileWitnesses [outcomeWitness outcome] of
            Left err -> pure (Left err)
            Right automaton -> do
                verdict <- accepts entailment automaton (witnessTerm $ outcomeWitness outcome)
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
                            rest
                    No -> go (sourceIndex + 1) accepted rest
                    Unknown -> pure (Left SolverUnknown)

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
            | source <- [0 .. length (generatorOutcomes generator) - 1]
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
    IntMap.IntMap [Integer]
buildShrinkTable generator accepted implications =
    IntMap.fromList
        [ (acceptedRank, nearestAccepted (Set.singleton sourceIndex) candidates)
        | (acceptedRank, (sourceIndex, _, _)) <- zip [0 ..] accepted
        , let candidates = generatorShrinks generator sourceIndex
        ]
  where
    acceptedRanks =
        IntMap.fromList
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
            , Just acceptedRank <- [IntMap.lookup (shrinkCandidateIndex candidate) acceptedRanks]
            ]
        indirect =
            concat
                [ nearestAccepted
                    (Set.insert target visited)
                    (generatorShrinks generator target)
                | candidate <- eligible
                , let target = shrinkCandidateIndex candidate
                , IntMap.notMember target acceptedRanks
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
