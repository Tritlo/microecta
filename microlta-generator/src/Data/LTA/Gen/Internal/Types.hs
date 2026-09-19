{-# LANGUAGE GADTs #-}

{- | The generator types, their instances, and the finite rank plumbing.

A generator keeps two views of one source. 'Prepared' holds the finite ranked
outcome language that sampling and shrinking read. 'Recipe' holds the
compositional description that the grouped solver path reads. 'Finite' wraps
the shared ranked engine so an empty language needs no special case.
-}
module Data.LTA.Gen.Internal.Types (
    -- * Finite rank plumbing
    Finite (..),
    finiteFromList,
    finiteOneof,
    finiteCardinality,
    finiteSelect,
    enumerateFinite,

    -- * Outcomes and shrink plans
    Outcome (..),
    ShrinkCandidate (..),
    ShrinkCondition (..),
    liftShrink,
    Accepted,
    acceptedGenerated,

    -- * Sources
    LTAGen (..),
    Prepared (..),
    generatorOutcomes,
    generatorShrinks,
    Refined (..),

    -- * Retained recipes
    Recipe (..),
    NodeRefinement (..),
    RootObservation (..),
    ChildRecipe (..),

    -- * Child forests
    Children (..),
    PreparedChildren (..),
    ForestOutcome (..),
    NodeLayer (..),
    children,
    applyChildren,

    -- * Compiled generators
    CompiledSupport (..),
    Compiled (..),
    Generated (..),
) where

import Data.Bifunctor (first)
import qualified Data.Tree as Tree

import qualified Data.CFTA.Equality as ECTA.Core
import Data.CFTA.Equality.Constraints (EqConstraints)
import Data.LTA
import Data.LTA.Gen.Internal.Error (GeneratorError (..), fromRankedError)
import Data.LTA.Gen.Internal.Witness (Witness)
import qualified Data.Ranked as Ranked

-- | A possibly empty wrapper around the shared non-empty ranked engine.
data Finite a
    = EmptyFinite
    | RankedFinite !(Ranked.Ranked a)

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
    case Ranked.fromWeighted [(1, value) | value <- values] of
        Right ranked -> RankedFinite ranked
        Left err -> error $ "microlta-generator bug in Data.LTA.Gen.Internal.Types.finiteFromList: " <> show err

-- | Combine ranked branches without flattening their members.
finiteOneof :: [Finite a] -> Finite a
finiteOneof alternatives =
    case [ranked | RankedFinite ranked <- alternatives] of
        [] -> EmptyFinite
        rankedAlternatives ->
            case Ranked.oneof rankedAlternatives of
                Right ranked -> RankedFinite ranked
                Left err -> error $ "microlta-generator bug in Data.LTA.Gen.Internal.Types.finiteOneof: " <> show err

-- | Exact number of ranks without enumerating their values.
finiteCardinality :: Finite a -> Integer
finiteCardinality EmptyFinite = 0
finiteCardinality (RankedFinite ranked) = Ranked.cardinality ranked

-- | Decode one valid rank.
finiteSelect :: Integer -> Finite a -> Either GeneratorError a
finiteSelect rank EmptyFinite = Left $ SelectionOutOfRange rank 0
finiteSelect rank (RankedFinite ranked) =
    first fromRankedError $ Ranked.unrank ranked rank

-- | All valid ranks of a finite language.
finiteRanks :: Finite a -> [Integer]
finiteRanks finite = [0 .. finiteCardinality finite - 1]

-- | Materialize a finite language only for an explicit support observer.
enumerateFinite :: Finite a -> Either GeneratorError [a]
enumerateFinite finite = traverse (`finiteSelect` finite) $ finiteRanks finite

-- | One source member with its relative weight and complete witness.
data Outcome a = Outcome
    { outcomeWeight :: !Integer
    , outcomeValue :: a
    , outcomeWitness :: !Witness
    }

-- | One source shrink target and the condition that permits it.
data ShrinkCandidate = ShrinkCandidate
    { shrinkCandidateIndex :: !Integer
    , shrinkCandidateCondition :: !ShrinkCondition
    }

-- | Whether a shrink always holds, or waits on a refinement implication.
data ShrinkCondition
    = AlwaysShrink
    | WeakenRefinement !Refinement !Refinement !Bool

-- | Move a shrink target into an enclosing rank domain.
liftShrink :: (Integer -> Integer) -> ShrinkCandidate -> ShrinkCandidate
liftShrink transform candidate =
    candidate{shrinkCandidateIndex = transform $ shrinkCandidateIndex candidate}

{- | A finite weighted language paired with guarded witness trees and shrinks.

The outcome language is an indexed rank plan. Applicative composition retains
products as mixed-radix decoders, so constructing a generator does not allocate
one outcome record for every element of its Cartesian product.
-}
data LTAGen a = LTAGen
    { generatorPrepared :: !(Maybe (Prepared a))
    , generatorRecipe :: !(Either GeneratorError (Recipe a))
    }

-- | Finite source operations available after deferred imports are compiled.
data Prepared a = Prepared
    { preparedOutcomes :: !(Finite (Outcome a))
    , preparedShrinks :: Integer -> [ShrinkCandidate]
    }

-- | Read a source after preparation has established its finite rank domain.
generatorOutcomes :: LTAGen a -> Finite (Outcome a)
generatorOutcomes = preparedOutcomes . preparedGenerator

-- | Read the source shrink plan after preparation.
generatorShrinks :: LTAGen a -> Integer -> [ShrinkCandidate]
generatorShrinks = preparedShrinks . preparedGenerator

-- | Internal accessor for paths that have already prepared their sources.
preparedGenerator :: LTAGen a -> Prepared a
preparedGenerator generator =
    case generatorPrepared generator of
        Just prepared -> prepared
        Nothing -> error "microlta-generator bug in Data.LTA.Gen.Internal.Types: source used before preparation"

{- | One atom that can participate in refinement-based pool shrinking.

The refinement is trusted metadata; checking that an arbitrary Haskell value
satisfies it requires a separate value encoding.
-}
data Refined a = Refined !a !Symbol !Refinement

-- | Compositional source retained for solver-compiled grouped generation.
data Recipe a where
    PoolRecipe :: [Refined a] -> Recipe a
    MapRecipe :: (a -> b) -> Recipe a -> Recipe b
    NodeRecipe :: Symbol -> NodeRefinement a -> LiquidConstraint -> ChildRecipe a -> Recipe a
    ChoiceRecipe :: [(Integer, Recipe a)] -> Recipe a
    AutomatonRecipe :: Int -> Automaton -> Recipe (Tree.Tree LiquidSymbol)
    CompiledRecipe :: Compiled a -> Recipe a

-- | Whether a node refinement is known before decoding its domain value.
data NodeRefinement a
    = FixedRefinement !Refinement
    | ComputedRefinement (a -> Refinement)
    | RootComputedRefinement ([RootObservation] -> Refinement)

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

-- | A generated child forest awaiting one root constructor.
data Children a = Children
    { childrenPrepared :: !(Maybe (PreparedChildren a))
    , childrenRecipe :: !(Either GeneratorError (ChildRecipe a))
    }

-- | A finite child product and its source shrink plan.
data PreparedChildren a = PreparedChildren
    { childrenOutcomes :: !(Finite (ForestOutcome a))
    , childrenShrinks :: Integer -> [ShrinkCandidate]
    }

-- | One child forest member with its weight and ordered child witnesses.
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
            { generatorPrepared = fmap mapPrepared $ generatorPrepared generator
            , generatorRecipe = MapRecipe function <$> generatorRecipe generator
            }
      where
        mapPrepared prepared =
            prepared
                { preparedOutcomes =
                    fmap
                        (\outcome -> outcome{outcomeValue = function (outcomeValue outcome)})
                        (preparedOutcomes prepared)
                }

instance Functor Children where
    fmap function childForest =
        childForest
            { childrenPrepared = fmap mapPrepared $ childrenPrepared childForest
            , childrenRecipe = fmap (fmapChildRecipe function) $ childrenRecipe childForest
            }
      where
        mapPrepared prepared =
            prepared
                { childrenOutcomes =
                    fmap
                        (\outcome -> outcome{forestValue = function (forestValue outcome)})
                        (childrenOutcomes prepared)
                }

instance Applicative Children where
    pure value =
        Children
            (Just $ PreparedChildren (pure $ ForestOutcome 1 value []) (const []))
            (Right $ PureChildRecipe value)

    functions <*> arguments =
        Children
            (combinePrepared <$> childrenPrepared functions <*> childrenPrepared arguments)
            (ApplyChildRecipe <$> childrenRecipe functions <*> childrenRecipe arguments)
      where
        combinePrepared preparedFunctions preparedArguments =
            PreparedChildren
                (combine <$> childrenOutcomes preparedFunctions <*> childrenOutcomes preparedArguments)
                (shrinkProduct preparedFunctions preparedArguments)

        combine function argument =
            ForestOutcome
                (forestWeight function * forestWeight argument)
                (forestValue function $ forestValue argument)
                (forestWitnesses function <> forestWitnesses argument)

        shrinkProduct preparedFunctions preparedArguments index
            | argumentCount <= 0 = []
            | otherwise =
                let (functionIndex, argumentIndex) = index `quotRem` argumentCount
                 in [ liftShrink
                        (\candidate -> candidate * argumentCount + argumentIndex)
                        shrink
                    | shrink <- childrenShrinks preparedFunctions functionIndex
                    ]
                        <> [ liftShrink
                                (functionIndex * argumentCount +)
                                shrink
                           | shrink <- childrenShrinks preparedArguments argumentIndex
                           ]
          where
            argumentCount = finiteCardinality $ childrenOutcomes preparedArguments

-- | Treat one LTA language as a one-child forest.
children :: LTAGen a -> Children a
children generator =
    Children
        (toPrepared <$> generatorPrepared generator)
        (OneChildRecipe <$> generatorRecipe generator)
  where
    toPrepared prepared =
        PreparedChildren (toForest <$> preparedOutcomes prepared) (preparedShrinks prepared)
    toForest outcome =
        ForestOutcome
            (outcomeWeight outcome)
            (outcomeValue outcome)
            [outcomeWitness outcome]

-- | Apply one generated child-forest function to another child forest.
applyChildren :: Children (a -> b) -> Children a -> Children b
applyChildren = (<*>)

-- | The support retained by either compilation path.
data CompiledSupport
    = -- | Semantic pruning produced an equality-annotated generic FTA.
      EqualitySupport !EqualityAutomaton
    | -- | A pruned LTA retains Boolean equalities interpreted by the symbolic ranker.
      SymbolicSupport !Automaton
    | -- | A grouped relational plan produced native hash-consed ECTA support.
      RelationalSupport !(ECTA.Core.Node Symbol EqConstraints)

-- | Solver-checked support paired with its pure ranked language and shrinks.
data Compiled a = Compiled
    { compiledSupport :: !CompiledSupport
    -- ^ The graph after every solver obligation is discharged.
    , compiledRanked :: !(Ranked.Ranked (Generated a))
    -- ^ Pure sampling and replay after solver compilation.
    , compiledPlanShrinks :: !(Integer -> [Integer])
    -- ^ Valid refinement and structural shrinks from the retained rank plan.
    }

-- | A checked generator member and its relative sampling weight.
data Generated a = Generated
    { generatedWeight :: !Integer
    , generatedValue :: a
    , generatedTerm :: Tree.Tree LiquidSymbol
    {- ^ The annotated witness. Automaton decoders build this lazily so sampling
    a mapped domain value does not pay for an intermediate 'Tree.Tree' 'LiquidSymbol'.
    -}
    }
    deriving (Eq, Show)

-- | One accepted candidate: its source rank, its outcome, and its member.
type Accepted a = (Integer, Outcome a, Generated a)

-- | Read the generated member of one accepted candidate.
acceptedGenerated :: Accepted a -> Generated a
acceptedGenerated (_, _, generated) = generated
