{-# LANGUAGE PatternSynonyms #-}

{- | Generators over liquid tree automata.

A refinement generator is a generator over 'LiquidSymbol' and
'LiquidConstraint': every constructor carries a refinement, and the guard of
a constructor relates the refinements of its children. Everything of
"Data.CFTA.Gen" applies, and this module adds the refined sources, the
guarded constructors, and the imports of the theory.

A guard that the engine cannot decide without a solver defers the generator:
its inspectors report 'SourceRequiresCompilation' until 'compile' has
decided every guard once, with the solver, and returned an ordinary finite
generator. A guard of Boolean equality between subterms, and a constructor
without a guard, need no solver and are built at once.
-}
module Data.CFTA.Gen.Refinement (
    -- * Generators
    LTAGen,
    Grouped,
    module Data.CFTA.Gen,

    -- * Refined sources
    Refined (..),
    pool,
    leaf,
    minimizePoolBy,

    -- * Guarded constructors
    node,
    refinedNode,
    refinedNodeByRoots,

    -- * Imported automata and datatypes
    fromAutomaton,
    fromAutomatonUpToDepth,
    fromDatatypeUpToDepth,

    -- * Compilation
    compile,
    validOutcomes,
) where

import Data.Bifunctor (first)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.String (fromString)
import qualified Data.Text as Text
import qualified Data.Tree as Tree

import qualified Data.CFTA as FTA
import Data.CFTA.Gen hiding (
    Grouped,
    fromAutomaton,
    fromAutomatonUpToDepth,
    fromDatatype,
    fromDatatypeUpToDepth,
    leaf,
    node,
 )
import qualified Data.CFTA.Gen as Gen
import qualified Data.CFTA.Gen.Internal.Flat as Flat
import Data.CFTA.Gen.Internal.Types (Gen (..), Language (..), Recipe (..), withRecipe, pattern Transparent)
import Data.CFTA.Gen.Refinement.Internal.Compile (compile, liquidOrder, spineArity, validOutcomes)
import Data.CFTA.Generic (TypedFTA, constructorLabel, datatypeFTA, decodeLabelledTerm)
import Data.CFTA.Refinement (
    Automaton,
    AutomatonError (GuardArityMismatch),
    Entailment,
    LiquidConstraint,
    LiquidSymbol (LiquidSymbol),
    Node (Node),
    Refinement,
    Symbol (Symbol),
    eraseRefinements,
    minimize,
    nodeEdges,
    refinementSubtypingBy,
    similarity,
    transitionSymbol,
    unconstrainedConstraint,
    validate,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (true)
import Data.CFTA.Refinement.Guard (GuardBuilder, buildGuard, guardArgumentCount)

-- | A generator over liquid tree automata.
type LTAGen = Gen LiquidSymbol LiquidConstraint

-- | A grouped generator over liquid tree automata.
type Grouped = Gen.Grouped LiquidSymbol LiquidConstraint

{- | One atom of a refined pool: a value, its symbol, and its refinement.

The refinement is trusted metadata; checking that an arbitrary Haskell value
satisfies it requires a separate value encoding.
-}
data Refined a = Refined !a !Symbol !Refinement

-- | Choose uniformly from refined atoms. Repeated entries are repeated ranks.
pool :: [Refined a] -> LTAGen a
pool entries = oneof [leaf value symbol refinement | Refined value symbol refinement <- entries]

-- | One refined atom.
leaf :: a -> Symbol -> Refinement -> LTAGen a
leaf value symbol refinement = Gen.node (LiquidSymbol symbol refinement) $ pure value

{- | Retain the most specific semantic representatives in each similarity
class through the core LTA @Similarity@ and @Minimize@ procedures.

The pool is represented as a one-node LTA whose transition refinements are the
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
    IO (Either GenError (LTAGen a))
minimizePoolBy _ _ [] = pure $ Left EmptyGenerator
minimizePoolBy entailment similarityKey entries = do
    inferred <- similarity (refinementSubtypingBy entailment classify) poolAutomaton
    pure $ do
        related <- first InvalidSimilarity inferred
        reduced <- first InvalidMinimization $ minimize poolAutomaton related
        let retained = Set.fromList [transitionSymbol transition | transition <- nodeEdges reduced]
        pure . pool $
            [ entry
            | (symbol, entry) <- zip poolSymbols entries
            , Set.member symbol retained
            ]
  where
    poolAutomaton = Node poolTransitions
    poolSymbols = map poolSymbol [0 :: Int .. length entries - 1]
    poolTransitions =
        [ Transition symbol refinement [] unconstrainedConstraint
        | (symbol, Refined _ _ refinement) <- zip poolSymbols entries
        ]
    classes =
        Map.fromList
            [ (symbol, similarityKey value)
            | (symbol, Refined value _ _) <- zip poolSymbols entries
            ]
    classify transition = Map.lookup (transitionSymbol transition) classes

    poolSymbol index = fromString $ "__microlta_pool_" <> show index

{- | Close an applicative child description with a guarded constructor.

With @ApplicativeDo@ and @QualifiedDo@:

@node "pair" guard $ LTA.do ...@

The guard reads the children by position, as "Data.CFTA.Refinement.Guard"
builds it. The constructor's own refinement is the universally accepting one;
use 'refinedNode' when the constructor establishes a more precise result.
-}
node :: (GuardBuilder guard) => Symbol -> guard -> LTAGen a -> LTAGen a
node symbol = refinedNode symbol true

-- | Close a child description with a constructor that has a refinement and a guard.
refinedNode :: (GuardBuilder guard) => Symbol -> Refinement -> guard -> LTAGen a -> LTAGen a
refinedNode symbol refinement guardBuilder child =
    guarded symbol guardBuilder child (Closed label) $ \constraint ->
        if constraint == unconstrainedConstraint
            then Just $ Gen.node label child
            else Nothing
  where
    label = LiquidSymbol symbol refinement

{- | Close a child description with a constructor whose refinement is computed
from the labels of its children.

'compile' calls the function once per tuple of child groups, and
'validOutcomes' once per candidate.
-}
refinedNodeByRoots ::
    (GuardBuilder guard) =>
    Symbol ->
    ([LiquidSymbol] -> Refinement) ->
    guard ->
    LTAGen a ->
    LTAGen a
refinedNodeByRoots symbol refinementOf guardBuilder child =
    guarded symbol guardBuilder child (ClosedBy $ \roots -> LiquidSymbol symbol $ refinementOf roots) (const Nothing)

{- | Close a child description with a guarded constructor.

The guard's argument count must match the child positions. A constructor
the engine can build at once is built; the rest waits for 'compile'.
-}
guarded ::
    (GuardBuilder guard) =>
    Symbol ->
    guard ->
    LTAGen a ->
    (LiquidConstraint -> LTAGen a -> Recipe LiquidSymbol LiquidConstraint a) ->
    (LiquidConstraint -> Maybe (LTAGen a)) ->
    LTAGen a
guarded symbol guardBuilder child recipe immediate
    | Just supplied <- guardArgumentCount guardBuilder
    , supplied /= arity =
        Transparent $ Left $ InvalidSupport $ GuardArityMismatch symbol arity supplied
    | Just built <- immediate constraint = built
    | otherwise = withRecipe (recipe constraint child) $ Transparent $ Left SourceRequiresCompilation
  where
    arity = spineArity child
    constraint = buildGuard guardBuilder

{- | Read a liquid automaton as a generator of the terms it accepts.

An automaton whose guards the engine can count is read at once, as
'Data.CFTA.Gen.fromAutomaton' reads it. One with guards that need the solver
waits for 'compile', which prunes it first. Symbolic ranks order constructors
by symbol text and refinement.
-}
fromAutomaton :: Automaton -> LTAGen (Tree.Tree LiquidSymbol)
fromAutomaton = deferConstrained . Flat.fromAutomaton liquidOrder

-- | Read the terms a liquid automaton accepts up to a constructor-depth bound. A leaf has depth zero.
fromAutomatonUpToDepth :: Int -> Automaton -> LTAGen (Tree.Tree LiquidSymbol)
fromAutomatonUpToDepth depth = deferConstrained . Flat.fromAutomatonUpToDepth liquidOrder depth

-- | Defer an import whose guards the engine cannot count to 'compile'.
deferConstrained :: LTAGen a -> LTAGen a
deferConstrained generator = case genLanguage generator of
    TransparentLanguage (Left CannotCountConstrainedEdges) -> deferred
    CyclicLanguage (Left CannotCountConstrainedEdges) -> deferred
    _ -> generator
  where
    deferred = generator{genLanguage = TransparentLanguage $ Left SourceRequiresCompilation}

{- | Import a derived datatype with constructor refinements and liquid guards.

The grammar is bounded, interned, and validated as an LTA, and read as
'fromAutomatonUpToDepth' reads it. The datatype codec supplies the generated
values; the constructor terms keep their ranks.
-}
fromDatatypeUpToDepth :: Int -> TypedFTA (Refinement, LiquidConstraint) a -> LTAGen a
fromDatatypeUpToDepth depth datatype =
    case validate graph of
        Left err -> Transparent $ Left $ InvalidSupport err
        Right () -> decode <$> fromAutomatonUpToDepth depth graph
  where
    bounded = FTA.boundDepth depth $ datatypeFTA datatype
    graph = nodes Map.! FTA.initialState bounded
    -- The bounded graph is acyclic and the map is lazy in its values, so
    -- each state is interned once, on demand.
    nodes = fmap (Node . map liquidTransition) (FTA.transitionTable bounded)
    liquidTransition transition =
        let (refinement, constraint) = FTA.transitionConstraint transition
         in Transition
                (fromString $ constructorLabel $ FTA.transitionSymbol transition)
                refinement
                (map (nodes Map.!) (FTA.transitionChildren transition))
                constraint
    decode term =
        case decodeLabelledTerm datatype (fmap (\(Symbol label) -> Text.unpack label) $ eraseRefinements term) of
            Just value -> value
            Nothing ->
                error
                    "microcfta-generator bug in Data.CFTA.Gen.Refinement.fromDatatypeUpToDepth: \
                    \the derived codec rejected a term of its own grammar"
