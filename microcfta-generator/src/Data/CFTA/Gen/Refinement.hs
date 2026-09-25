{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
    elements,
    integers,
    every,
    pool,
    Refined (..),
    namedPool,
    leaf,
    checkPool,
    minimizePoolBy,

    -- * Conditions and contracts
    satisfying,
    node,
    guarded,
    refinedNode,
    refinedNodeByRoots,

    -- * Imported automata and datatypes
    fromAutomaton,
    fromAutomatonUpToDepth,
    fromDatatypeUpToDepth,

    -- * Compilation
    compile,
    compileAssuming,
    compileWith,
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
    elements,
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
import Data.CFTA.Gen.Refinement.Internal.Compile (liquidOrder, spineArity, validOutcomes)
import qualified Data.CFTA.Gen.Refinement.Internal.Compile as Compile
import Data.CFTA.Generic (TypedFTA, constructorLabel, datatypeFTA, decodeLabelledTerm)
import Data.CFTA.Refinement (
    Automaton,
    AutomatonError (GuardArityMismatch),
    Entailment (entails),
    Formula,
    LiquidConstraint,
    LiquidSymbol (LiquidSymbol),
    Node (EmptyNode, Node),
    Symbol (Symbol),
    Verdict (Yes),
    boundDepth,
    combineConstraints,
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
import Data.CFTA.Refinement.Expression (
    Literal (..),
    Refinement,
    literal,
    refinementFormula,
    true,
    (.&&),
    (.<=),
    (.==),
 )
import Data.CFTA.Refinement.Guard (
    ContractBuilder (contractArity),
    GuardBuilder,
    buildGuard,
    contract,
    guardArgumentCount,
    requires,
    root,
 )
import Data.CFTA.Refinement.LiquidFixpoint (withZ3Assuming)

-- | A generator over liquid tree automata.
type LTAGen = Gen LiquidSymbol LiquidConstraint

-- | A grouped generator over liquid tree automata.
type Grouped = Gen.Grouped LiquidSymbol LiquidConstraint

{- | Choose uniformly from values, each refined as the value itself.

The refinement of @x@ is @\\v -> v .== literal x@, so a condition or a
contract can decide each value exactly. The value's 'show' names its entry.
-}
elements :: (Literal a, Show a) => [a] -> LTAGen a
elements members = pool [(member, \v -> v .== literal member) | member <- members]

{- | Choose uniformly from the integers that the conditions on this leaf admit.

Each integer is refined as itself, @\\v -> v .== literal x@, as in
'elements'. Bound the integers with 'satisfying' before 'compile':

@integers `satisfying` (\\v -> 0 .<= v .&& v .< 1000000)@

On this leaf, a condition narrows the integers: 'compile' counts them without
enumeration and without the solver, and ranks them in increasing order. A
condition must be linear in @v@.
-}
integers :: LTAGen Integer
integers = withRecipe (Integers unconstrainedConstraint) $ Transparent $ Left SourceRequiresCompilation

{- | Choose uniformly from every value of a type that integers stand for.

Each value is refined as itself, @\\v -> v .== literal x@, as 'elements'
refines its members. A bounded type, such as 'Word8', 'Char', 'Bool', or an
enumeration that derives 'Literal' via 'Enumerated', needs no condition. An
unbounded type, such as 'Integer', needs conditions that bound it. As on
'integers', a condition narrows the values and a contract relates them:

@d <- every @Word8 `satisfying` (./= 0)@

A condition and a contract read a value as its integer, 'toLiteral', so
compare it with a 'literal', as in @\\c -> c ./= literal Red@. Arithmetic on
these integers is exact: it does not wrap around. A term names each value by
its integer.
-}
every :: forall a. (Literal a) => LTAGen a
every = case literalRange :: (Maybe a, Maybe a) of
    (Nothing, Nothing) -> fromLiteral <$> integers
    (least, greatest) ->
        fromLiteral
            <$> integers
                `satisfying` \v ->
                    foldr
                        (.&&)
                        true
                        ([literal low .<= v | Just low <- [least]] <> [v .<= literal high | Just high <- [greatest]])

{- | Choose uniformly from values with their refinements.

A refinement can be weaker than the value itself, as in
@(3, \\v -> v ./= 0)@: the solver then knows only that. The generator trusts
each refinement, and 'checkPool' checks them. The value's 'show' names its
entry. Repeated entries are repeated ranks.
-}
pool :: (Show a) => [(a, Refinement)] -> LTAGen a
pool entries = namedPool [Refined member (fromString $ show member) refinement | (member, refinement) <- entries]

-- | One atom of a refined pool: a value, its symbol, and its refinement.
data Refined a = Refined !a !Symbol !Refinement

-- | Choose uniformly from refined atoms with explicit symbols.
namedPool :: [Refined a] -> LTAGen a
namedPool entries = oneof [leaf member symbol refinement | Refined member symbol refinement <- entries]

-- | One refined atom.
leaf :: a -> Symbol -> Refinement -> LTAGen a
leaf member symbol refinement = Gen.node (LiquidSymbol symbol $ refinementFormula refinement) $ pure member

{- | Find the pool entries whose refinement the solver does not prove.

For each entry, the solver decides whether @v .== literal x@ implies the
refinement. The result gives the values for which the answer is not 'Yes', in
pool order. An empty result means that each refinement holds.
-}
checkPool :: (Literal a) => Entailment -> [(a, Refinement)] -> IO [a]
checkPool solver entries =
    fmap concat . traverse check $ entries
  where
    check (member, refinement) = do
        verdict <- entails solver (refinementFormula (.== literal member)) (refinementFormula refinement)
        pure [member | verdict /= Yes]

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
        pure . namedPool $
            [ entry
            | (symbol, entry) <- zip poolSymbols entries
            , Set.member symbol retained
            ]
  where
    poolAutomaton = Node poolTransitions
    poolSymbols = map poolSymbol [0 :: Int .. length entries - 1]
    poolTransitions =
        [ Transition symbol (refinementFormula refinement) [] unconstrainedConstraint
        | (symbol, Refined _ _ refinement) <- zip poolSymbols entries
        ]
    classes =
        Map.fromList
            [ (symbol, similarityKey value)
            | (symbol, Refined value _ _) <- zip poolSymbols entries
            ]
    classify transition = Map.lookup (transitionSymbol transition) classes

    poolSymbol index = fromString $ "__microlta_pool_" <> show index

{- | Keep the terms whose root refinement implies the condition.

Use it where a child is drawn:

@d <- elements [0 .. 5] `satisfying` (\\v -> v ./= 0)@

The condition applies to the root of each term, the constructor that the
generator ends in. A pool, a leaf, a node, a bounded import, a choice of these,
and a mapped generator have such a root. On 'integers', the condition narrows
the integers. An unbounded import with a recursive
root, and another generator, give 'ConditionNeedsConstructor', because the
condition must not apply to the recursive occurrences. The condition can name only @v@ and ambient
names; a relation between children is the contract of 'guarded'.
-}
satisfying :: LTAGen a -> Refinement -> LTAGen a
satisfying generator condition = case generator of
    Transparent (Left err) | err /= SourceRequiresCompilation -> generator
    _ -> case genRecipe generator of
        Closed label constraint child -> deferred (Closed label (conditioned constraint) child)
        ClosedBy labelOf constraint child -> deferred (ClosedBy labelOf (conditioned constraint) child)
        Integers constraint -> deferred (Integers $ conditioned constraint)
        Chosen alternatives -> Flat.frequency [(weight, alternative `satisfying` condition) | (weight, alternative) <- alternatives]
        Mapped transform inner -> transform <$> (inner `satisfying` condition)
        Imported bound graph -> case maybe graph (`boundDepth` graph) bound of
            EmptyNode -> generator
            Node transitions ->
                fromAutomaton $
                    Node
                        [ Transition symbol refinement children (conditioned constraint)
                        | Transition symbol refinement children constraint <- transitions
                        ]
            _ -> Transparent $ Left ConditionNeedsConstructor
        _ -> Transparent $ Left ConditionNeedsConstructor
  where
    conditioned constraint = constraint `combineConstraints` (root `requires` condition)
    deferred recipe = withRecipe recipe $ Transparent $ Left SourceRequiresCompilation

{- | Close an applicative child description with one constructor.

With @ApplicativeDo@ and @QualifiedDo@:

@node "divide" $ LTAGen.do ...@

Put a condition on one child where it is drawn, with 'satisfying'. Use
'guarded' for a contract that relates children.
-}
node :: Symbol -> LTAGen a -> LTAGen a
node symbol = refinedNode symbol (const true) unconstrainedConstraint

{- | Close a child description with a constructor whose contract relates its
children.

The contract takes one term for each child, in order, as in
@\\n i -> 0 .<= i .&& i .< n@. The solver proves each conjunct separately. For
a conjunct, it assumes the refinement of each child that the conjunct names.
The contract must take one term for every child.
-}
guarded :: (ContractBuilder contract) => Symbol -> contract -> LTAGen a -> LTAGen a
guarded symbol builder child
    | contractArity builder /= arity =
        Transparent $ Left $ InvalidSupport $ GuardArityMismatch symbol arity (contractArity builder)
    | otherwise = refinedNode symbol (const true) (contract builder) child
  where
    arity = spineArity child

{- | Close a child description with a constructor that has a refinement and a
positional guard.

This is the form of the paper's encodings: the guard reads the children by
position, as "Data.CFTA.Refinement.Guard" builds it, and the refinement is the
constructor's own result.
-}
refinedNode :: (GuardBuilder guard) => Symbol -> Refinement -> guard -> LTAGen a -> LTAGen a
refinedNode symbol refinement guardBuilder child =
    closeGuarded symbol guardBuilder child (Closed label) $ \constraint ->
        if constraint == unconstrainedConstraint
            then Just $ Gen.node label child
            else Nothing
  where
    label = LiquidSymbol symbol $ refinementFormula refinement

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
    closeGuarded
        symbol
        guardBuilder
        child
        (ClosedBy $ \roots -> LiquidSymbol symbol $ refinementFormula $ refinementOf roots)
        (const Nothing)

{- | Close a child description with a guarded constructor.

The guard's argument count must match the child positions. A constructor
the engine can build at once is built; the rest waits for 'compile'.
-}
closeGuarded ::
    (GuardBuilder guard) =>
    Symbol ->
    guard ->
    LTAGen a ->
    (LiquidConstraint -> LTAGen a -> Recipe LiquidSymbol LiquidConstraint a) ->
    (LiquidConstraint -> Maybe (LTAGen a)) ->
    LTAGen a
closeGuarded symbol guardBuilder child recipe immediate
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
                (refinementFormula refinement)
                (map (nodes Map.!) (FTA.transitionChildren transition))
                constraint
    decode term =
        case decodeLabelledTerm datatype (fmap (\(Symbol label) -> Text.unpack label) $ eraseRefinements term) of
            Just value -> value
            Nothing ->
                error
                    "microcfta-generator bug in Data.CFTA.Gen.Refinement.fromDatatypeUpToDepth: \
                    \the derived codec rejected a term of its own grammar"

{- | Compile a generator with Z3.

The solver decides every guard, condition, and contract once, and the result
is an ordinary finite generator. The call fails with the 'explain' text of the
error when the generator cannot be compiled. Each free name in a refinement is
an integer.
-}
compile :: LTAGen a -> IO (LTAGen a)
compile = compileAssuming []

{- | Compile a generator with Z3 under ambient facts, such as
@[variable "input" .== 2]@, that the solver may assume.
-}
compileAssuming :: [Formula] -> LTAGen a -> IO (LTAGen a)
compileAssuming assumptions generator =
    withZ3Assuming [] assumptions $ \solver -> compileWith solver generator >>= orFail

{- | Compile a generator with the given solver, and return the error instead of
failing. Use it to share one solver between several generators.
-}
compileWith :: Entailment -> LTAGen a -> IO (Either GenError (LTAGen a))
compileWith = Compile.compile
