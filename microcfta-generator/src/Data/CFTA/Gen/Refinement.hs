{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- | Generators over liquid tree automata.

A refinement generator is a generator over 'Symbol' and
'Constraint': every constructor carries a refinement, and the guard of
a constructor relates the refinements of its children. Everything of
"Data.CFTA.Gen" applies, and this module adds the refined sources, the
guarded constructors, and the imports of the theory.

A guard that the engine cannot decide without a solver defers the generator:
its inspectors report 'SourceRequiresCompilation' until 'compile' has
decided every guard once, with the solver, and returned an ordinary
generator: finite, or recursive for a recursive import. A constructor without a guard needs no solver and is built at once.
A guard of Boolean equality between subterms also defers the generator. An
imported automaton counts Boolean equality symbolically and is built at once.
-}
module Data.CFTA.Gen.Refinement (
    -- * Generators
    LTAGen,
    Grouped,
    module Data.CFTA.Gen,

    -- * Refined sources
    elements,
    every,
    pool,
    Refined (..),
    namedPool,
    leaf,
    checkPool,
    minimizePoolOn,

    -- * Conditions, contracts, and measures
    satisfying,
    node,
    guarded,
    measured,
    recurUpTo,
    refinedNode,
    measuredNode,
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

import Control.Applicative ((<|>))
import Data.Bifunctor (first)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.String (fromString)
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
    rankOfValue,
 )
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Gen.Internal.Automaton (datatypeDecoder, declarationOrder, undecodableConstructor)
import qualified Data.CFTA.Gen.Internal.Flat as Flat
import Data.CFTA.Gen.Internal.Types (Gen (..), Language (..), Recipe (..), withRecipe, pattern Transparent)
import Data.CFTA.Gen.Refinement.Internal.Compile (spineArity, validOutcomes)
import qualified Data.CFTA.Gen.Refinement.Internal.Compile as Compile
import Data.CFTA.Generic (TypedFTA, constructorLabel, constructorName, datatypeDecode, datatypeFTA)
import Data.CFTA.Index (ArgumentIndex (..), Depth)
import Data.CFTA.Refinement (
    Automaton,
    AutomatonError (GuardArityMismatch),
    Constraint,
    Entailment (entails),
    Formula,
    Node (EmptyNode, Mu, Node),
    Symbol (RefinedSymbol, Symbol),
    Verdict (Yes),
    boundDepth,
    conjoinConstraints,
    contractTermName,
    eraseRefinements,
    minimize,
    noConstraint,
    nodeEdges,
    refinementSubtypingOn,
    similarity,
    transitionSymbol,
    unfoldOuterRec,
    validate,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (
    Literal (..),
    Refinement,
    definingTerm,
    freeNames,
    literal,
    refinementFormula,
    substitute,
    true,
    (.&&),
    (.<=),
    (.==),
 )
import Data.CFTA.Refinement.Guard (
    ContractBuilder (contractArity),
    GuardBuilder,
    MeasureBuilder (measureArity),
    buildGuard,
    contract,
    guardArgumentCount,
    measureTerm,
    requires,
    root,
 )
import Data.CFTA.Refinement.Lattice (onlyPoint)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3Assuming)
import Data.CFTA.Symbol (liquidOrder, valueName)

-- | A generator over liquid tree automata.
type LTAGen = Gen Symbol

-- | A grouped generator over liquid tree automata.
type Grouped = Gen.Grouped Symbol

{- | Choose uniformly from values, each refined as the value itself.

The refinement of @x@ is @\\v -> v .== literal x@, so a condition or a
contract can decide each value exactly. The value's 'show' names its entry.
-}
elements :: (Literal a, Show a) => [a] -> LTAGen a
elements members = pool [(member, \v -> v .== literal member) | member <- members]

{- | Choose uniformly from every value of a type that integers stand for.

Each value is refined as itself, @\\v -> v .== literal x@, as 'elements'
refines its members. A bounded type, such as 'Word8', 'Char', 'Bool', or an
enumeration that derives 'Literal' via 'Enumerated', needs no condition. An
unbounded type, such as 'Integer', needs conditions that bound it:

@d <- every @Word8 `satisfying` (./= 0)@

@n <- every @Integer `satisfying` (\\v -> 0 .<= v .&& v .< 1000000)@

On this leaf, a condition narrows the values, and a contract of 'guarded' keeps
the tuples of values that it admits. 'compile' counts them without enumeration,
by counting integer points. The solver still decides the parts of a guard that
read no value of 'every'. Inside one group, 'compile' ranks the tuples in
increasing lexicographic order, with the leaves of 'every' as the digits from
left to right and the tuple as the fastest part of the rank. Groups are ordered
by their keys, so ranks in different groups are not ordered by their integers. A
condition and a contract must be linear. They read a value as its integer,
'toLiteral', so compare it with a 'literal', as in
@\\c -> c ./= literal Red@. Arithmetic on these integers is exact: it does
not wrap around. A term names each value by its integer.
-}
every :: forall a. (Literal a) => LTAGen a
every = case literalRange :: (Maybe a, Maybe a) of
    (Nothing, Nothing) -> fromLiteral <$> integerLeaf
    (least, greatest) ->
        fromLiteral
            <$> integerLeaf
                `satisfying` \v ->
                    foldr
                        (.&&)
                        true
                        ([literal low .<= v | Just low <- [least]] <> [v .<= literal high | Just high <- [greatest]])

-- | The leaf of all integers, which conditions narrow and 'compile' counts.
integerLeaf :: LTAGen Integer
integerLeaf = withRecipe (Integers noConstraint) $ Transparent $ Left SourceRequiresCompilation

{- | Choose uniformly from values with their refinements.

A refinement can be weaker than the value itself, as in
@(3, \\v -> v ./= 0)@: the solver then has only that fact. The generator
assumes that each refinement holds, and 'checkPool' checks them. The value's
'show' names its entry. Repeated entries are repeated ranks.
-}
pool :: (Show a) => [(a, Refinement)] -> LTAGen a
pool entries = namedPool [Refined member (fromString $ show member) refinement | (member, refinement) <- entries]

-- | One atom of a refined pool: a value, its symbol, and its refinement.
data Refined a = Refined !a !Symbol !Refinement

-- | Choose uniformly from refined atoms with explicit symbols.
namedPool :: [Refined a] -> LTAGen a
namedPool entries = oneof [leaf member symbol refinement | Refined member symbol refinement <- entries]

{- | One refined atom: a Haskell value, a symbol, and a refinement.

The refinement is about the integer @v@ of the atom, not about the Haskell
value. Every node of a term of a liquid tree automaton has one such integer,
and the contracts and measures of a parent read only these integers. The
author chooses what the integer means: @leaf Leaf "leaf" (.== 0)@ gives the
leaf the integer 0, which 'measured' then reads as a black height.
-}
leaf :: a -> Symbol -> Refinement -> LTAGen a
leaf member symbol refinement = Gen.node (RefinedSymbol symbol $ refinementFormula refinement) $ pure member

{- | Find the pool entries whose refinement the solver does not prove.

For each entry, the solver decides whether @v .== literal x@ implies the
refinement. The result gives the values for which the answer is not 'Yes', in
pool order. An empty result means that each refinement holds. A query that
reaches the time limit of the solver raises its exception, as 'entails' does.
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
'refinementSubtypingOn'. Within one class, a subtype replaces its supertype;
equivalent refinements keep the earlier entry. Incomparable entries remain.
This operation is opt-in: ordinary QuickCheck pools should keep syntactically
distinct values when broad coverage matters more than semantic representatives.
-}
minimizePoolOn ::
    (Eq key) =>
    Entailment ->
    (a -> key) ->
    [Refined a] ->
    IO (Either GenError (LTAGen a))
minimizePoolOn _ _ [] = pure $ Left EmptyGenerator
minimizePoolOn entailment similarityKey entries = Compile.reportTimeLimit $ do
    inferred <- similarity (refinementSubtypingOn entailment classify) poolAutomaton
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
      where
        poolTransitions =
            [ Transition symbol (refinementFormula refinement) [] noConstraint
            | (symbol, Refined _ _ refinement) <- zip poolSymbols entries
            ]
    -- Equal-width indices make the text order of the symbols the pool order.
    -- 'similarity' pairs the transitions of a node in that order, so of two
    -- equivalent entries it records the earlier one as the subtype.
    poolSymbols = map poolSymbol [0 .. length entries - 1]
      where
        width = length (show (length entries - 1))
        poolSymbol index =
            let digits = show index
             in fromString $ "__microcfta_pool_" <> replicate (width - length digits) '0' <> digits
    classes =
        Map.fromList
            [ (symbol, similarityKey value)
            | (symbol, Refined value _ _) <- zip poolSymbols entries
            ]
    classify transition = Map.lookup (transitionSymbol transition) classes

{- | Keep the terms whose root refinement implies the condition.

Use it where a child is drawn:

@d <- elements [0 .. 5] `satisfying` (\\v -> v ./= 0)@

The condition applies to the root of each term, the constructor that the
generator ends in. A pool, a leaf, a node, an import, a choice of these, and
a mapped generator have such a root. An import with a recursive root is
unfolded once, so the condition does not apply to the recursive occurrences.
On 'every', the condition narrows the values. Another generator gives
'ConditionNeedsConstructor'. The condition can name only @v@ and ambient
names; a relation between children is the contract of 'guarded'. On 'every',
'compile' counts the values, and it does not count an ambient name, so a
condition there names only @v@ and constants.
-}
satisfying :: LTAGen a -> Refinement -> LTAGen a
satisfying generator condition = case generator of
    Transparent (Left err) | err /= SourceRequiresCompilation -> generator
    _ -> case genRecipe generator of
        Closed label constraint child -> deferred (Closed label (conditioned constraint) child)
        ClosedBy labelOf constraint child -> deferred (ClosedBy labelOf (conditioned constraint) child)
        Integers constraint -> deferred (Integers $ conditioned constraint)
        Chosen alternatives -> Flat.frequency [(weight, alternative `satisfying` condition) | (weight, alternative) <- alternatives]
        Uniform alternatives -> Flat.uniformly [alternative `satisfying` condition | alternative <- alternatives]
        Mapped transform inner -> transform <$> (inner `satisfying` condition)
        Imported bound order graph -> case unfoldRoot $ maybe graph (`boundDepth` graph) bound of
            EmptyNode -> generator
            Node transitions ->
                deferConstrained
                    $ Flat.fromAutomaton order
                    $ Node
                        [ Transition symbol refinement children (conditioned constraint)
                        | Transition symbol refinement children constraint <- transitions
                        ]
            _ -> Transparent $ Left ConditionNeedsConstructor
        _ -> Transparent $ Left ConditionNeedsConstructor
  where
    conditioned constraint = constraint `conjoinConstraints` (root `requires` condition)
    -- The children of the unfolded root refer to the recursive node itself,
    -- so the recursive occurrences keep the language of the import.
    unfoldRoot recursive@(Mu _) = unfoldOuterRec recursive
    unfoldRoot other = other
    deferred recipe = withRecipe recipe $ Transparent $ Left SourceRequiresCompilation

{- | Close an applicative child description with one constructor.

With @ApplicativeDo@ and @QualifiedDo@:

@node "divide" $ LTAGen.do ...@

Put a condition on one child where it is drawn, with 'satisfying'. Use
'guarded' for a contract that relates children, and 'measured' to give the
constructed terms a measure that a parent's contract reads.
-}
node :: Symbol -> LTAGen a -> LTAGen a
node symbol = refinedNode symbol (const true) noConstraint

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

{- | Close a child description with a constructor that has a contract and a
measure.

A measure gives each generated term one integer that refinements can read,
defined constructor by constructor. Liquid Haskell calls such a function a
measure. The black height of a red-black tree is one:

@
-- The measure of a tree is its black height.
leaf = LTAGen.leaf Leaf "leaf" (.== 0)
black child =
    LTAGen.measured "black"
        (\\leftHeight rightHeight -> leftHeight .== rightHeight)
        (\\leftHeight _ -> leftHeight + 1)
        (Black \<$\> child \<*\> child)
@

Every node of a term of a liquid tree automaton has one integer, the @v@ of
its refinement. The solver reads only these integers, never the Haskell value.
A leaf gets its integer from its refinement: @(.== 0)@ above says that the
integer of a leaf is 0. A constructor from 'measured' gets its integer from its
measure. What the integer means is the author's choice. Here the leaf, the
@black@ node, and a @red@ node that keeps the height of its subtrees agree that
it is the black height, so the integer of every tree is its black height.
Nothing checks that meaning.

The second argument is the contract, as for 'guarded'. The third argument is
the measure of the constructed term. Both take one term for each child, in
order, and each term is the measure of that child, not its Haskell value. The
leaf above has the measure @0@, from its refinement @v == 0@, and a @black@
term has the measure that its third argument gives. So the contract says that
the two subtrees have equal black heights, and the measure says that the black
height of the new term is one more than that of its left subtree.

The refinement of each constructed term is @\\v -> v .== measure@, so the
contract of a parent and a condition from 'satisfying' read the measure. A
measure does not change the generated value.

Each child that the measure names must have a measure of its own: a
refinement that fixes one integer, as 'elements' and 'leaf' give, an integer
from 'every', or a constructor from 'measured' or 'measuredNode'. The measure
of children from 'every' stays a term of their integers, so a parent's
contract relates it without enumerating them. A child without a measure makes
'compile' report 'InexactMeasure'. The contract and the measure must each take
one term for every child.
-}
measured ::
    (ContractBuilder contract, MeasureBuilder measure) =>
    Symbol ->
    contract ->
    measure ->
    LTAGen a ->
    LTAGen a
measured symbol builder measure child
    | contractArity builder /= spineArity child =
        Transparent $ Left $ InvalidSupport $ GuardArityMismatch symbol (spineArity child) (contractArity builder)
    | otherwise = measuredNode symbol (contract builder) measure child

{- | A recursive description, unfolded a bounded number of times.

The step receives the generator of the previous unfolding and returns the
next one. The first unfolding receives the empty generator, so the recursive
occurrences nest at most the given number of times:

@recurUpTo 3 $ \\self -> oneof [leaf Nil "nil" (const true), node "cons" (Cons <$> elements [1, 2] <*> self)]@

Each unfolding is one shared generator, and 'compile' compiles it once for
each set of observations that its parents read. Bind a generator that a step
uses twice, such as @self@ itself, with @let@ so that the step shares it. A
negative bound gives the empty generator.
-}
recurUpTo :: Depth -> (LTAGen a -> LTAGen a) -> LTAGen a
recurUpTo bound step
    | bound < 0 = empty
    | otherwise = iterate step (step empty) !! fromEnum bound
  where
    empty = Transparent $ Left EmptyGenerator

{- | Close a child description with a constructor that has a refinement and a
positional guard.

This is the form of the transitions in Definition 2 of Mishra and Jagannathan,
/Liquid Tree Automata/ (arXiv:2605.13456): the guard reads the children by
position, as "Data.CFTA.Refinement.Guard" builds it, and the refinement is the
constructor's own result.
-}
refinedNode :: (GuardBuilder guard) => Symbol -> Refinement -> guard -> LTAGen a -> LTAGen a
refinedNode symbol refinement guardBuilder child =
    closeGuarded symbol guardBuilder child (Closed label) $ \constraint ->
        if constraint == noConstraint
            then Just $ Gen.node label child
            else Nothing
  where
    label = RefinedSymbol symbol $ refinementFormula refinement

{- | Close a child description with a constructor that has a positional guard
and a measure.

This is 'refinedNode' with a measure in place of its refinement, and
'measured' with a positional guard in place of a contract. The measure takes
one term for each child, as for 'measured'.
-}
measuredNode ::
    (GuardBuilder guard, MeasureBuilder measure) =>
    Symbol ->
    guard ->
    measure ->
    LTAGen a ->
    LTAGen a
measuredNode symbol guardBuilder measure child
    | measureArity measure /= spineArity child =
        Transparent $ Left $ InvalidSupport $ GuardArityMismatch symbol (spineArity child) (measureArity measure)
    | otherwise = closeGuarded symbol guardBuilder child (ClosedBy labelOf) (const Nothing)
  where
    -- The children's measures replace their names in the measure. A measure
    -- that fixes one integer is that integer.
    labelOf roots =
        let formula =
                substitute
                    [ (contractTermName index, term)
                    | (index, RefinedSymbol _ refinement) <- zip [0 ..] roots
                    , Just term <- [(literal <$> onlyPoint valueName refinement) <|> definingTerm refinement]
                    ]
                    (refinementFormula (.== measureTerm measure))
         in case onlyPoint valueName formula of
                Just value -> Right $ RefinedSymbol symbol $ refinementFormula (.== literal value)
                Nothing
                    | any (`elem` map (contractTermName . ArgumentIndex) [0 .. fromEnum (measureArity measure) - 1]) (freeNames formula) ->
                        Left $ InexactMeasure symbol
                    | otherwise -> Right $ RefinedSymbol symbol formula

{- | Close a child description with a constructor whose refinement is computed
from the labels of its children.

'compile' can call the function more than once for one tuple of child groups, so
the function must be pure. 'validOutcomes' calls it once per candidate. The
function reads exact labels, so a child with values from 'every' gives
'IntegerLeafRead'; use 'measured' for a measure of such children.
-}
refinedNodeByRoots ::
    (GuardBuilder guard) =>
    Symbol ->
    ([Symbol] -> Refinement) ->
    guard ->
    LTAGen a ->
    LTAGen a
refinedNodeByRoots symbol refinementOf guardBuilder child =
    closeGuarded
        symbol
        guardBuilder
        child
        (ClosedBy labelOf)
        (const Nothing)
  where
    labelOf roots
        | any (\(RefinedSymbol _ refinement) -> any Compile.isIntegerName $ freeNames refinement) roots =
            Left $ IntegerLeafRead Nothing
        | otherwise = Right $ RefinedSymbol symbol $ refinementFormula $ refinementOf roots

{- | Close a child description with a guarded constructor.

The guard's argument count must match the child positions. The engine
builds at once each constructor that it can build. 'compile' builds the rest.
-}
closeGuarded ::
    (GuardBuilder guard) =>
    Symbol ->
    guard ->
    LTAGen a ->
    (Constraint -> LTAGen a -> Recipe Symbol a) ->
    (Constraint -> Maybe (LTAGen a)) ->
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
is deferred to 'compile', which prunes it first. An automaton read at once
ranks constructors by arity, then by symbol text and refinement. A compiled
one is split by the labels that its parents read, at least the label of the
root, and ranks the parts by those labels: by symbol text and refinement, with
a constructor before a leaf of the same symbol. Arity orders the constructors
within one part.
-}
fromAutomaton :: Automaton -> LTAGen (Tree.Tree Symbol)
fromAutomaton = deferConstrained . Flat.fromAutomaton liquidOrder

-- | Read the terms a liquid automaton accepts up to a constructor-depth bound. A leaf has depth zero.
fromAutomatonUpToDepth :: Depth -> Automaton -> LTAGen (Tree.Tree Symbol)
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
values; the constructor terms keep their ranks. Ranks order the constructors
of a type by arity, then in declaration order, and atomic literals in domain
order, as 'Data.CFTA.Gen.fromDatatype' does. When the guards need 'compile',
the compiled generator ranks the root constructors by the text and refinement
of their labels instead, as 'fromAutomaton' says. A codec that rejects a term
of its own grammar gives 'UndecodableConstructor'.
-}
fromDatatypeUpToDepth :: Depth -> TypedFTA (Refinement, Constraint) a -> LTAGen a
fromDatatypeUpToDepth depth datatype =
    case validate graph of
        Left err -> Transparent $ Left $ InvalidSupport err
        Right ()
            | Just constructor <- undecodableConstructor (null . datatypeDecode datatype) (datatypeFTA datatype) ->
                Transparent $ Left $ UndecodableConstructor $ constructorName constructor
            | otherwise -> decode <$> deferConstrained (Flat.fromAutomatonUpToDepth key depth graph)
  where
    order = declarationOrder datatype
    key symbol@(RefinedSymbol (Symbol name) _) = (order name, liquidOrder symbol)
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
    decodeValue = datatypeDecoder datatype
    decode term =
        case decodeValue $ eraseRefinements term of
            Just value -> value
            Nothing ->
                error
                    "microcfta-generator bug in Data.CFTA.Gen.Refinement.fromDatatypeUpToDepth: \
                    \the derived codec rejected a term of its own grammar"

{- | Compile a generator with Z3.

The solver decides every guard, condition, and contract once, and the result
is an ordinary generator: finite, or recursive for a recursive import. The
call fails with the 'explain' text of the error when the generator cannot be
compiled. A product with an empty part is empty, and its other parts are not
compiled, so their errors are not reported; 'validOutcomes' reports them. Each
free name in a refinement is an integer.
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
