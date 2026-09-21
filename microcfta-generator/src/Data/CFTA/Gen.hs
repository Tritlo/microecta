{- | Generators over constrained tree automata.

A generator is a language of values whose support is an interned automaton
with edges of type @symbol@ and constraints of type @constraint@. The theory
of the automaton is the constraint type: @()@ for an ordinary tree automaton,
'Data.CFTA.Equality.Constraint.EqConstraints' for equalities between child
paths, and 'Data.CFTA.Refinement.Constraint.LiquidConstraint' for refinements
decided by a solver. Every value stands for a term the automaton accepts, so
the language is counted, replayed by rank, sampled, and shrunk exactly.

A finite generator has a 'cardinality' and one rank per distinct member. It
comes from a source ('elements', 'leaf', 'fromIndexed'), from applicative
composition closed by 'node', from a choice ('frequency', 'oneof'), from a
join ('match', 'relate', 'apply'), or from an acyclic automaton
('fromAutomaton'). A recursive generator ('recur', or 'fromAutomaton' on a
cyclic automaton) is counted by size; 'upToSize' bounds it to a finite one.
An opaque generator ('fromGen') can only be sampled. A construction failure
stays inside the generator, and every inspector reports it.

"Data.CFTA.Gen.QuickCheck" adds sampling and properties, and
"Data.CFTA.Gen.Do" adds qualified applicative do-notation.
-}
module Data.CFTA.Gen (
    -- * Generators
    Gen,
    Grouped,
    Label (..),
    GenError (..),
    explain,

    -- * Sources
    Indexed (..),
    fromIndexed,
    elements,
    namedElements,
    leaf,
    fromGen,

    -- * Imported automata and datatypes
    fromAutomaton,
    fromAutomatonUpToDepth,
    fromDatatype,
    fromDatatypeUpToDepth,

    -- * Composing
    NodeLayer,
    node,
    frequency,
    oneof,
    uniformly,
    On (..),
    match,
    relate,
    relateM,

    -- * The grouped layer
    Sig (..),
    sigResult,
    Args (..),
    keyed,
    groupBy,
    regroupBy,
    mapWithKey,
    nameGroups,
    atKey,
    apply,
    frequencies,
    oneofGrouped,
    uniformlyGrouped,
    ungroup,
    relateGroupsM,
    relateN,
    filterGroupsM,

    -- * Recursion
    atomic,
    recur,
    recurGrouped,
    upToSize,
    isRecursive,
    isOpaque,

    -- * Inspection
    Inspection (..),
    InspectionSymbol (..),
    inspect,
    support,
    cardinality,
    sizes,
    countsAtSize,
    massesAtSize,
    countAtSize,
    minimumSize,
    countBy,
    pmf,
    pmfAtSize,
    smallest,
    unrank,
    termAt,
    sizeOfRank,
    smallerMembers,
    shrinkRank,

    -- * Lowering
    lower,
    lowerWithRank,
    lowerUniform,
    lowerUniformWithRank,
    lowerVia,
    lowerWithRankVia,
) where

import Data.Hashable (Hashable)
import Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint)
import Data.CFTA.Gen.Equality.Internal.Flat hiding (fromAutomaton, fromAutomatonUpToDepth)
import qualified Data.CFTA.Gen.Equality.Internal.Flat as Flat
import Data.CFTA.Gen.Equality.Internal.Grouped
import Data.CFTA.Gen.Equality.Internal.Inspect
import Data.CFTA.Gen.Equality.Internal.Inspection (Inspection (..), InspectionSymbol (..))
import Data.CFTA.Gen.Equality.Internal.Recursion
import Data.CFTA.Gen.Equality.Internal.Types
import Data.CFTA.Gen.Equality.Sig (On (..), Sig (..), sigResult)
import Data.CFTA.Gen.Error
import Data.CFTA.Gen.Label (Label (..))
import Data.CFTA.Generic (TypedFTA, constructorLabel, datatypeFTA, decodeLabelledTerm)
import Data.CFTA.Interned (Node)
import qualified Data.CFTA.Interned as Common
import Data.CFTA.Ranked.Internal (Indexed (..))
import Data.CFTA.Refinement (AutomatonError (InconsistentArity))
import Data.CFTA.Symbol (Symbol (Symbol))

-- | Build one nullary constructor.
leaf :: (Constraint constraint, Hashable symbol, Typeable symbol) => a -> symbol -> Gen symbol constraint a
leaf value symbol = node symbol $ pure value

{- | Read an automaton as a generator of the terms it accepts.

The automaton is the support, unchanged. An acyclic automaton gives a finite
generator with one rank per distinct term; where alternatives overlap or an
equality reaches below direct children, the count is symbolic and ranks order
constructors by the symbol's 'Ord'. A cyclic automaton gives a recursive
generator counted by size, the number of term nodes, so 'upToSize' draws
uniformly from the terms of at most a given size. Its count sums over
accepting runs, so an ambiguous automaton is rejected with
'AmbiguousAutomaton' and one with equality constraints with
'CannotCountConstrainedEdges'. Because the values are the accepted terms, a
bounded generator keeps full inspection.
-}
fromAutomaton ::
    (Constraint constraint, Ord symbol, Hashable symbol, Typeable symbol) =>
    Node symbol constraint -> Gen symbol constraint (Tree.Tree symbol)
fromAutomaton = Flat.fromAutomaton id

{- | Read the terms an automaton accepts up to a constructor-depth bound.

A leaf has depth zero. The result is the finite generator 'fromAutomaton'
gives for an acyclic automaton: each distinct term has one rank, unranking
constructs only the selected term, and shrinks remain in the language.
-}
fromAutomatonUpToDepth ::
    (Constraint constraint, Ord symbol, Hashable symbol, Typeable symbol) =>
    Int -> Node symbol constraint -> Gen symbol constraint (Tree.Tree symbol)
fromAutomatonUpToDepth = Flat.fromAutomatonUpToDepth id

{- | Read a datatype grammar as a generator of its values.

The generator is recursive when the datatype is, and finite otherwise. The
value and its constructor term share one rank, and the codec runs only when a
selected value is demanded. Constructor symbols carry the type and constructor
name, and symbolic ranks order them by that text.
-}
fromDatatype :: (Constraint constraint) => TypedFTA constraint a -> Gen Symbol constraint a
fromDatatype datatype = importDatatype datatype $ Flat.fromAutomaton symbolText

{- | Generate datatype values up to a constructor depth. A leaf has depth zero.

An annotated constructor generates only the values whose equal fields agree.
-}
fromDatatypeUpToDepth :: (Constraint constraint) => Int -> TypedFTA constraint a -> Gen Symbol constraint a
fromDatatypeUpToDepth depth datatype =
    importDatatype datatype $ Flat.fromAutomatonUpToDepth symbolText depth

-- | The text of a symbol, the order in which symbolic counts rank constructors.
symbolText :: Symbol -> Text
symbolText (Symbol name) = name

-- | Import the grammar of a datatype and decode its terms as values.
importDatatype ::
    (Constraint constraint) =>
    TypedFTA constraint a ->
    (Node Symbol constraint -> Gen Symbol constraint (Tree.Tree Symbol)) ->
    Gen Symbol constraint a
importDatatype datatype readAutomaton =
    case FTA.mapSymbols (fromString . constructorLabel) (datatypeFTA datatype) of
        Left (FTA.InconsistentArity symbol expected actual) ->
            Transparent $ Left $ InvalidSupport $ InconsistentArity symbol expected actual
        Left err ->
            error $ "microcfta-generator bug in Data.CFTA.Gen.importDatatype: " <> show err
        Right graph -> decode <$> readAutomaton (Common.fromFTA graph)
  where
    decode term = case decodeLabelledTerm datatype (fmap (\(Symbol label) -> Text.unpack label) term) of
        Just value -> value
        Nothing ->
            error
                "microcfta-generator bug in Data.CFTA.Gen.importDatatype: \
                \the derived codec rejected a term of its own grammar"
