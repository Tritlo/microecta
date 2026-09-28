{- | Generators over constrained tree automata.

A generator is a language of values whose support is an interned automaton
with edges of type @symbol@. Every edge carries a
'Data.CFTA.Constraint.Constraint': none for an ordinary tree automaton,
equalities between child paths for an equality automaton, and guards that a
solver decides for a liquid automaton. Every value stands for a term the
automaton accepts, so the language is counted, replayed by rank, sampled, and
shrunk exactly.

An ordinary generator, one over a plain tree automaton, is 'FTAGen';
"Data.CFTA.Gen.Equality" and "Data.CFTA.Gen.Refinement" fix the other two
theories the same way.

A finite generator has a 'cardinality' and one rank per member. Equal values
from 'elements' are separate members with separate ranks. It comes from a source
('elements', 'leaf', 'fromIndexed'), from applicative composition closed by
'node', from a choice ('frequency', 'oneof'), from a join ('match', 'relate',
'apply'), or from an acyclic automaton ('fromAutomaton'). A recursive generator
('recur', or 'fromAutomaton' on a cyclic automaton) is counted by size;
'upToSize' bounds it to a finite one. An opaque generator ('fromGen') can only
be sampled. A construction failure stays inside the generator, and every
inspector reports it.

"Data.CFTA.Gen.QuickCheck" adds sampling and properties, and
"Data.CFTA.Gen.Do" adds qualified applicative do-notation.
-}
module Data.CFTA.Gen (
    -- * Generators
    Gen,
    FTAGen,
    Grouped,
    Label (..),
    surface,
    GenError (..),
    explain,
    orFail,

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
    groupOn,
    regroupOn,
    mapWithKey,
    nameGroups,
    atKey,
    nodeWithKey,
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
    drawInspection,
    support,
    cardinality,
    values,
    sizes,
    countsAtSize,
    massesAtSize,
    countAtSize,
    minimumSize,
    countOn,
    pmf,
    pmfAtSize,
    smallest,
    unrank,
    termAt,
    rankOf,
    ranksOf,
    rankOfTerm,
    rankOfValue,
    sizeOfRank,
    smallerMembers,
    shrinkRank,

    -- * Lowering
    RankedValue (..),
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
import Data.CFTA.Gen.Error
import Data.CFTA.Gen.Internal.Automaton (declarationOrder, undecodableConstructor)
import Data.CFTA.Gen.Internal.Flat hiding (fromAutomaton, fromAutomatonUpToDepth)
import qualified Data.CFTA.Gen.Internal.Flat as Flat
import Data.CFTA.Gen.Internal.Grouped
import Data.CFTA.Gen.Internal.Inspection (Inspection (..), InspectionSymbol (..), drawInspection)
import Data.CFTA.Gen.Internal.Query
import Data.CFTA.Gen.Internal.Recur
import Data.CFTA.Gen.Internal.Types
import Data.CFTA.Gen.Label (Label (..), surface)
import Data.CFTA.Gen.Sig (On (..), Sig (..), sigResult)
import Data.CFTA.Generic (
    HasFTA (encodeTerm),
    TypedFTA,
    constructorLabel,
    constructorName,
    datatypeDecode,
    datatypeFTA,
    decodeLabelledTerm,
 )
import Data.CFTA.Index (Depth, Rank)
import Data.CFTA.Interned (Node)
import qualified Data.CFTA.Interned as Common
import Data.CFTA.Ranked.Internal (Indexed (..))
import Data.CFTA.Ranked.Internal.Decoder (RankedValue (..))
import Data.CFTA.Refinement (AutomatonError (InconsistentArity))
import Data.CFTA.Symbol (Symbol (Symbol))

-- | A generator over ordinary tree automata: the theory without constraints.
type FTAGen symbol = Gen symbol

-- | Build one nullary constructor.
leaf :: (Hashable symbol, Typeable symbol) => a -> symbol -> Gen symbol a
leaf value symbol = node symbol $ pure value

{- | Read an automaton as a generator of the terms it accepts.

The automaton is the support, unchanged. An acyclic automaton gives a finite
generator with one rank per distinct term. Where alternatives overlap or an
equality reaches below direct children, the count is symbolic.

Ranks order constructors by arity, then by the 'Ord' of the symbol. 'Symbol'
orders by text, so ranks do not depend on the order in which the process
interned the symbols. Alternatives with the same symbol and arity are ordered
by the structure of their children, in an acyclic and in a cyclic automaton, so
their ranks do not depend on interning order either. Nullary constructors come
first, so shrinking moves toward leaves.

A cyclic automaton gives a recursive generator counted by size, the number of
term nodes, so 'upToSize' draws uniformly from the terms of at most a given
size. The count sums over accepting runs. An ambiguous automaton is therefore
rejected with 'AmbiguousAutomaton', and one with equality constraints with
'CannotCountConstrainedEdges'.

The values are the accepted terms, so a bounded generator keeps full
inspection. The bounded form keeps the terms, the support, and the inspection
graph. 'support', 'inspect', 'termAt', and 'ranksOf' work on it.
-}
fromAutomaton ::
    (Ord symbol, Hashable symbol, Typeable symbol) =>
    Node symbol -> Gen symbol (Tree.Tree symbol)
fromAutomaton = Flat.fromAutomaton id

{- | Read the terms an automaton accepts up to a constructor-depth bound.

A leaf has depth zero. The result is the finite generator 'fromAutomaton'
gives for an acyclic automaton: each distinct term has one rank, unranking
constructs only the selected term, and shrinks remain in the language.
-}
fromAutomatonUpToDepth ::
    (Ord symbol, Hashable symbol, Typeable symbol) =>
    Depth -> Node symbol -> Gen symbol (Tree.Tree symbol)
fromAutomatonUpToDepth = Flat.fromAutomatonUpToDepth id

{- | Read a datatype grammar as a generator of its values.

The generator is recursive when the datatype is, and finite otherwise. The
value and its constructor term share one rank, and the codec runs only when a
selected value is demanded. Ranks order the constructors of a type by arity,
then in declaration order, and atomic literals in domain order. The derived
grammar keeps its rows in that order, and a label is in the row of its own type
only.

The generator decodes one term per constructor when it is built. If the codec
rejects one, the generator fails with 'UndecodableConstructor'. This happens
for an atomic literal whose 'Show' text 'Read' does not accept.
-}
fromDatatype :: TypedFTA Constraint a -> Gen Symbol a
fromDatatype datatype = importDatatype datatype Flat.fromAutomaton

{- | The least rank of a datatype value in a generator from 'fromDatatype' or
'fromDatatypeUpToDepth'. The codec of the type encodes the value as a
constructor term. 'ranksOf' lists the ranks of a term in ascending order, so
this is its first rank. A value that the generator does not give has
'TermNotInLanguage'.
-}
rankOfValue :: (HasFTA a) => Gen Symbol a -> a -> Either GenError Rank
rankOfValue generator = rankOfTerm generator . fmap (fromString . constructorLabel) . encodeTerm

{- | Generate datatype values up to a constructor depth. A leaf has depth zero.

An annotated constructor generates only the values whose equal fields agree.
-}
fromDatatypeUpToDepth :: Depth -> TypedFTA Constraint a -> Gen Symbol a
fromDatatypeUpToDepth depth datatype =
    importDatatype datatype $ \order -> Flat.fromAutomatonUpToDepth order depth

{- | Import the grammar of a datatype and decode its terms as values.

The key is 'declarationOrder'. The import orders by arity before it uses
the key.
-}
importDatatype ::
    TypedFTA Constraint a ->
    ((Symbol -> (Int, Text)) -> Node Symbol -> Gen Symbol (Tree.Tree Symbol)) ->
    Gen Symbol a
importDatatype datatype readAutomaton =
    case FTA.mapSymbols (fromString . constructorLabel) (datatypeFTA datatype) of
        Left (FTA.InconsistentArity symbol expected actual) ->
            Transparent $ Left $ InvalidSupport $ InconsistentArity symbol expected actual
        Left err ->
            error $ "microcfta-generator bug in Data.CFTA.Gen.importDatatype: " <> show err
        Right graph
            | Just constructor <-
                undecodableConstructor (null . datatypeDecode datatype) (datatypeFTA datatype) ->
                Transparent $ Left $ UndecodableConstructor $ constructorName constructor
            | otherwise -> decode <$> readAutomaton (\(Symbol name) -> order name) (Common.fromFTA graph)
  where
    order = declarationOrder datatype
    decode term = case decodeLabelledTerm datatype (fmap (\(Symbol label) -> Text.unpack label) term) of
        Just value -> value
        Nothing ->
            error
                "microcfta-generator bug in Data.CFTA.Gen.importDatatype: \
                \the derived codec rejected a term of its own grammar"
