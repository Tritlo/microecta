{- | Indexed generators whose transparent regions are represented as ECTAs.

An indexed source stores a finite cardinality and a function from indices to
values. Applicative composition tracks exact cardinalities and rank-based
selection alongside the ECTA, without materializing the product language.
Joins count matched group products and unrank directly within them. A
construction failure stays inside the generator; 'cardinality' and
'Data.CFTA.Gen.Equality.QuickCheck.toGen' report it.

This module is the generator engine at the symbol type 'Symbol'. A support
is an automaton over 'Label': the user's symbols, closed with 'node' or read
from an imported automaton, and the private labels of the engine. The engine
reserves no symbol names.
-}
module Data.CFTA.Gen.Equality (
    -- * Generators
    ECTAGen,
    Grouped,
    Label (..),
    GenError (..),
    explain,

    -- * Sources
    Indexed (..),
    fromIndexed,
    elements,
    namedElements,
    fromAutomaton,
    fromAutomatonUpToDepth,
    fromDatatypeUpToDepth,
    fromGen,

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

import qualified Data.Map.Strict as Map
import Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Tree as Tree
import qualified Test.QuickCheck as QC

import qualified Data.CFTA as FTA
import Data.CFTA.Equality (Node)
import Data.CFTA.Equality.Constraint (EqConstraints)
import qualified Data.CFTA.Gen.Equality.Internal.Flat as Engine
import qualified Data.CFTA.Gen.Equality.Internal.Grouped as Engine
import qualified Data.CFTA.Gen.Equality.Internal.Inspect as Engine
import Data.CFTA.Gen.Equality.Internal.Inspection (Inspection (..), InspectionSymbol (..))
import qualified Data.CFTA.Gen.Equality.Internal.Recursion as Engine
import Data.CFTA.Gen.Equality.Internal.Types (Args (..), Gen (Transparent), NodeLayer)
import qualified Data.CFTA.Gen.Equality.Internal.Types as Engine
import Data.CFTA.Gen.Equality.Sig (On (..), Sig (..), sigResult)
import Data.CFTA.Gen.Error
import Data.CFTA.Gen.Label (Label (..))
import Data.CFTA.Generic (TypedFTA, constructorLabel, datatypeFTA, decodeLabelledTerm)
import qualified Data.CFTA.Interned as Common
import Data.CFTA.Ranked.Internal (Indexed (..))
import Data.CFTA.Ranked.Internal.Sampler (GenBackend)
import Data.CFTA.Refinement (AutomatonError (InconsistentArity))
import Data.CFTA.Symbol (Symbol (Symbol))

{- | A generator is inspectable ECTA structure — finite or recursive — or an
opaque QuickCheck generator.
-}
type ECTAGen = Gen Symbol

{- | A transparent generator whose values are classified by a projected key.

The key is not part of the generated value. It classifies values into groups;
during a join, matching key values determine which groups receive equal internal
labels on constrained ECTA paths. Each key group retains compact ECTA support
and indexed selection without storing all outcomes.
-}
type Grouped = Engine.Grouped Symbol

-- | The text of a symbol, the order in which symbolic counts rank constructors.
symbolText :: Symbol -> Text
symbolText (Symbol name) = name

-- | Lift one finite indexed source into transparent ECTA structure.
fromIndexed :: Indexed a -> ECTAGen a
fromIndexed = Engine.fromIndexed

-- | Embed an ordinary QuickCheck generator as an opaque region.
fromGen :: QC.Gen a -> ECTAGen a
fromGen = Engine.fromGen

{- | Read an ECTA as a generator of the terms it accepts.

The automaton is the support, unchanged, and members are counted by size —
the number of term nodes — so the generator draws uniformly from the terms
of at most a given size, recursive @Mu@ nodes included. Because the values
are the accepted terms, a bounded generator keeps full inspection: 'pmf',
'countBy', and 'groupBy' all work on it.

Equality constraints are not counted: they correlate an edge's children, so
its count is the size of an intersection rather than a product, and an
automaton carrying them is rejected with 'CannotCountConstrainedEdges'
rather than miscounted.

Ambiguity is not counted either. A node's count sums over its edges, which
counts accepting runs, so a node with two edges accepting a common term would
count that term twice and report it at two ranks. Such an automaton is
rejected with 'AmbiguousAutomaton'.
-}
fromAutomaton :: Node Symbol EqConstraints -> ECTAGen (Tree.Tree Symbol)
fromAutomaton = Engine.fromAutomaton

{- | Compile an equality-constrained automaton up to a constructor-depth bound.

A leaf has depth zero. Each distinct accepted term has one rank, and sampling
is uniform over these ranks. Direct child equalities use shared rank plans.
Nested equality paths and overlapping alternatives use symbolic counts over
shared states, whose ranks order constructors by their text. Unranking
constructs only the selected term. Shrinks remain in the accepted language.
-}
fromAutomatonUpToDepth :: Int -> Node Symbol EqConstraints -> ECTAGen (Tree.Tree Symbol)
fromAutomatonUpToDepth = Engine.fromAutomatonUpToDepth symbolText

-- | Generate typed values from a datatype grammar with equality annotations.
fromDatatypeUpToDepth :: Int -> TypedFTA EqConstraints a -> ECTAGen a
fromDatatypeUpToDepth depth datatype =
    case FTA.mapSymbols (fromString . constructorLabel) (datatypeFTA datatype) of
        Left (FTA.InconsistentArity symbol expected actual) ->
            Transparent $ Left $ InvalidSupport $ InconsistentArity symbol expected actual
        Left err ->
            error $ "microcfta-generator bug in Data.CFTA.Gen.Equality.fromDatatypeUpToDepth: " <> show err
        Right graph -> decode <$> fromAutomatonUpToDepth depth (Common.fromFTA graph)
  where
    decode term = case decodeLabelledTerm datatype (fmap (\(Symbol label) -> Text.unpack label) term) of
        Just value -> value
        Nothing ->
            error
                "microcfta-generator bug in Data.CFTA.Gen.Equality.fromDatatypeUpToDepth: \
                \the derived codec rejected a term of its own grammar"

-- | Choose uniformly from a finite non-empty list.
elements :: [a] -> ECTAGen a
elements = Engine.elements

{- | Choose uniformly from named source values.

Names are retained for inspection and may describe functions. They do not
change the support symbols, rank order, weights, or values. Mapping a source
preserves its source names; it does not claim to name the mapped results.
-}
namedElements :: [(Text, a)] -> ECTAGen a
namedElements = Engine.namedElements

{- | Close an applicative child description with one domain constructor.

Instances cover ordinary and grouped ECTA generators. The grouped instance
keeps its result key and equality constraints while replacing the generator's
private join label with the supplied domain symbol.
-}
node :: (NodeLayer Symbol layer) => Symbol -> layer a -> layer a
node = Engine.node

-- | Choose one generator with the supplied positive relative weight.
frequency :: [(Integer, ECTAGen a)] -> ECTAGen a
frequency = Engine.frequency

{- | Choose uniformly among generators.

Every alternative is equally likely, whatever the size of its language, as
in QuickCheck's own @oneof@. In a recursive definition this is the shape to
reach for: weights around a recursive occurrence are rejected, because such
a language uses structural counts for global size selection and rank offsets.
A finite choice closed with 'atomic' can still retain its own sampler mass
within the selected size.
-}
oneof :: [ECTAGen a] -> ECTAGen a
oneof = Engine.oneof

{- | Choose among generators so that every member of the combined language is
equally likely.

Finite alternatives are combined in proportion to their cardinalities. An
alternative with no members is dropped, as is one whose construction failed
with 'EmptyGenerator'; any other failure is reported, including an opaque
alternative, which has no cardinality to weight by. A recursive alternative
makes this 'oneof': a recursive language has no cardinality either, and its
size-class sampler already draws every member of a size class equally.

An alternative that is itself weighted keeps its own distribution, so members
are equally likely exactly when each alternative is uniform.
-}
uniformly :: [ECTAGen a] -> ECTAGen a
uniformly = Engine.uniformly

-- | Generate two values whose projected keys agree.
match :: On left right -> ECTAGen left -> ECTAGen right -> ECTAGen (left, right)
match = Engine.match

{- | Generate two values whose projected keys satisfy a relation.

For finite inspectable inputs, the relation is evaluated once per live key
pair. The accepted group products are counted and sampled directly without
rejection. The key types may differ, and the relation need not be symmetric.
The relation must be total for every live key pair. An opaque input uses
QuickCheck rejection filtering instead.
-}
relate ::
    (Ord leftKey, Ord rightKey) =>
    (left -> leftKey) ->
    (right -> rightKey) ->
    (leftKey -> rightKey -> Bool) ->
    ECTAGen left ->
    ECTAGen right ->
    ECTAGen (left, right)
relate = Engine.relate

{- | Compile an effectful relation between two finite inspectable languages.

Each input is grouped once by its projected key. The callback then runs once
per live key pair, not once per value pair. Accepted pairs are lowered through
'relateGroupsM' to the same ECTA equality join used by grouped application.
The outer 'Either' is reserved for a caller-defined relation failure, such as
an undecided solver query; generator construction failures remain inspectable
through the returned 'ECTAGen'. Recursive and opaque inputs are rejected by
the grouped layer rather than sampled by rejection.
-}
relateM ::
    (Ord leftKey, Ord rightKey) =>
    (left -> leftKey) ->
    (right -> rightKey) ->
    (leftKey -> rightKey -> IO (Either relationError Bool)) ->
    ECTAGen left ->
    ECTAGen right ->
    IO (Either relationError (ECTAGen (left, right)))
relateM = Engine.relateM

{- | Declare that every member of an inspectable generator has one key.

This enters the grouped layer without enumerating members. It preserves a
finite or recursive generator's support, ranks, and distribution unchanged.
Use 'groupBy' when the key must be computed from each member. Opaque generators
cannot be keyed because they have no inspectable support or rank index.
-}
keyed :: key -> ECTAGen a -> Grouped key a
keyed = Engine.keyed

{- | Classify a transparent generator's outcomes by a projected key.

This is the boundary from flat to grouped generation: any transparent
generator can be grouped, including 'frequency'-weighted sources and 'match'
results. Building the groups enumerates the generator's outcomes once. Keys
are ordered by their 'Ord' instance; outcomes within each key retain their
rank order. Opaque generators cannot be grouped.
-}
groupBy :: (Ord key) => (a -> key) -> ECTAGen a -> Grouped key a
groupBy = Engine.groupBy

{- | Reclassify the groups without enumerating their values.

When several old keys map to one new key, their compact supports are merged and
their probability masses are preserved. Previous group names are cleared;
use 'nameGroups' to name the new keys. Source descriptions remain available.
-}
regroupBy :: (Ord newKey) => (oldKey -> newKey) -> Grouped oldKey a -> Grouped newKey a
regroupBy = Engine.regroupBy

-- | Map group values with access to their retained key.
mapWithKey :: (key -> a -> b) -> Grouped key a -> Grouped key b
mapWithKey = Engine.mapWithKey

{- | Retain a display name for each group without inspecting its members.

Names describe the retained keys. They do not affect key comparison, support,
ranks, or generated values. Formatting runs only when inspection needs it.
-}
nameGroups :: (key -> Text) -> Grouped key a -> Grouped key a
nameGroups = Engine.nameGroups

{- | Select one retained group as an ordinary conditional generator.

A missing key produces 'EmptyGenerator'.
-}
atKey :: (Ord key) => key -> Grouped key a -> ECTAGen a
atKey = Engine.atKey

-- | Merge all retained groups while preserving their probability masses.
ungroup :: Grouped key a -> ECTAGen a
ungroup = Engine.ungroup

{- | Apply a generated operation of any arity to one argument family per
signature component, retaining the operation's result group.

The operation family must already hold functions consuming the 'Args' chain
left to right; use 'fmap' to attach a compiling function. Every matched
component joins the operation group and all
argument groups in one ECTA edge holding one equality constraint per argument.
Ranks are ordered by result key, then signature, then operation rank, then
argument ranks left to right.
-}
apply ::
    (Ord resultKey) =>
    Grouped (Sig argKeys resultKey) operation ->
    Args Symbol argKeys operation result ->
    Grouped resultKey result
apply = Engine.apply

{- | Choose among grouped generators with positive relative weights,
group by group.

Every key present in any alternative is retained. Within one key, the group
is the weighted mixture of that key's groups across the alternatives; a key
missing from an alternative simply contributes nothing to it. Ranks within a
merged group are ordered by alternative order, then by the inner rank.
-}
frequencies :: (Ord key) => [(Integer, Grouped key a)] -> Grouped key a
frequencies = Engine.frequencies

{- | Choose uniformly among grouped generators, group by group.

'frequencies' with equal weights, which is the only shape a recursive
family admits.
-}
oneofGrouped :: (Ord key) => [Grouped key a] -> Grouped key a
oneofGrouped = Engine.oneofGrouped

{- | Choose among grouped generators so that every member of the combined
language is equally likely.

Finite alternatives are combined in proportion to their exact cardinalities,
the sum of their 'sizes'. An alternative with no members is dropped, as is one
whose construction failed with 'EmptyGenerator'; any other failure is
reported. A recursive family has no cardinality, and its size-class sampler
already draws every member of a size class equally, so alternatives around one
are combined with equal weights, as 'oneofGrouped' does.

An alternative that is itself weighted keeps its own distribution, so members
are equally likely exactly when each alternative is uniform.
-}
uniformlyGrouped :: (Ord key) => [Grouped key a] -> Grouped key a
uniformlyGrouped = Engine.uniformlyGrouped

{- | Compile an effectful relation directly over two grouped languages.

This is the non-enumerating boundary used by higher-level relational
compilers. One solver decision selects or rejects each pair of already
materialized keys. A selected component keeps both compact bucket indexes and
encodes their membership with the ECTA n-ary equality join; no bucket member
is visited. The result key may be computed from both input keys.
-}
relateGroupsM ::
    (Ord resultKey) =>
    (leftKey -> rightKey -> IO (Either relationError Bool)) ->
    (leftKey -> rightKey -> resultKey) ->
    Grouped leftKey left ->
    Grouped rightKey right ->
    IO (Either relationError (Grouped resultKey (left, right)))
relateGroupsM = Engine.relateGroupsM

{- | Compile one relation over a homogeneous list of grouped arguments.

Intermediate products range over key tuples only. The relation is evaluated
once for every live complete tuple, while the values under each tuple remain
in their compact ECTA indexes. The result stays grouped by that tuple so a
caller can reclassify it without enumerating members.
-}
relateN ::
    (Ord key) =>
    ([key] -> IO (Either relationError Bool)) ->
    [Grouped key a] ->
    IO (Either relationError (Grouped [key] [a]))
relateN = Engine.relateN

-- | Retain complete groups selected by one effectful key predicate.
filterGroupsM ::
    (Ord key) =>
    (key -> IO (Either relationError Bool)) ->
    Grouped key a ->
    IO (Either relationError (Grouped key a))
filterGroupsM = Engine.filterGroupsM

{- | Treat every member of a finite generator as one atomic source choice.

An already finite generator keeps its support, cardinality, ranks, values,
and distribution. Only size changes: every complete member has size one when
it is used inside 'recur'. Its finite distribution is also used when sampling
that recursive language. Put 'atomic' around the complete finite choice that
enters recursion; a finite composition outside the boundary is a new choice
and needs its own boundary. An acyclic automaton read with 'fromAutomaton' closes
its whole finite language without enumerating its terms, rather than taking
an inner prefix from the QuickCheck size. Bound a recursive language with
'upToSize' before making it atomic, /outside/ the recursive definition:
@atomic (upToSize n self)@ inside a 'recur' body asks for an atom whose
cardinality depends on itself, and is rejected with
'BoundedRecursiveOccurrence'. Opaque generators have no size structure to
change.
-}
atomic :: ECTAGen a -> ECTAGen a
atomic = Engine.atomic

{- | Build a recursive generator from its own language.

The argument receives the generator being defined and returns its body, so
a language can refer to itself:

@
tree = ECTAGen.recur $ \\self ->
    ECTAGen.frequency
        [ (1, Leaf '<$>' ECTAGen.elements [0 .. 3])
        , (1, Branch '<$>' self '<*>' self)
        ]
@

The result stands for the whole unbounded language: it has size classes and
size-major ranks instead of a cardinality, and its ECTA support is a @Mu@
node. 'upToSize' bounds it back to an ordinary finite generator, and the
QuickCheck adapter does that automatically from the size parameter. A keyed
language recurses with 'recurGrouped' instead.

The self-reference has to go through this combinator. A generator that
names itself directly, as in @tree = Branch '<$>' tree '<*>' tree@, is an
infinite Haskell value: building it never finishes, and the failure is a
hang or @\<\<loop\>\>@ rather than anything this library can report. In the
other direction, a body that never uses the argument is not recursive, and
is returned as it is: a finite body stays a finite generator, with the
cardinality and the inspection that come with it. A body that could not be
built at all is returned with its own error, not as a recursive language.

'upToSize' and 'atomic' cannot be applied to the argument, or to anything
built from it: the bound would need the size classes this definition is still
computing, and an atom over them would have a cardinality depending on itself.
Both shapes are rejected with 'BoundedRecursiveOccurrence'. Bound the finished
language from outside instead, as in @upToSize n (recur ...)@, and keep only
finite atomic choices inside the body.

Two rules apply inside the knot. The recursion must be guarded — every
occurrence of the argument under at least one '<*>' — or the language has no
smallest member; an unguarded definition is rejected with
'UnguardedRecursion' rather than left to diverge. The check is per definition,
so inside a nested 'recur' an occurrence of the /outer/ language must also sit
under an application within the inner body. 'pure' is one source choice, so
@pure f '<*>' self@ counts as guarded where @f '<$>' self@ does not - and
@pure f '<*>' x@ has one more choice than @f '<$>' x@, so the two have
different sizes and different ranks. A recursive language also
needs a finite base member; a guarded cycle with no base is an 'EmptyGenerator'.
Recursive structure is
chosen from its counted size classes, so 'frequency' alternatives around a
recursive occurrence must carry equal weights; 'oneof' is the combinator that
already reads that way, and the size bound controls how large members get. A
weighted finite choice closed with 'atomic' keeps its distribution inside
each recursive size class without changing counts, sizes, or ranks.
-}
recur :: (ECTAGen a -> ECTAGen a) -> ECTAGen a
recur = Engine.recur

{- | Build a recursive grouped family from its own languages.

The argument receives the family being defined, so a keyed language can
refer to itself — which is what a recursively typed expression language
needs:

@
expressions = ECTAGen.recurGrouped $ \self ->
    ECTAGen.frequencies
        [ (1, literalsByType)
        , (1, ECTAGen.apply (compileBinary '<$>' binaryFunctionsBySignature) (self ':&' self ':&' 'ANil'))
        ]
@

Which keys the family has is itself part of the fixpoint, so it is solved
first, from the empty family upward: each pass adds the result keys of the
operations whose argument keys are already present, and the set can only
grow, so it converges in at most one pass per key. The languages are then
tied lazily over that fixed set.

The reachable key set must be finite. For example,
@oneofGrouped [keyed 0 atom, regroupBy succ self]@ adds another key on every
pass and therefore cannot converge.

All the keys share one @Mu@ node, whose edges carry their key as a first
child. An occurrence at one key is that node under an edge holding the
key's label, with an equality constraint tying the two — so a recursive
family is one recursive automaton whose cycle carries equality constraints,
and the keyed joins inside it keep the constraints they always had. The
joined edges are not reduced, since propagating constraints through a
recursive node is not sound.

'ungroup' and 'atKey' are the exits into an ordinary recursive generator.
The rules of 'recur' apply here too: the recursion must be guarded by an
'apply', every live key must eventually reach a finite base member, and
alternatives around a recursive occurrence must carry equal weights, which is
what 'oneofGrouped' gives without asking for them.
-}
recurGrouped :: (Ord key) => (Grouped key a -> Grouped key a) -> Grouped key a
recurGrouped = Engine.recurGrouped

{- | Bound a generator to the members of size at most the given bound.

Size is the number of source choices in a member. A recursive generator
becomes an ordinary finite one and keeps the ranks it already had, so a rank
found under one bound replays under any larger bound and through the unbounded
generator itself. Size classes keep their count-based probability. Weighted
finite choices closed with 'atomic' keep their own distribution inside those
classes.

This bounds recursion; it does not filter a finite language. A generator
that is not recursive is returned unchanged, members larger than the bound
included.

Bounding the recursive occurrence inside the 'recur' or 'recurGrouped' body
that defines it is rejected with 'BoundedRecursiveOccurrence': the bound would
need the size classes the definition is still computing. Bound the finished
language instead, as in @upToSize n (recur ...)@.
-}
upToSize :: Int -> ECTAGen a -> ECTAGen a
upToSize = Engine.upToSize

-- | Whether a generator stands for a recursive language.
isRecursive :: ECTAGen a -> Bool
isRecursive = Engine.isRecursive

-- | Whether a generator is an opaque region, which cannot be inspected.
isOpaque :: ECTAGen a -> Bool
isOpaque = Engine.isOpaque

{- | Read retained source descriptions and group names as a diagnostic graph.

The graph preserves construction context and equality obligations. It does
not reduce constraints or enumerate complete generated values. Use 'support'
for semantic operations. An unnamed source retains its original labels.
-}
inspect :: ECTAGen a -> Either GenError (Inspection Symbol)
inspect = Engine.inspect

{- | Return the ECTA support of an inspectable generator.

The support is an automaton over 'Label': the user's symbols and the private
labels of the engine. A recursive generator's support is its @Mu@ node, which
accepts members of every size: a size bound restricts the rank space, not the
automaton.
-}
support :: ECTAGen a -> Either GenError (Node (Label Symbol) EqConstraints)
support = Engine.support

{- | Return the exact number of ranks in a transparent generator.

A recursive generator has no cardinality; bound it with 'upToSize', or ask
for one size class with 'countAtSize'.
-}
cardinality :: ECTAGen a -> Either GenError Integer
cardinality = Engine.cardinality

-- | Return the exact cardinality of each retained group in O(number of groups).
sizes :: Grouped key a -> Either GenError (Map.Map key Integer)
sizes = Engine.sizes

{- | Return the exact number of retained members in every live key at one
structural size.

Counts describe the language, not the sampler. A declared atomic distribution
can therefore give two keys equal counts and unequal probability masses.
-}
countsAtSize :: Grouped key a -> Int -> Either GenError (Map.Map key Integer)
countsAtSize = Engine.countsAtSize

{- | Return the exact distribution of retained keys conditional on one
structural size.

This is the distribution used by sampling that exact size. Weighted atomic
choices retain both their between-key and within-key distributions. Recursive
families memoize each key's mass series. A query extends that recurrence to the
requested size without enumerating members, then normalizes one mass per key.
A finite family may enumerate group outcomes to condition their stored masses
on size. A size with no members returns an empty map.
-}
massesAtSize :: Grouped key a -> Int -> Either GenError (Map.Map key Rational)
massesAtSize = Engine.massesAtSize

{- | The number of members of one size, for any inspectable generator.

Size is the number of source choices in a member. This is the counting a
recursive generator supports in place of a cardinality: every class is
finite even when the language is not.
-}
countAtSize :: ECTAGen a -> Int -> Either GenError Integer
countAtSize = Engine.countAtSize

{- | The smallest structural size in an inspectable language.

Size is the number of source choices in a member. 'Nothing' means the language
is empty. Opaque generators cannot be inspected.
-}
minimumSize :: ECTAGen a -> Either GenError (Maybe Int)
minimumSize = Engine.minimumSize

-- | Count ranked outcomes by a projected key without aggregating equal values.
countBy :: (Ord key) => (a -> key) -> ECTAGen a -> Either GenError (Map.Map key Integer)
countBy = Engine.countBy

-- | Aggregate the exact probability mass of every finite transparent result.
pmf :: (Ord a) => ECTAGen a -> Either GenError [(a, Rational)]
pmf = Engine.pmf

{- | Aggregate the exact result distribution conditional on one structural
size.

For a recursive generator this interprets its size-indexed sampler, so a
weighted finite choice closed with 'atomic' retains its declared probability.
For a finite generator it conditions the retained outcome masses on the
requested size. A size with no members returns an empty distribution.

This enumerates every result in the selected size class before equal results
are aggregated. A language can therefore be cheap to count and too large for
this observer. Use 'countAtSize' for cardinality, or 'massesAtSize' when a
retained-key distribution answers the question.
-}
pmfAtSize :: (Ord a) => ECTAGen a -> Int -> Either GenError [(a, Rational)]
pmfAtSize = Engine.pmfAtSize

{- | Return the first member in structural size and rank order.

For recursive generators this is a globally smallest member. 'Nothing' means
the language is empty; other construction or inspection failures stay explicit.
-}
smallest :: ECTAGen a -> Either GenError (Maybe a)
smallest = Engine.smallest

{- | Decode one stable rank from an inspectable generator.

Ranks are stable while the generator definition and the ordering of its finite
sources remain unchanged.
-}
unrank :: ECTAGen a -> Integer -> Either GenError a
unrank = Engine.unrank

{- | The term of one member by rank, over 'Label'.

A recursive generator keeps its automaton rather than its members' terms,
so it reports 'CannotInspectRecursiveGenerator'; 'unrank' still gives the
value.
-}
termAt :: ECTAGen a -> Integer -> Either GenError (Tree.Tree (Label Symbol))
termAt = Engine.termAt

{- | The number of source choices in the member a rank decodes to.

'Nothing' for opaque generators and out-of-range ranks.
-}
sizeOfRank :: ECTAGen a -> Integer -> Maybe Int
sizeOfRank = Engine.sizeOfRank

{- | Every member of strictly smaller size than the given rank's member, in
size order, as replayable rank and value.

Size is the number of source choices in a member. The stream is lazy, so cap
it before use; a smallest failing member found in it is globally minimal.
Opaque generators have no smaller members, and neither does a rank outside
a finite generator. A recursive generator has a size class for every rank.
-}
smallerMembers :: ECTAGen a -> Integer -> [(Integer, a)]
smallerMembers = Engine.smallerMembers

{- | Structural shrink candidates for one rank of a transparent generator.

Candidates decode to values from the same language and are never larger than
the current member: earlier alternatives at their smallest members come
first, then each product component shrinks independently. Opaque generators
and out-of-range ranks have no candidates.
-}
shrinkRank :: ECTAGen a -> Integer -> [Integer]
shrinkRank = Engine.shrinkRank

-- | Lower to QuickCheck, preserving construction and decoding errors.
lower :: ECTAGen a -> QC.Gen (Either GenError a)
lower = Engine.lower

-- | Lower an inspectable generator while retaining the sampled rank.
lowerWithRank :: ECTAGen a -> QC.Gen (Either GenError (Integer, a))
lowerWithRank = Engine.lowerWithRank

{- | Lower a transparent uniform generator to a direct QuickCheck generator.

The generator carries no per-sample error wrapping; construction errors and
the non-uniform and opaque cases return 'Nothing' and must go through 'lower'.
-}
lowerUniform :: ECTAGen a -> Maybe (QC.Gen a)
lowerUniform = Engine.lowerUniform

-- | Like 'lowerUniform', retaining the sampled replay rank.
lowerUniformWithRank :: ECTAGen a -> Maybe (QC.Gen (Integer, a))
lowerUniformWithRank = Engine.lowerUniformWithRank

{- | Lower an inspectable generator through any sampling backend.

The exact backend of "Data.CFTA.Ranked.Internal.Sampler" gives the sampling
distribution as a finite list. An opaque region is a QuickCheck generator and
cannot be interpreted, so it reports 'CannotInspectOpaqueGenerator'.
-}
lowerVia :: (GenBackend gen) => ECTAGen a -> gen (Either GenError a)
lowerVia = Engine.lowerVia

-- | 'lowerVia' retaining the sampled replay rank.
lowerWithRankVia :: (GenBackend gen) => ECTAGen a -> gen (Either GenError (Integer, a))
lowerWithRankVia = Engine.lowerWithRankVia
