# microecta-generator

[![Hackage](https://img.shields.io/hackage/v/microecta-generator.svg)](https://hackage.haskell.org/package/microecta-generator)

`microecta-generator` builds indexed generators on
[`microecta`](https://hackage.haskell.org/package/microecta). Transparent
generator regions retain an exact ECTA support, cardinality, and replay rank;
the same package includes QuickCheck integration for sampling, opaque fallbacks,
and structural shrinking.

The lower-level `Data.Tree.Gen` API is automaton-neutral. It represents a
non-empty finite language by stable ranks plus a backend-independent sampling
plan. `Data.Tree.FTA.Gen.fromFTA` compiles an acyclic ordinary FTA into that
representation, after which `Data.Tree.Gen.QuickCheck.forAll` supplies valid
sampling, deterministic replay ranks, and language-preserving shrinking:

```haskell
import qualified Data.Tree.FTA.Gen as FTAGen
import qualified Data.Tree.Gen as Ranked
import qualified Data.Tree.Gen.QuickCheck as RankedQC

Right ranked = FTAGen.fromFTA plainFTA

replay = Ranked.unrank ranked 42
property = RankedQC.forAll ranked invariant
```

For directly authored finite generators, the FTA-facing API retains the term
witness and gives each do binding one direct constructor position:

```haskell
import qualified Data.Tree.FTA.Gen.QuickCheck as FTA

pair = FTA.node "pair" $ FTA.do
  left  <- atoms
  right <- atoms
  FTA.pure (left, right)
```

`FTA.support pair` returns the exact ordinary FTA; `FTA.toGen pair` lowers the
same ranked language to QuickCheck.

The flagship ordinary language is
[`Data.Tree.FTA.UntypedExpressionLanguage`](common/Data/Tree/FTA/UntypedExpressionLanguage.hs).
Every expression is an integer, so constructor shape is the whole problem:

```haskell
binaryLayer children =
  oneofOrDie "integer operations"
    [ FTA.node "add" $ FTA.do
      left  <- children
      right <- children
      FTA.pure (Add left right)
    , FTA.node "multiply" $ FTA.do
      left  <- children
      right <- children
      FTA.pure (Multiply left right)
    ]
```

Its exact-depth cardinality is executable documentation: two literals and two
binary operations give `count (n + 1) = 2 * count n ^ 2`. The ECTA flagship
below starts from the same expression idea, adds Booleans, and must therefore
relate operation signatures to child result types.

ECTA and LTA remain adapters over this layer. ECTA keeps its richer grouped,
recursive, and equality-aware combinators; LTA can discharge liquid guards
once and then use the same pure rank/sample/shrink operations.

Add the package to `build-depends` and import the QuickCheck-facing API:

```cabal
build-depends: microecta-generator
```

```haskell
import Data.ECTA.Gen.QuickCheck (ECTAGen)
import qualified Data.ECTA.Gen.QuickCheck as ECTAGen
```

## Generator API

`Data.ECTA.Gen` turns a finite indexed source into an ECTA whose leaves contain
stable indices, not generated values. `Functor` and `Applicative` composition
preserve that symbolic structure, so ordinary `ApplicativeDo` builds ECTA
products. Alongside the ECTA, the generator tracks an exact cardinality and a
rank-to-outcome selector; applicative products multiply their counts rather
than materializing their Cartesian products.

`match` generates two values under a reified key equality: in
`match (authenticatedUser :==: fileOwner) authentication filesystem`, the
`:==:` keeps both projections as data, so the match can group each input by
its own key, encode the shared keys as an actual ECTA equality constraint,
count the matching group products, and unrank directly into the selected
group. `:&&:` conjoins several equalities. This is the exact-uniform
conditioning of [Claessen, Duregård and Pałka, *Generating Constrained Random
Data with Uniform Distribution*, JFP 25,
2015](https://doi.org/10.1017/S0956796815000143), with the condition reified as
data rather than tested on samples. `match` accepts arbitrary value
projections, so discovering its groups requires enumerating the input ranks;
conditioning three or more generators is the grouped layer's job (`groupBy`
and `apply`).

`relate leftKey rightKey relation left right` admits every pair for which the
projected keys satisfy `relation`. The relation is an ordinary Haskell
function such as `canRead Admin Public = True`; it may be asymmetric and the
two key types may differ. A transparent join evaluates it once per live key
pair, then counts, ranks, and samples the accepted group products directly.
An opaque input uses rejection filtering. `match` remains the shorter and
faster operation for equality because it intersects the two key maps without
testing their Cartesian product.

`Grouped key a` is the explicit grouping-preserving path for nested or very
large languages. The `key` is the type returned by the classifier and used to
decide which groups may be joined; it is not part of the generated `a`. Matching
key values receive equal internal labels on constrained ECTA paths. `groupBy`
classifies any transparent generator's outcomes (enumerating them once), and
`keyed key generator` declares that every member already has one known key.
`keyed` does not enumerate members, so it also accepts a recursive transparent
generator. The caller is responsible for declaring the right key. Grouped
generators support ordinary `fmap` (and `mapWithKey` when the value should
absorb its key). `regroupBy` changes the
classification without enumerating values, `sizes` returns the stored
cardinality of every group, and `atKey` selects one group as an ordinary
conditional generator. An operation of any arity is classified by a `Sig`,
written like a many-sorted operation signature — `:*` between argument keys,
`:->` before the result key: `leftKey :* rightKey :-> resultKey`.
`apply` matches each signature
key with the corresponding argument family, equates their paths in one ECTA
edge holding one equality constraint per argument, and retains the result key
for later equality constraints. The operation family holds functions (`fmap`
a compiling function onto it); the argument families arrive as an `Args`
chain. `frequencies` chooses among grouped generators with relative weights,
group by group, so alternated layers (for example expressions of depth at
most n) stay grouped. `uniformlyGrouped` combines grouped generators in
proportion to their exact cardinalities, so every member of the union is
equally likely, which is what a layered language wants; `uniformly` does the
same for flat generators. `ungroup` returns an ordinary `ECTAGen` with
the same exact distribution. Stable source order and ascending key order give
deterministic replay ranks.

```haskell
commandsByKind = ECTAGen.oneofGrouped
  [ ECTAGen.keyed Read readCommands
  , ECTAGen.keyed Write writeCommands
  ]
```

Here each command language keeps its existing compact support. Only the two
declared keys are stored.

```haskell
binaryFunctionsBySignature :: Grouped BinarySignature BinaryFunctionInstance
binaryFunctionsBySignature =
  ECTAGen.groupBy binarySignature (ECTAGen.elements binaryFunctionInstances)

binarySignature instance_ =
  firstArgumentType instance_
    :* secondArgumentType instance_
    :-> binaryResultType instance_

literalsByType :: Grouped Type TypedExpression
literalsByType = ECTAGen.groupBy expressionType (ECTAGen.elements literals)

unaryFunctionsBySignature :: Grouped UnarySignature (TypedExpression -> TypedExpression)
unaryFunctionsBySignature =
  compileNot <$ ECTAGen.keyed unarySignature (ECTAGen.elements [()])

conditionalFunctionsBySignature =
  compileConditional
    <$> ECTAGen.groupBy conditionalSignature (ECTAGen.elements allTypes)

binaryLayer children =
  ECTAGen.apply
    (compileBinary <$> binaryFunctionsBySignature)
    (children :& children :& ANil)

conditionalLayer children =
  ECTAGen.apply
    conditionalFunctionsBySignature
    (children :& children :& children :& ANil)
```

The
[`Data.ECTA.TypedExpressionLanguage`](common/Data/ECTA/TypedExpressionLanguage.hs)
flagship combines unary `Not`, binary functions, and
ternary `IfExpression`. Its finite layers combine those three alternatives with
`uniformlyGrouped`, so every expression remains equally likely. Its
recursive layer uses equal structural alternatives, as recursive declarations
require.

Both layers also support qualified do-notation through `Data.ECTA.Gen.Do`,
which `Data.ECTA.Gen.QuickCheck` re-exports. Enable `QualifiedDo` together
with `ApplicativeDo`; statements must stay independent, and the final
statement must use the qualified `ECTAGen.pure`. A grouped block chooses the
operation family first and then one argument per signature component in
order; whatever the arity, it builds exactly one `apply` join:

```haskell
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE QualifiedDo #-}

authentication :: ECTAGen Authentication
authentication = ECTAGen.node "authentication" $ ECTAGen.do
  user <- generatedUser
  method <- ECTAGen.elements [Password, Token]
  ECTAGen.pure (Authentication user method)

conditionalLayer children = ECTAGen.node "if" $ ECTAGen.do
  build <- conditionalFunctionsBySignature
  condition <- children
  ifTrue <- children
  ifFalse <- children
  ECTAGen.pure (build condition ifTrue ifFalse)
```

Impossible shapes fail at compile time with an explanation: a statement using
an earlier bound value, an unqualified `pure` ending, or a fallible pattern.
A block that binds fewer arguments than its operation's signature arity is a
type mismatch against `Applying`, whose haddock says what the remaining keys
are. A statement whose result is a tuple, as `match` and `relate` give, must
bind it lazily: `ApplicativeDo` rejects `(a, b) <- match ...` and accepts
`~(a, b) <- match ...`.

Every transparent generator samples compositionally by rank, including exact
non-uniform `frequency` and conditioned joins; sampling never materializes the
final Cartesian product. `cardinality` and `unrank` expose deterministic
replay, while `countBy` reports exact coverage of ranked outcomes. A retained
`Grouped` key is also a symbolic observation. `countsAtSize` reports how many
members reach each key. `massesAtSize` reports the exact key distribution used
by sampling that size. Declared atomic weights can therefore produce equal
counts and unequal masses. Recursive groups memoize both size series, so these
queries do not enumerate traces. ECTA support is demand-driven: counts, masses,
replay, sampling, and constrained joins retain it as a lazy thunk. `support`
forces the complete symbolic representation.

`smallest (atKey key family)` returns a globally smallest witness for one
observation. An unreachable key returns `Right Nothing`. A temporal observation
such as "failure state reached" belongs in the recursive key as a sticky state
bit; it is not recovered later by filtering complete traces.

`pmfAtSize` asks the more general value-level distribution question. It
interprets the same size-indexed sampler used by lowering, including weighted
atomic choices, but may enumerate products before equal results are aggregated.
The generic `countBy`, `pmf`, and `pmfAtSize` observers are therefore best for
finite or small result languages. Retain a reusable classification with
`Grouped` when the observation is part of a recursive language.

```haskell
failure = ECTAGen.atKey FailureReached tracesByOutcome

shortestFailure = ECTAGen.smallest failure
outcomeCounts = ECTAGen.countsAtSize tracesByOutcome 41
outcomeProbabilities = ECTAGen.massesAtSize tracesByOutcome 41
samples = ECTAGen.toGen (ECTAGen.ungroup tracesByOutcome)
```

`AtSize` means structural source choices, not list length. In this example the
empty trace contributes one choice, so size 41 represents forty commands.

`Data.ECTA.Gen.QuickCheck` exposes `toGen`, plus
`toGenWithRank` when the sampled replay rank is needed. `forAll` checks a
property and shrinks to the smallest failing member. It first tests every
member of strictly smaller size, in size order (`smallerMembers`, capped by
`smallerMemberLimit`), so the reported counterexample is globally size-minimal
whenever that search reaches one. Behind that it offers size-major structural
shrinking through `shrinkRank`, which for a recursive generator reads its
candidates from the form bounded at the current size, since bounding is what
gives a recursive member components to shrink. Every candidate is a member of
the generated language, and the failing rank is printed for deterministic
replay with `unrank`. A generator with an opaque region has no ranks at all, so
`forAll` tests it by sampling with no shrinking. `sized` builds and compiles
one generator per QuickCheck size (shared across samples), so layered
generators can scale with the size parameter.

Greedy shrinkers - QuickCheck, Hedgehog, Hypothesis, falsify - stop at a local
minimum. Bounded-exhaustive tools find a smallest counterexample by testing the
whole space up to a bound ([Runciman, Naylor and Lindblad, *SmallCheck and Lazy
SmallCheck*, Haskell 2008](https://doi.org/10.1145/1411286.1411292), and FEAT's
exhaustive modes). `forAll` gets a size-minimal counterexample starting from a
random one, by enumerating every member of strictly smaller size first.

```haskell
import Data.ECTA.Gen.QuickCheck (ECTAGen)
import qualified Data.ECTA.Gen.QuickCheck as ECTAGen

joined :: ECTAGen (Authentication, Filesystem)
joined =
  ECTAGen.match
    (authenticatedUser :==: fileOwner)
    authentication
    filesystem
```

```haskell
canRead :: Role -> Classification -> Bool
canRead Admin _ = True
canRead Member Public = True
canRead _ _ = False

authorized :: ECTAGen (User, File)
authorized =
  ECTAGen.relate roleOf classification canRead users files
```

```haskell
replay :: Either ECTAGenError Authentication
replay = ECTAGen.unrank authentication 42

coverage :: Either ECTAGenError (Map UserId Integer)
coverage = ECTAGen.countBy authenticatedUser authentication
```

## Recursive languages

`recur` builds a generator from its own language, so a language can be
unbounded rather than unrolled layer by layer:

```haskell
tree :: ECTAGen Tree
tree = ECTAGen.recur $ \self ->
    ECTAGen.oneof
        [ Leaf <$> ECTAGen.elements [0 .. 2]
        , Branch <$> self <*> self
        ]
```

The result stands for the whole language. It has no cardinality; it has
size classes, counted by FEAT-style convolution, where size is the number of
source choices in a member — `countAtSize tree 4` is `Right 405` for the
tree above. Ranks are size-major, so `unrank tree 0` is the smallest member
and every rank replays as usual, and the ECTA support is a `Mu` node: one
finite automaton for infinitely many terms.

The convolution is FEAT's ([Duregård, Jansson and Wang, *Feat: Functional
Enumeration of Algebraic Types*, Haskell
2012](https://doi.org/10.1145/2364506.2364515)), but the size measure is not:
FEAT charges size wherever the definition says `pay`, while here every source
choice costs one and nothing else does. "Size-major rank" is this package's own
term for the resulting order. Counting a family by a size recurrence and
drawing from those counts is the recursive method of Nijenhuis and Wilf,
*Combinatorial Algorithms*, 2nd ed., 1978, and of [Flajolet, Zimmermann and Van
Cutsem, *A Calculus for the Random Generation of Labelled Combinatorial
Structures*, TCS 132, 1994](https://doi.org/10.1016/0304-3975(94)90226-7);
turning a rank back into a member is unranking, as in [Martínez and Molinero,
*A generic approach for the unranking of labeled combinatorial classes*, RSA
19, 2001](https://doi.org/10.1002/rsa.10025).

`pure` is one source choice like any other, so `pure f <*> x` has one more
choice than `f <$> x`: the two have different sizes and therefore different
ranks. It also counts as guarding recursion, so `pure f <*> self` is accepted
where `f <$> self` is `UnguardedRecursion`.

`upToSize n` bounds the language back to an ordinary finite generator over
the members of size at most `n`, and `toGen` and `forAll` apply it from
QuickCheck's size parameter. Size classes and structural alternatives are
selected from their member counts; weighted finite choices closed with
`atomic` retain their declared PMF inside the selected size. Bounding preserves
ranks: the members of size at most `n` hold the same ranks under every bound
large enough to contain them. A counterexample therefore replays under any
larger bound, and `forAll` shrinks by walking whole size classes below the
failing member and then, past its cap, by shrinking the components of the form
bounded at the failing member's size.

`atomic` treats every member of a finite generator as one source choice. This
sets a domain-sized boundary inside a recursive language. For example, an
acyclic command FTA can retain its compact support and rank decoder while each
complete command, rather than each node in its term, contributes one unit to a
trace's size:

```haskell
command = decodeCommand <$> ECTAGen.atomic (ECTAGen.fromECTA commandFTA)

nonEmptyTrace = ECTAGen.recur $ \rest ->
  ECTAGen.oneof
    [ (: []) <$> command
    , (:) <$> command <*> rest
    ]
```

This does not enumerate the FTA or add one support edge per command. It keeps
the accepted language, compact support, ranks, and decoder. The whole acyclic
FTA becomes the finite command source, so QuickCheck's size acts on the outer
trace instead of taking a second prefix inside each command. For an already
finite generator, its cardinality and distribution also stay unchanged. Only
the size and structural-shrinking boundary changes. A recursive input has
infinitely many members, so bound it with `upToSize` before making it atomic --
and do that *outside* the recursive definition. Neither `upToSize` nor `atomic`
can be applied to the `recur` argument, or to anything built from it: the bound
would need the size classes that definition is still computing, and an atom
over them would have a cardinality depending on itself. Both shapes are
rejected with `BoundedRecursiveOccurrence`. Opaque generators have no size
structure and cannot be made atomic.

The self-reference has to go through `recur`. A generator that names itself
directly, as in `tree = Branch <$> tree <*> tree`, is an infinite Haskell
value: building it never finishes, and the failure is a hang rather than
anything the library can report. In the other direction, a body that never
uses the argument is not recursive, and is handed back as it is: a finite
body stays a finite generator, cardinality and inspection included. A body
that could not be built at all reports its own error, rather than becoming a
recursive language every finite inspector calls unbounded.

Two rules apply inside the knot. The recursion must be guarded: every
occurrence of the argument sits under at least one `<*>`, or the language
has no smallest member — an unguarded definition is rejected with
`UnguardedRecursion` rather than left to hang. The check is per definition, so
inside a nested `recur` an occurrence of the *outer* language must also sit
under an application within the inner body. Structural alternatives around a
recursive occurrence must carry equal weights; `oneof` is the combinator that
already reads that way, and the size bound controls how large members get.
`frequency` with unequal recursive-branch weights is rejected rather than
ignored. A weighted finite choice may still enter through `atomic`, retaining
its own distribution inside every recursive size.

Inspection that needs one ECTA term per member (`groupBy`, `match`, `relate`,
`pmf`, `countBy`) is not available on a language built with `recur`, bounded or
not: a recursive generator retains its automaton rather than a term per member,
and `upToSize` bounds the rank space without recovering those terms. Use the
exact-size observers (`countAtSize`, `pmfAtSize`, `countsAtSize`,
`massesAtSize`), keep that layer finite, or read the language from an automaton
with `fromECTA`, whose members *are* terms and which therefore does keep full
inspection once bounded.

`recurGrouped` does the same for the grouped layer, which is where recursion
and equality constraints meet in one cycle:

```haskell
expressions :: Grouped Type TypedExpression
expressions = ECTAGen.recurGrouped $ \self ->
    ECTAGen.oneofGrouped [literalsByType, applicationLayer self]

anyExpression = ECTAGen.ungroup expressions
intExpression = ECTAGen.atKey TInt expressions
```

Which keys the family has is part of the fixpoint, so it is solved first —
from the empty family upward, adding the result keys of operations whose
argument keys are already present — and the languages are tied over that
settled set. All the keys share one `Mu` node whose edges carry their key as
a first child; an occurrence at one key is that node under an edge holding
the key's label, with an equality constraint tying the two. A recursive
family is therefore one recursive automaton whose cycle carries the keyed
joins' equality constraints, which is the shape only an ECTA can hold.

For the language above, unfolding that automaton twice accepts exactly the 46
expressions produced by the hand-unrolled depth-one generator. This includes
unary `Not`, the binary functions, and ternary `IfExpression`. `ungroup` and
`atKey` are the exits back to an ordinary recursive generator, so bounding,
sampling, replay, and shrinking all work as above. `sizes` has no cardinality
to report for a recursive family; use `countAtSize` on `atKey`.

`fromECTA` goes the other way: it reads an existing automaton as a generator
of the terms it accepts, counting them by size — the number of term nodes —
with the automaton itself as the support.

```haskell
types :: Node Symbol
types = createMu $ \recursive -> Node
    [ Edge "baseType" []
    , Edge "->" [recursive, recursive]
    , Edge "Maybe" [recursive]
    ]

typeGen :: ECTAGen (Term Symbol)
typeGen = ECTAGen.fromECTA types
```

`countAtSize typeGen` reports 1, 1, 2, 4, 9 for sizes one to five, `unrank`
walks the terms in size order, and sampling draws uniformly from the terms
of at most the current size. Because the generated values *are* the accepted
terms, bounding one of these keeps full inspection: `pmf`, `countBy`, and
`groupBy` all work on `upToSize n (fromECTA node)`.

Equality constraints are not counted. They correlate an edge's children, so
the edge's count is the size of an intersection rather than a product of the
children's counts; an automaton carrying them is rejected with
`CannotCountConstrainedEdges` rather than miscounted.

Ambiguity is not counted either. A node's count is the sum over its edges,
which counts accepting *runs*, so a node with two edges that accept a common
term would count that term twice and `unrank` would return it at two ranks.
Every reachable node is checked, and an ambiguous automaton is rejected with
`AmbiguousAutomaton`. Two edges overlap when they share a symbol and arity and
every child position has a non-empty intersection, which without constraints
is exactly when they share a term.

`fromIndexed` is the transparent boundary for a FEAT-style finite enumeration:
it needs only a cardinality and a stable function from an integer index to a
value. `elements` is the corresponding list convenience function.

`Data.Tree.Gen.fromIndexedOnDemand` is the automaton-adapter variant. It keeps
the same cardinality, ranks, and sampler but never tabulates a small indexed
source while compiling its replay decoder. LTA counting uses it so the
automaton remains a graph until one rank is selected.

`pool n native` bridges a large or infinite QuickCheck source into this finite
world. Its outer `Gen` samples `n` values once and returns an `ECTAGen` whose
ranks are those draws. The result supports exact inspection and constrained
joins. Repeated draws remain repeated ranks and therefore retain their
empirical weight. Reuse the returned generator when two choices must range over
the same frozen universe.

`freeze seed n native` is `pool` with the draws fixed by a seed, so it is an
ordinary transparent generator rather than a `Gen` of one: it can be weighted
by `uniformly`, keyed, joined, replayed, and shrunk, and its ranks are the same
in every run under the same seed. The native generator runs at QuickCheck size
30, the default of `generate`; use `resize` on it for another size.

Every failure is an `ECTAGenError`. The derived `Show` names the case, and
`explain` says what it means and which combinator resolves it; sampling a
generator that could not be built raises both together.

```
>>> putStrLn (ECTAGen.explain ECTAGen.UnguardedRecursion)
The recursive language reaches itself without passing through an
application, so its members never get smaller and no size class can
be counted.
Fix: put every occurrence of the argument under <*>, as in
Branch <$> self <*> self, or under apply in a grouped family. An
alternative that is the argument itself, such as oneof [leaf, self],
is the shape to look for.
```

`fromGen` embeds an ordinary `QuickCheck.Gen` as an explicitly opaque region.
Opaque regions still compose and sample, but cannot be inspected with `pmf`;
joining through one falls back to QuickCheck rejection. Opaque regions also
have no replay rank, and `forAll` therefore tests a generator holding one by
sampling alone, without shrinking. There is deliberately no `Monad` or
`Selective` instance.
This keeps inspectable applicative regions inside ECTA and makes the loss of
structure explicit.

## Module map

- `Data.Tree.Gen` is the constraint-neutral finite ranked language;
  `Data.Tree.Gen.QuickCheck` supplies sampling and shrinking.
- `Data.Tree.FTA.Gen` retains ordinary FTA witnesses while constructing or
  compiling that ranked language; its `Do` and `QuickCheck` modules mirror the
  ECTA-facing split below.
- `Data.ECTA.Gen` is the backend-polymorphic indexed generator core.
- `Data.ECTA.Gen.Sig` defines the signature (`Sig`) and condition (`On`)
  syntax; `Data.ECTA.Gen` re-exports both.
- `Data.ECTA.Gen.Do` provides the qualified do-notation operators.
- `Data.ECTA.Gen.QuickCheck` provides the ordinary QuickCheck-facing API,
  including `fromGen`, `toGen`, `forAll`, and `sized`.
- `Data.ECTA.Gen.Internal`, `Data.ECTA.Gen.Internal.Automaton`,
  `Data.ECTA.Gen.Internal.Decoder`, `Data.ECTA.Gen.Internal.Sampler`,
  `Data.ECTA.Gen.Internal.Shrink`, and `Data.ECTA.Gen.Internal.Size` implement
  static languages, joins, reading an automaton, compiled rank decoding,
  exact sampling, structural shrinking, and size-stratified counting. They are
  not exposed.

## Concurrency

Safe. Generators build ECTAs, and `microecta` interns nodes through
process-global tables, which are synchronized as of `microecta` 0.2.0.0.

This matters here more than it sounds, because this is a testing library and
test runners parallelize: `tasty` runs independent tests concurrently by
default when the test binary is linked with `-threaded` and run with `+RTS -N`,
and `hspec` does under `parallel`. A property drawing from an
`ECTAGen` can be run that way without anything in your code looking
concurrent. Against earlier `microecta` that was silent corruption rather than
a crash; see the concurrency note in `microecta`'s README.

## Sampling performance

The flagship FTA and ECTA languages each have three exact-uniform generators:

- **naive** generates an unconstrained representation and recognizes or
  rejects it afterwards;
- **bespoke** is a handwritten generator specialized to the language; and
- **FTA/ECTA** compiles the declarative automaton to a rank decoder.

All rows at a given depth therefore sample the same finite language with the
same uniform distribution. This is important: a smaller or biased baseline
would make its speed meaningless. The FTA's naive generator builds a generic
ranked term, recognizes it with a one-state FTA, then decodes it. There is no
semantic condition to reject, so that row is the zero-rejection control. The
ECTA's naive generator creates a raw application at each layer and rejects it
after independent type inference; its root alternatives are weighted by raw
candidate counts, so conditioning preserves uniformity. The bespoke ECTA
generator carries the requested result type through ordinary Haskell.

Every cell runs in a fresh process because `microecta`'s interning tables never
evict. The first-sample column includes construction; the throughput and
allocation columns reuse the resulting generator. A complete cell has a
30-second wall-clock limit and successful cells are the median of three runs.

### FTA: untyped integer expressions

Each successful FTA cell draws 100,000 samples.

| depth | members | engine | first sample | samples/s | alloc/sample | setup mem | retained after 100k |
| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 8 | naive | 0.03 ms | 548,859 | 13.9 KB | 33.6 KB | 35.8 KB |
| 1 | 8 | bespoke | 0.02 ms | 813,504 | 9.9 KB | 1.6 KB | 34.8 KB |
| 1 | 8 | FTA | 0.04 ms | 739,629 | 10.9 KB | 35.9 KB | 37.2 KB |
| 2 | 128 | naive | 0.03 ms | 235,626 | 32.3 KB | 33.9 KB | 36.0 KB |
| 2 | 128 | bespoke | 0.02 ms | 352,576 | 23.6 KB | 33.0 KB | 35.0 KB |
| 2 | 128 | FTA | 0.04 ms | 317,910 | 25.8 KB | 40.2 KB | 45.6 KB |
| 3 | 32,768 | naive | 0.04 ms | 110,228 | 69.2 KB | 34.4 KB | 36.5 KB |
| 3 | 32,768 | bespoke | 0.03 ms | 161,212 | 50.9 KB | 33.5 KB | 35.5 KB |
| 3 | 32,768 | FTA | 0.06 ms | 140,954 | 55.8 KB | 46.5 KB | 78.5 KB |
| 4 | 2,147,483,648 | naive | 0.05 ms | 51,775 | 143.0 KB | 35.4 KB | 37.5 KB |
| 4 | 2,147,483,648 | bespoke | 0.04 ms | 76,214 | 105.7 KB | 34.5 KB | 36.5 KB |
| 4 | 2,147,483,648 | FTA | 0.08 ms | 67,158 | 115.6 KB | 57.2 KB | 209.7 KB |

The control behaves as it should: all three approaches stay close because an
ordinary FTA adds no semantic pruning to this language. The FTA decoder is
within roughly 13% of the direct bespoke generator throughout.

### ECTA: typed integer and Boolean expressions

Each successful ECTA cell draws 20,000 samples. The smaller fixed workload
keeps depth three measurable while preserving the depth-four rejection
failure; it is still large enough for stable normalized rates.

| depth | members | engine | first sample | samples/s | alloc/sample | setup mem | retained after 20k |
| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 42 | naive | 0.02 ms | 160,984 | 49.1 KB | 33.5 KB | 35.6 KB |
| 1 | 42 | bespoke | 0.02 ms | 574,366 | 14.1 KB | 3.1 KB | 41.5 KB |
| 1 | 42 | ECTA | 0.09 ms | 2,166,143 | 3.6 KB | 40.5 KB | 37.2 KB |
| 2 | 27,054 | naive | 0.09 ms | 17,498 | 449.0 KB | 34.3 KB | 36.5 KB |
| 2 | 27,054 | bespoke | 0.04 ms | 200,256 | 38.3 KB | 37.4 KB | 105.9 KB |
| 2 | 27,054 | ECTA | 0.15 ms | 1,675,322 | 4.1 KB | 50.8 KB | 54.9 KB |
| 3 | 8,887,065,932,466 | naive | 0.28 ms | 2,537 | 2.93 MB | 35.1 KB | 37.3 KB |
| 3 | 8,887,065,932,466 | bespoke | 0.10 ms | 66,822 | 112.4 KB | 50.1 KB | 304.5 KB |
| 3 | 8,887,065,932,466 | ECTA | 0.22 ms | 887,311 | 6.6 KB | 65.9 KB | 128.3 KB |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | naive | **timeout (30s)** | — | — | — | — |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | bespoke | 0.60 ms | 22,230 | 335.9 KB | 83.9 KB | 850.4 KB |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | ECTA | 0.40 ms | 332,127 | 15.3 KB | 104.5 KB | 296.1 KB |

At depth three the ECTA decoder is about 350x faster than rejection and 13x
faster than the bespoke generator, allocating about 455x and 17x less per
sample respectively. At depth four, rejection cannot complete the fixed cell;
the ECTA remains about 15x faster than the bespoke implementation. The setup
cost stays below half a millisecond because the finite dependency structure is
compiled once and every later sample is one rank decode.

Measured with GHC 9.12.2 and `-O2` on the maintainer's Apple Silicon machine on
2026-09-02. An empty generator ran at about 15.4M draws/s and one `chooseInt`
at 2.7M draws/s during the ECTA run. Rates move a few percent between runs and
with the QuickCheck and `random` versions in use. Reproduce one table, or all
four repository tables, with:

```sh
cabal bench microecta-generator:untyped-expression-speed --enable-optimization=2
cabal bench microecta-generator:typed-expression-speed --enable-optimization=2
./scripts/benchmark-generators.sh
```

## Dependency surface

The library depends directly on `microecta`, `QuickCheck`, `array`,
`containers`, and `text`; the benchmarks additionally use `random` and
`process`. The
dependency direction is one-way: `microecta` does not depend on this package
or on QuickCheck.

## Build

From the repository root:

```sh
cabal build microecta-generator -j1
cabal test microecta-generator:unit-tests -j1
```

`-j1` is a suggestion, not a requirement: optimized builds of the `microecta`
core are memory-hungry, and one unit of parallelism keeps a whole workspace
build inside a small machine's memory. Drop it if you have the headroom.
