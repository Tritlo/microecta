# microecta-generator

[![Hackage](https://img.shields.io/hackage/v/microecta-generator.svg)](https://hackage.haskell.org/package/microecta-generator)

`microecta-generator` builds indexed generators on
[`microecta`](https://hackage.haskell.org/package/microecta). Transparent
generator regions retain an exact ECTA support, cardinality, and replay rank;
the same package includes QuickCheck integration for sampling, opaque fallbacks,
and structural shrinking.

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
group. `:&&:` conjoins several equalities. `match` accepts arbitrary value
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
most n) stay grouped. `ungroup` returns an ordinary `ECTAGen` with
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
binaryFunctionsBySignature :: Grouped (Sig '[Type, Type] Type) BinaryFunctionInstance
binaryFunctionsBySignature = ECTAGen.groupBy signature (ECTAGen.elements functionInstances)

signature function =
  argument1Type function :* argument2Type function :-> resultType function

literalsByType :: Grouped Type TypedExpression
literalsByType = ECTAGen.groupBy expressionType (ECTAGen.elements literals)

notFunctions :: Grouped (Sig '[Type] Type) (TypedExpression -> TypedExpression)
notFunctions =
  compileNot <$ ECTAGen.keyed (TBool :-> TBool) (ECTAGen.elements [()])

conditionalFunctions =
  compileConditional
    <$> ECTAGen.groupBy
      (\result -> TBool :* result :* result :-> result)
      (ECTAGen.elements allTypes)

binaryLayer children =
  ECTAGen.apply
    (compileApplication <$> binaryFunctionsBySignature)
    (children :& children :& ANil)

conditionalLayer children =
  ECTAGen.apply
    conditionalFunctions
    (children :& children :& children :& ANil)
```

The typed-expression example combines unary `Not`, binary functions, and
ternary `IfExpression`. Its finite layers weight those three alternatives by
their exact cardinalities, so every expression remains equally likely. Its
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
authentication = ECTAGen.do
  user <- generatedUser
  method <- ECTAGen.elements [Password, Token]
  ECTAGen.pure (Authentication user method)

conditionalLayer children = ECTAGen.do
  build <- conditionalFunctions
  condition <- children
  ifTrue <- children
  ifFalse <- children
  ECTAGen.pure (build condition ifTrue ifFalse)
```

Impossible shapes fail at compile time with an explanation: a statement using
an earlier bound value, an unqualified `pure` ending, a missing operation
argument, or a fallible pattern.

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
property and shrinks to the smallest failing member: candidates first search
every structurally smaller member in size order (`smallerMembers`, capped),
so the reported counterexample is globally size-minimal whenever the search
reaches one - a guarantee ordinary shrinking cannot make. Structural
component shrinking through `shrinkRank` follows as a fallback. Every
candidate is a member of the generated language, and the failing rank is
printed for deterministic replay with `unrank`. `sized` builds one generator per QuickCheck size (shared
across samples), so layered generators can scale with the size parameter.

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

`upToSize n` bounds the language back to an ordinary finite generator over
the members of size at most `n`, and `toGen` and `forAll` apply it from
QuickCheck's size parameter. Size classes and structural alternatives are
selected from their member counts; weighted finite choices closed with
`atomic` retain their declared PMF inside the selected size. Bounding preserves
ranks: the members of size at most `n` hold the same ranks under every bound
large enough to contain them. A counterexample therefore replays under any
larger bound, and `forAll` shrinks by walking whole size classes below the
failing member.

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
infinitely many members, so bound it with `upToSize` before making it atomic.
Opaque generators have no size structure and cannot be made atomic.

The self-reference has to go through `recur`. A generator that names itself
directly, as in `tree = Branch <$> tree <*> tree`, is an infinite Haskell
value: building it never finishes, and the failure is a hang rather than
anything the library can report. In the other direction, a body that never
uses the argument is not recursive, and is handed back as it is: a finite
body stays a finite generator, cardinality and inspection included.

Two rules apply inside the knot. The recursion must be guarded: every
occurrence of the argument sits under at least one `<*>`, or the language
has no smallest member — an unguarded definition is rejected with
`UnguardedRecursion` rather than left to hang. Structural alternatives around a
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
    ECTAGen.oneofGrouped [literalsByType, applicationGen self]

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

`fromIndexed` is the transparent boundary for a FEAT-style finite enumeration:
it needs only a cardinality and a stable function from an integer index to a
value. `elements` is the corresponding list convenience function.

`pool n native` bridges a large or infinite QuickCheck source into this finite
world. Its outer `Gen` samples `n` values once and returns an `ECTAGen` whose
ranks are those draws. The result supports exact inspection and constrained
joins. Repeated draws remain repeated ranks and therefore retain their
empirical weight. Reuse the returned generator when two choices must range over
the same frozen universe.

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
have no replay rank. There is deliberately no `Monad` or `Selective` instance.
This keeps inspectable applicative regions inside ECTA and makes the loss of
structure explicit.

## Module map

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
default, and `hspec` does under `parallel`. A property drawing from an
`ECTAGen` can be run that way without anything in your code looking
concurrent. Against earlier `microecta` that was silent corruption rather than
a crash; see the concurrency note in `microecta`'s README.

## Sampling performance

Against a handwritten QuickCheck generator for the same language: nested
`frequency` choices, the same exact weights, drawing uniformly from the same
well-typed expressions at the same exact depth. Both are driven the way
QuickCheck drives a property, one split seed per draw.

A rate on its own would flatter this library, because the decoder has to be
built before it can draw and that cost does not appear in a rate. So the
benchmark reports what one draw costs from cold as well, and what each
generator holds. Every cell runs in a fresh process -- `microecta`'s interning
tables never evict, so measuring depth 4 after depth 1 would let it reuse
depth 1's nodes and report a setup cost no first run can reproduce.

| depth | engine | first expr | exprs/s | alloc/expr | setup mem | retained after 100k |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | ECTA | 0.04 ms | 2,218,918 | 3.6 KB | 6.0 KB | 38.0 KB |
| 1 | handwritten | 0.03 ms | 552,279 | 14.1 KB | 3.1 KB | 41.6 KB |
| 2 | ECTA | 0.06 ms | 1,828,388 | 3.8 KB | 48.8 KB | 57.8 KB |
| 2 | handwritten | 0.04 ms | 197,621 | 38.2 KB | 6.3 KB | 106.0 KB |
| 3 | ECTA | 0.09 ms | 986,359 | 5.8 KB | 64.7 KB | 159.9 KB |
| 3 | handwritten | 0.10 ms | 67,269 | 112.3 KB | 50.1 KB | 354.6 KB |
| 4 | ECTA | 0.15 ms | 370,664 | 12.8 KB | 102.6 KB | 396.7 KB |
| 4 | handwritten | 0.57 ms | 21,981 | 335.8 KB | 83.9 KB | 1019.8 KB |

The ECTA generator draws 4x faster at depth 1 and 17x faster at depth 4,
allocating 4x to 26x less, and the gap widens with depth because the
handwritten generator's cost is per node while this one's is one decode per
sample. On the same machine an empty generator runs at 14.3M draws/s and a
single `chooseInt` at 2.6M, so at depth 1 the ECTA generator is already within
a small factor of one QuickCheck draw and cannot get much faster.

Setup is not the tax it might look like. It is a fraction of a millisecond
throughout, and by depth 4 it is *lower* than the handwritten generator's,
which has to build a tree of alternatives weighted by exact expression counts
before it can draw anything either.

Memory is the honest cost. Both generators grow while they are sampled --
neither is a fixed-size decoder -- and this one holds less at every depth, but
part of what it holds is in `microecta`'s process-global tables and is not
released when the generator is dropped. See the memory section of `microecta`'s
README before pointing this at a long-lived process.

Measured on the maintainer machine, three runs per cell, median of each metric.
The memory figures are deterministic; the rates move a few percent between
runs, and the ratios move with the QuickCheck and `random` versions in use.
Reproduce with:

```sh
cabal bench microecta-generator:typed-expression-speed --enable-optimization=2
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
