# Changelog

## 0.1.0.0 - Unreleased

Initial release: indexed applicative generators whose transparent regions are
represented as equality-constrained tree automata.

Requires `microecta` 0.2.0.0 or newer, and builds against `containers` 0.7 or
0.8, so GHC 9.14 uses the one it ships.

* Add the automaton-neutral `Data.Tree.Gen` ranked layer and
  `Data.Tree.FTA.Gen`. Ordinary finite FTA languages now have exact ranks,
  replay, QuickCheck sampling, shrinking, inspectable support, and the same
  `FTA.node "label" $ FTA.do ...` authoring form as the constrained adapters.
* Add `ECTAGen.node`, which closes a qualified-do block with its public domain
  constructor while preserving the equality constraints accumulated by a
  grouped join.

### Generators and sources

* `fromIndexed` and `elements` lift a finite indexed source into transparent
  ECTA structure; `fromGen` embeds an ordinary QuickCheck generator as an
  explicitly opaque region with no support, ranks, or inspection.
* `pool` samples an ordinary QuickCheck generator once and freezes its draws as
  a finite transparent generator. Repeated draws stay repeated ranks, so the
  pool keeps the native generator's empirical weight. `freeze` is `pool`
  with the draws fixed by a seed, so it is an ordinary transparent generator
  whose ranks are the same in every run.
* `fromECTA` reads an existing automaton as a generator of the terms it
  accepts. Nodes become choices, edges become products under a size-one symbol,
  and interning ties `Mu` nodes into the same recursive size index `recur`
  uses. The generated values are the accepted terms, so a bounded one still
  supports `pmf`, `countBy`, and `groupBy`. Automata whose edges carry equality
  constraints are rejected with `CannotCountConstrainedEdges`: a constrained
  edge's count is the size of an intersection rather than a product of its
  children's counts. Ambiguous automata are rejected with
  `AmbiguousAutomaton`: a node's count sums over its edges, which counts
  accepting runs, so a node with two edges accepting a common term would count
  that term twice and report it at two ranks. A node that accepts nothing at
  all, such as a `Mu` with no base case, counts nothing rather than an endless
  run of zeroes, which `unrank`, `sizeOfRank`, and `smallerMembers` used to
  walk forever on an out-of-range rank.
* `frequency`, `oneof`, and `uniformly` choose among generators, the last in
  proportion to their cardinalities so every member of the union is equally
  likely; `Functor` and `Applicative`
  composition tracks exact cardinalities without materializing the product.

### Conditioned joins

* `match` conditions two flat generators on a reified key equality, written as
  an `On` value such as `authenticatedUser :==: fileOwner` and conjoinable with
  `:&&:`. Keeping the projections as data lets each side be grouped by its own
  key, so the join intersects two key maps instead of testing sampled pairs.
* `relate` conditions two flat generators on a Boolean relation over their
  projected keys. The key types may differ and the relation need not be
  symmetric. Transparent inputs evaluate it once per live key pair and retain
  exact counts, ranks, masses, and direct sampling; an opaque input falls back
  to rejection.

### The grouped layer

* `Grouped key a` retains a projected key beside a compact support, so repeated
  joins compose without enumerating prior layers. `groupBy` classifies any
  transparent generator's outcomes, `keyed` declares one key for a whole
  inspectable generator without enumerating it, `regroupBy` reclassifies without
  enumerating values, `mapWithKey` maps with the key in hand, `atKey` and
  `ungroup` are the exits, and `frequencies`, `oneofGrouped`, and
  `uniformlyGrouped` choose among grouped generators group by group, the last
  in proportion to their cardinalities.
* `apply` applies a generated operation of any arity to one argument family per
  signature component, in a single ECTA edge holding one equality constraint per
  argument. A `Sig` is written like a many-sorted operation signature:
  `leftKey :* rightKey :-> resultKey`.

### Recursion

* `recur` builds a generator from its own language. A recursive generator stands
  for the whole unbounded language: size classes counted by FEAT-style
  convolution instead of a cardinality, size-major ranks, and a `Mu` node for a
  support. `upToSize` bounds it back to a finite generator, and `toGen` and
  `forAll` do that from QuickCheck's size parameter. Bounding preserves ranks, so
  a counterexample replays under any larger bound.
* Recursion must be guarded by `<*>`; an unguarded definition is rejected with
  `UnguardedRecursion` rather than left to hang. Alternatives around a recursive
  occurrence must carry equal weights, and a guarded cycle still needs a finite
  base member. `recur` and `recurGrouped` hand back a body that never reaches
  its own occurrence unchanged, so a finite body stays a finite generator, and
  hand back a body that failed to build with its own error rather than as a
  recursive language. `upToSize` and `atomic` cannot be applied to the
  occurrence itself, or to anything built from it, and say so with
  `BoundedRecursiveOccurrence`.
* `recurGrouped` does the same for the grouped layer, where recursion and
  equality constraints meet in one cycle. The key set is solved by a monotone
  fixpoint before the languages are tied over it, and all keys share one `Mu`
  node whose edges carry their key as a first child, with an equality constraint
  tying an occurrence to its key.
* `atomic` treats every member of a finite generator as one source choice while
  preserving its support, ranks, decoder, cardinality, and distribution. That
  distribution is retained inside each recursive size class. An acyclic
  automaton read with `fromECTA` can therefore close its whole finite language
  without enumerating it or taking an inner size prefix.

### Inspection

* `support`, `cardinality`, `sizes`, `countAtSize`, `minimumSize`, `countBy`,
  `pmf`, `unrank`, `sizeOfRank`, `smallest`, `smallerMembers`, and `shrinkRank`
  report exact structure. `unrank` is deterministic replay; ranks are stable
  while the generator definition and its finite sources are.
* `countsAtSize` reports how a grouped language's members divide among retained
  keys, and `massesAtSize` reports the sampling distribution over those keys,
  which differs from the counts under weighted atomic choices. `pmfAtSize`
  aggregates arbitrary values by interpreting one size-class sampler.
* Every failure is an `ECTAGenError`, and `explain` says what it means and which
  combinator resolves it. `BoundedRecursiveOccurrence` covers `upToSize` or
  `atomic` applied to the recursive occurrence inside the body defining it,
  which is ill-founded rather than merely unbounded. Sampling a generator that could not be built raises
  the case name together with that guidance. Internal invariant failures name
  themselves as bugs in this package so they are not mistaken for misuse.

### QuickCheck integration

* `toGen`, `toGenWithRank`, and their `Either`-returning variants sample through
  the generator type QuickCheck expects, bounding recursive generators from the
  size parameter. `sized` maps the size parameter to a generator, building and
  compiling each size once.
* `forAll` shrinks to the smallest failing member: it first searches every
  member of strictly smaller size, in size order (`smallerMembers`, capped by
  `smallerMemberLimit`), then shrinks components through `shrinkRank`. For a
  recursive generator those component candidates come from the form bounded at
  the failing member's size, since `shrinkRank` has none of its own for a
  recursive language; bounding preserves ranks, so they replay unchanged. Every
  candidate is a member of the generated language, and the failing rank is
  printed so `unrank` replays it. A generator with an opaque region has no
  ranks, so `forAll` tests it by sampling with no shrinking.
* `Data.ECTA.Gen.Do` provides qualified do-notation for flat generators and for
  grouped operation application at any arity, with curated compile-time errors
  for monadic shapes.

### Performance

* Uniform transparent languages are counted and unranked without materializing
  applicative or joined Cartesian products.
* Every outcome index retains a symbolic decode plan - choices, mixed-radix
  products, maps - that lowering normalizes (maps pushed into leaves, nested
  choices spliced flat, small leaves tabulated) and compiles into one flat
  decoder, narrowing each branch, product component, and counted size class to
  machine `Int` arithmetic when its local cardinality fits.
* Non-uniform finite generators closed by `atomic` are compiled to one exact
  ticket selection when they have at most 32,768 ranks and their smallest
  equivalent integer ticket space fits an `Int`. Other generators retain the
  compositional exact sampler.
* ECTA support is demand-driven: counting, masses, replay, and sampling use
  their own retained indexes, and finite joins keep support reduction as a
  thunk. `support` forces it.
