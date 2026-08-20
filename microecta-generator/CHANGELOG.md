# Changelog

## 0.1.0.0 - Unreleased

* Add indexed applicative generators represented by ECTA terms, conditioned
  joins backed by ECTA equality constraints, and QuickCheck integration with
  an explicit opaque `fromGen` boundary.
* Add `pool`, which samples an ordinary QuickCheck generator once and freezes
  its draws as a finite transparent ECTA generator. Repeated draws remain
  repeated ranks, so the pool retains their empirical weight.
* Rework the typed-expression reference language around integer and Boolean
  literals, unary `Not`, binary functions, and ternary `IfExpression`. Its
  independent depth-two reference checks all 27,054 generated expressions.
* Count and unrank uniform transparent generator languages without
  materializing applicative or joined Cartesian products.
* Expose deterministic rank replay and exact coverage counts, sample weighted
  transparent generators compositionally, and support direct three-way joins
  with two ECTA equality constraints.
* Add a two-tier exact-size oracle. `countsAtSize` reports how a grouped
  language's structural witnesses divide among retained keys; `massesAtSize`
  reports the actual sampler distribution, which may differ under weighted
  atomic choices. `pmfAtSize` aggregates arbitrary values by interpreting one
  size-class sampler, and `smallest` returns the first structural witness.
  Recursive grouped sampling now carries key masses through choices, products,
  regrouping, and `apply` instead of silently reverting to count weights.
* Build ECTA support only when `support` needs it. Finite joins retain support
  reduction as a lazy thunk once their live outcome groups prove non-emptiness.
  Recursive grouped application retains its support thunk too.
  Counting, masses, and sampling use their own retained indexes. Store
  `elements` in a boxed array so `groupBy` can enumerate ranks without repeated
  list walks.
* Add partition-preserving grouped generators (`Grouped`, built with `groupBy`
  from any transparent generator) so repeated joins compose compact ECTA
  supports and exact rank indices without enumerating prior layers.
* Add `keyed`, which declares one key for every member of an inspectable finite
  or recursive generator. It enters the grouped layer without enumerating the
  language and preserves the existing support, ranks, and distribution.
* Generalize keyed operation application to any arity: a `Sig` is written
  like a many-sorted operation signature (`leftKey :* rightKey :-> resultKey`),
  and
  the single `apply` joins the operation family with one argument family per
  signature component in one ECTA edge holding one equality constraint per
  argument.
* Condition flat generators with reified key equalities: `match` takes an
  `On` value such as `authenticatedUser :==: fileOwner`, conjoinable with
  `:&&:`, replacing the positional `matchOn`. The three-way `matchOn3` is
  gone; star-shaped conditioning belongs to the keyed layer (`apply`).
* Add `relate`, which conditions two flat generators with a Boolean relation
  over their projected keys. Transparent inputs evaluate the predicate once
  per live key pair and retain exact counts, ranks, probability masses, and
  direct sampling without rejection. `match` keeps its map-intersection fast
  path for equality.
* Add `frequencies`, the per-group weighted choice among grouped generators,
  so alternated layers such as depth-bounded languages stay grouped.
* Compile transparent uniform sampling: every outcome index now retains a
  symbolic decode plan (choices, mixed-radix products, maps) that lowering
  normalizes — maps pushed into leaves, nested choices spliced flat, small
  leaves tabulated — and compiles one flat decoder, narrowing each branch,
  product component, and counted size class to machine `Int` arithmetic when
  its local cardinality fits. Larger roots retain `Integer`; public replay
  ranks, masses, supports, and inspection are unchanged. Local narrowing
  improved the five-run depth-four typed-expression median by 13.5%, and the
  counted-size path improved bounded recursive sampling by 9.6%–20.2% at the
  measured size bounds.
* Compile non-uniform finite generators closed by `atomic` when they have at
  most 32,768 ranks and their smallest equivalent integer ticket space fits an
  `Int`. Ranks with the same ticket width share one payload array. Sampling
  binary-searches the distinct widths, then indexes the selected payload to
  recover the original structural rank and value. Other generators retain the
  compositional exact sampler. Recursive value sampling also avoids calculating
  replay ranks that `toGen` discards. Exact recursive tests preserve a declared
  9:1 atomic distribution while leaving structural ranks unchanged.
* Add `mapWithKey` for grouped generators, and `forAll` and `sized` to the
  QuickCheck adapter: `forAll` shrinks to the smallest failing member by
  first searching every structurally smaller member in size order
  (`smallerMembers`, capped), then shrinking components through
  `shrinkRank` - every shrink stays inside the generated language, the
  counterexample is globally size-minimal whenever the search reaches one,
  and the failing rank replays it deterministically; `sized` maps
  QuickCheck's size parameter to a generator, building each size once.
* Add qualified do-notation in `Data.ECTA.Gen.Do`, re-exported by the
  QuickCheck adapter: QuickCheck-style blocks for flat generators and for
  grouped operation application at any arity, with curated compile-time errors
  for monadic shapes.
* Add `recur`, which builds a generator from its own language. A recursive
  generator stands for the whole unbounded language: size classes counted by
  FEAT-style convolution instead of a cardinality, size-major ranks, and a
  `Mu` node for a support. `upToSize` bounds it to an ordinary finite
  generator, and `toGen` and `forAll` do that from QuickCheck's size
  parameter. Size classes and structural alternatives are selected from member
  counts; weighted finite choices closed with `atomic` retain their declared
  PMF inside the selected size.
  Bounding preserves ranks, so a counterexample replays under any bound.
  Finite generators keep their mixed-radix ranks and compiled decoder
  unchanged. Recursion must be guarded by `<*>` — an unguarded definition is
  rejected with `UnguardedRecursion` rather than left to hang — alternatives
  around a recursive occurrence must carry equal weights, and inspection
  that needs one term per member (`groupBy`, `match`, `pmf`, `countBy`)
  reports an error on a recursive language.
* Add `fromECTA`, which reads an existing automaton as a generator of the
  terms it accepts. Nodes become choices, edges become products under a
  size-one symbol, and interning ties `Mu` nodes into the same recursive
  size index `recur` uses, so a recursive automaton generates uniformly by
  size with the automaton itself as the support. The generated values are
  the accepted terms, so a bounded one supports `pmf`, `countBy`, and
  `groupBy`. Automata whose edges carry equality constraints are rejected
  with `CannotCountConstrainedEdges`: a constrained edge's count is the size
  of an intersection rather than a product of its children's counts.
* Add `atomic`, which treats every member of a finite transparent generator as
  one source choice while preserving its compact support, ranks, and decoder.
  Already finite inputs also keep their cardinality and distribution. An
  acyclic FTA read with `fromECTA` closes its whole finite language without
  enumerating its terms, so QuickCheck size can count complete commands in an
  outer recursion instead of taking an inner term-node prefix. Recursive
  inputs must cross an `upToSize` boundary first, and opaque inputs are
  rejected. An atomic finite language now also retains its sampler when used
  inside `recur` or `recurGrouped`. Counts, sizes, rank order, replay, and
  shrinking remain structural; only the probability of those ranks changes.
* Add `recurGrouped`, recursion for the grouped layer, where a language refers
  to itself through `apply` and the automaton carries equality constraints
  inside its own cycle. The key set is solved by a monotone fixpoint before
  the languages are tied over it, and all keys share one `Mu` node whose
  edges carry their key as a first child: an occurrence at one key is that
  node under an edge holding the key's label, with an equality constraint
  tying the two. `ungroup` and `atKey` are the exits into an ordinary
  recursive generator. The typed-expression language writes unary, binary,
  and ternary applications inside one `Mu`; two unfoldings accept the same 46
  members as the hand-unrolled depth-one generator.
* Add `oneof` and `oneofGrouped`, uniform choice among generators and among
  grouped generators. They are `frequency` and `frequencies` with equal
  weights, which is the only shape a recursive definition admits, so a
  recursive generator reads without weights it cannot use.
* Add `explain`, which turns an `ECTAGenError` into what it means and which
  combinator resolves it. Sampling a generator that could not be built now
  raises the case name together with that guidance instead of the
  constructor alone. An application whose *operation* family is recursive
  reports `RecursiveOperationFamily` rather than the general
  `UnboundedGenerator`, since only argument families may recurse. Internal
  invariant failures name themselves as bugs in this package so they are
  not mistaken for misuse.
* `recur` and `recurGrouped` return the body unchanged when it never uses
  the argument they pass it. Such a body is not recursive, so a finite one
  stays a finite generator with a cardinality and full inspection instead of
  becoming a language with neither.
