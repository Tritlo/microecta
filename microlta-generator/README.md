# microlta-generator

`microlta-generator` is the Liquid Tree Automata adapter for the ranked engine
in `microecta-generator`. Building the language is pure. `compile` is the
finite-witness fallback; `compileRelational` preserves a surface DSL's
applicative structure and compiles semantic relations as indexed ECTA joins;
`compileAutomaton` performs transition-level semantic pruning, then counts and
unranks the equality-free graph. All three use Liquid Fixpoint/Z3 only at the
compilation boundary and return a pure `Compiled` value.

```haskell
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE QualifiedDo #-}

import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.Guard (isSubtypeOf)
import Data.LTA.Refinement ((.==.), (.>=.))

choices = LTA.pool
  [ LTA.refined 0 "non-negative" (value .>=. 0)
  , LTA.refined 1 "one"          (value .==. 1)
  ]

liquidPairs =
  LTA.node "pair" subtypePair $ LTA.do
    left  <- choices
    right <- choices
    LTA.pure (left, right)

subtypePair actual expected = actual `isSubtypeOf` expected
```

The do-block only describes independent children. The root symbol and guard
live at `node`, where they belong. Its result refinement defaults internally to
the universal predicate; use `refinedNode` for one fixed result refinement or
`refinedNodeBy` when each generated result computes its own. A value-dependent
child choice is rejected at compile time; express that relationship with the
liquid guard.
The guard function receives symbolic constructor arguments in the same order
as the child generators below it. For guards over nested terms,
`descendant left [1]` selects the second child below `left`. The common cases
read as ``argument `requires` nonZero``, ``actual `isSubtypeOf` expected``, and
`withActualFor actual formal dependentResultCheck`. Raw `Guard` constructors
and `argument` remain available for unusual programmatic guards.

After the one solver phase, QuickCheck and replay are pure:

```haskell
Right compiled <- LTA.compileRelational solver liquidPairs

quickCheck $ LTA.forAll compiled (uncurry (>=))
replayed = LTA.select failingRank compiled
```

Applicative construction retains a `Data.Tree.Gen` rank plan. A pair of
languages with cardinalities `m` and `n` is represented by one `PlanAp` and a
mixed-radix decoder, not a list of `m * n` outcomes. The finite `compile`
fallback still walks those ranks when an arbitrary Haskell function such as
`refinedNodeBy (a -> Refinement)` makes the refinement depend on an opaque
value. `compileRelational` avoids that scan when node refinements are fixed or
are declared from child-root groups with `refinedNodeByRoots`. That is an
explicit generator-layer boundary, not part of LTA semantics.

The automaton path avoids that scan:

```haskell
Right compiled <- LTA.compileAutomaton solver automaton
term <- LTA.select replayRank compiled
```

`microlta.prune` first removes invalid transitions while retaining an LTA.
`compileAutomaton` then requests the optional `pruneToECTA` lowering when every
residual constraint is expressible as positive ECTA equality.
Dynamic programming then computes state cardinalities, and the selected rank
walks those counts to construct one accepted `LiquidTerm`. This is the same
materialization boundary as MicroECTA: the graph stays symbolic; only the term
being observed is materialized.

Semantic guards are compiled away by partitioning the states reached at their
observed positions. Syntactic equality remains a Boolean LTA atom until the
optional lowering converts a positive conjunction to ECTA `EqConstraints`.
Arbitrary subtree equality is not an ordinary FTA language, so
`compileAutomaton` routes a positive equality residual through MicroECTA rather
than multiplying independent child counts. The first equality-aware backend
materializes the finite accepted language; it is a correctness baseline for a
future symbolic ranker, not a performance claim. Negated or disjunctive equality
is valid LTA syntax but is outside the ECTA lowering fragment.

The relational surface path has that rank plan because it creates each
solver-approved group product through MicroECTA's grouped join machinery. It
asks the solver once per live observation tuple and never visits the values
inside a group. The same plan supplies valid structural shrink ranks on demand,
without precomputing a table proportional to the language. Hand-authored
positive equality-constrained automata use the correctness-first MicroECTA
enumeration path. A non-materializing general ECTA counter remains separate
work.

This first relational path is deliberately narrow: alternatives must have unit
weights, result refinements must be fixed or supplied from child-root groups,
and surface `isSameTermAs` constraints currently report
`RelationalSyntacticEqualityUnsupported`. The equality is still preserved by
the authoritative LTA path; what is missing is a rank plan that threads the
surface term's own paths through the ECTA support. Use the finite `compile`
fallback for small value-computed or weighted languages, and `compileAutomaton`
for finite handwritten automata. These are explicit compiler boundaries, not
silent changes of distribution.

The pool need not be part of a long-lived specification. It can be sampled and
frozen only for one generation run:

```haskell
compiled <- LTA.compileSampled solver $ do
  lefts  <- LTA.samplePool 32 nativeRefinedInt
  rights <- LTA.samplePool 8  nativeRefinedInt
  pure $
    LTA.node "pair" subtypePair $ LTA.do
      left  <- lefts
      right <- rights
      LTA.pure (left, right)
```

Here the two pools are sampled independently. Sample once and use the same
`LTAGen` at both child positions when they should share a universe. The pools
remain fixed inside `compiled`; changing them for each individual test would
make ranks, replay, and shrinking unstable and would also invoke Z3 per test.
Independent pool sizes multiply: the example presents 32 x 8 candidate pairs
to the finite pool compiler before its guards reject any of them. Use an ECTA
grouped join when a relation can be indexed by finite keys; use a smaller or
native-shrunk frozen pool when the relation genuinely needs SMT entailment.

For replay across process runs, fix each pool with a seed, just as in
`microecta-generator`:

```haskell
lefts  = LTA.freeze 20260902 32 nativeRefinedInt
rights = LTA.freeze 20260903 8  nativeRefinedInt
```

The same seed, size, and native generator produce the same pool ranks. Reuse a
single frozen value at several child positions when they should range over one
shared universe; use distinct seeds for independent pools.

### Push direct refinements into opaque sampling

Freezing first can waste most of a small native pool on values the LTA will
immediately reject. An `OpaqueSource` receives the unconditional refinements
required at its direct child position, so an adapter for the native value can
move those requirements into `suchThat` before the pool is frozen:

```haskell
offsetSource =
  LTA.opaqueSource
    (\requirements ->
      chooseInt (-128, 127) `suchThat` \offset ->
        all (`offsetSatisfies` offset) requirements)
    (fromString . ("offset-" <>) . show)
    exactOffset

sampledReads =
  LTA.sampledNode "read-at" (\offset -> offset `requires` validOffset) $
    PageRead <$> LTA.opaquePool 32 offsetSource
```

This leaves the range predicate in the LTA specification; it is not duplicated
as a second handwritten generator contract. `offsetSatisfies` is the small
boundary that interprets the refinements this opaque Haskell type understands.
The library cannot generically evaluate a Liquid Fixpoint expression over an
arbitrary Haskell value.

Several `opaquePool` calls may be combined applicatively. `sampledNode` routes
the first guard argument's requirements to the first pool, the second to the
second, and so on. It deliberately pushes only positive, direct-child
`requires` clauses (and conjunctions of them). Subtyping between children,
substitution, disjunction, negation, and nested paths still need the assembled
term and remain solver work.

The optimization is not trusted: `compile` checks the exact refinement attached
to every sampled value against the original guard with Z3. A partial adapter
therefore leaves extra candidates for compilation to reject; an incorrect
adapter can discard useful candidates but cannot admit an invalid one. As with
any `suchThat`, use this only for reasonably dense predicates. Constructive
native generation is preferable when rejection sampling would be sparse or
unsatisfiable.

The executable
[`OpaquePoolSpec`](test/Data/LTA/OpaquePoolSpec.hs) compares this with the
freeze-first route on a partial page read, checks every retained offset, and
uses a two-pool division example to verify positional routing.

## What the LTA adds

An FTA says which constructor shapes exist. An ECTA additionally says that two
paths must contain the same term. An LTA can say that one path's refinement
implies another predicate, including after substituting actual argument names
for formal parameters. That permits constraints such as:

```haskell
safeDivision =
  LTA.node "divide" validDenominator $ LTA.do
    numerator   <- integers
    denominator <- integers
    LTA.pure (Divide numerator denominator)

validDenominator _ denominator = denominator `requires` nonZero
```

For dependent application, put the result type, function, and argument in the
term exactly as the paper does, and give names to the nested type positions:

```haskell
applicationGuard result function argument =
  allOf
    [ argument `isSubtypeOf` descendant function [1] -- input type
    , withActualFor argument (descendant function [0]) $
        descendant function [2] `isSubtypeOf` result -- output type
    ]
```

The finite fallback checks every frozen candidate rank, removes those whose
complete guard is false, and returns a pure language. This remains useful for
opaque value-dependent refinements. A compositional surface language should use
`compileRelational`; a language already expressed as an automaton should use
`compileAutomaton`, so pruning happens on transitions instead.

## Flagship: typed state-machine traces

[`Data.LTA.StateMachineTraceLanguage`](common/Data/LTA/StateMachineTraceLanguage.hs)
is the LTA step in the repository's worked progression. The FTA example has
only integer expression shapes; the ECTA example adds Boolean result types;
this example carries those types through time as a stack-machine state.

The abstract contract is the familiar typed reverse-Polish calculator:

```text
Push TInt  : Stack s                   -> Stack (TInt  ': s)
Add        : Stack (TInt ': TInt ': s) -> Stack (TInt  ': s)
Equal      : Stack (a    ': a    ': s) -> Stack (TBool ': s)
Pop        : Stack (a    ': s)         -> (a, Stack s)
```

Those are explanatory signatures, not GADT constructors. The public Haskell
values stay ordinary. The surface specification recursively builds a prefix
and one command, grouped by their root refinements. The liquid guard decides
which group tuples survive, and `refinedNodeByRoots` propagates the resulting
output state without decoding the traces hidden inside those groups:

```haskell
extendTrace prefixes =
  LTA.refinedNodeByRoots
    "step"
    (stateRefinement . prefixFinalState)
    stepRefinementFromRoots
    validStep $ LTA.do
      prefix  <- prefixes
      command <- commandContracts
      LTA.pure (predictPrefixStep prefix command)

validStep previous command =
  allOf
    [ previous `isSubtypeOf` command
    , withActualFor previous (descendant command [0]) $
        descendant command [1] `isSubtypeOf` root
    ]

Right compiled <- LTA.compileRelational solver (tracesOfLength length)
```

The first guard says that the preceding trace's output state inhabits the next
command's input space. The second substitutes that actual state for the
command's formal `model` and proves its output formula implies the new trace
root. With the top stack type in the low bits, for example, pushing an integer
has output `v = 2 * model + 1`, while `Add` accepts two leading integer tags and
has output relation `model = 2 * v + 1`.

The stack depth is bounded only to keep the refinement-key space finite. There
is one liquid schema per operation; each compilation layer relates the live
prefix-state and command-contract groups instead of expanding complete command
sequences. This is where the LTA is materially clearer than an ECTA: a bounded
ECTA could tabulate every valid state pair, but it cannot state and reuse the
dependent arithmetic transition itself.

Following the
[quickcheck-state-machine workflow](https://well-typed.com/blog/2019/01/qsm-in-depth/),
the whole trace is generated before execution. Every retained event predicts
its before-state, response space, and after-state. The specs ask Z3 to prune the
LTA, check its independently computed cardinalities, enumerate all 132 accepted
traces of length three, and replay each through an independent abstract model
and a separate concrete integer/Boolean interpreter. A smaller surface-DSL
variant also verifies guarded shrinking. The final QuickCheck property needs no
implication or `suchThat` filter.

## LTA-biased case study: sized-vector pipelines

The stack machine is a good stateful progression, but its bounded stack shapes
can still be tabulated by a sufficiently patient FTA author. The more
LTA-native example is
[`Data.LTA.SizedVectorLanguage`](common/Data/LTA/SizedVectorLanguage.hs): a
dependent vector-expression language in which result sizes are arithmetic
refinements rather than finite type tags.

```text
append xs ys    : Vector n -> Vector m -> Vector (n + m)
take k xs       : 0 <= k <= n => Vector n -> Vector k
zipWith (+) x y : Vector n -> Vector n -> Vector n
index i xs      : 0 <= i < n => Vector n -> Int
```

One operation layer is ordinary applicative LTA syntax:

```haskell
takenVectors maximumLength children =
  LTA.refinedNodeBy "take" vectorLength validTake $ LTA.do
    result    <- possibleLengths maximumLength
    _function <- takeFunction
    count     <- possibleLengths maximumLength
    input     <- children
    LTA.pure $ SizedVector
      (Take (numberValue count) $ vectorExpression input)
      (numberRefinement result)

validTake result function count input =
  withActualFor count (takeCountFormalAt function) $
    allOf
      [ vectorLengthAt input `isSubtypeOf` function
      , takeResultAt function `isSubtypeOf` result
      ]
```

The `takeFunction` contract says that its input length is at least the formal
`k` and its result is exactly `k`. The guard substitutes the selected count for
that formal. `append` substitutes both input lengths into `out = n + m`;
`zipWith` substitutes the left length and requires the right length to inhabit
the same input space. A stable result-length child lets these proofs compose at
the next expression layer without exposing a refinement wrapper in `Program`.

The one-layer language contains 20 pipelines and exactly 44 safe indexing
programs. The tests enumerate them, check every result refinement against an
independent list interpreter, and execute the deliberately partial indexer over
every accepted program.

This is the specification-leverage example. A handwritten exact-uniform
generator must group every recursive sublanguage by result length, derive the
append, take, and zip cardinality recurrences for those groups, weight each
constructor by its number of valid completions, and repeat the bookkeeping for
the final index. The LTA source states the four dependent contracts once. This
small surface compiler is intentionally an executable clarity example; large
recursive languages should be compiled as automata so terms stay symbolic.

## Sampling performance

The typed stack-machine benchmark separates seven useful paths:

- **naive** draws uniformly from all nine raw commands at every position and
  rejects the complete sequence if abstract replay fails;
- **QSM online** follows the normal state-machine-testing shape: choose a
  command admitted by the current model, advance the model, and continue;
- **bespoke** is ordinary compositional QuickCheck code which weights every
  valid next command by its number of complete suffixes;
- **ranked** is the strongest handwritten control: it duplicates the count and
  global-unrank algorithm in application code and constructs `Trace` directly;
- **LTA do** preserves the qualified-do recipe, groups its live refinement
  observations, and lowers solver-approved tuples through ECTA joins;
- **LTA materialized** prunes the explicit automaton, constructs a selected
  `LiquidTerm`, then decodes it to `Trace`;
- **LTA fused** uses the same explicit automaton but folds a selected run
  directly into `Trace`.

Naive rejection, bespoke, ranked, and all three LTA rows are uniform over the
same exact trace language. QSM online has the same support but intentionally has
a different distribution: choosing uniformly at each prefix gives extra
probability to traces passing through states with fewer valid continuations.
That is usually the right engineering trade in state-machine testing. As in
[quickcheck-state-machine](https://well-typed.com/blog/2019/01/qsm-in-depth/),
the complete trace is generated before execution; after a failure,
`qsmTraceShrinks` removes commands and replays the remainder so dependencies
whose producers disappeared are rejected.

Each successful cell draws 20,000 traces. It runs in a fresh process with a
30-second wall-clock limit and is the median of three runs. The first-sample
column includes all setup—in an LTA row, that includes starting Z3, compiling
the semantic constraints, building the rank index, and drawing once.
Steady-state sampling is pure. After an engine times out at one length, the
harness skips its larger cells and reports `after timeout`.

The crossover and deep-scaling rows are:

| length | members | engine | first sample | samples/s | alloc/sample | setup mem | retained after 20k |
| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 8 | 342,136 | naive | 0.07 ms | 6,280 | 1.23 MB | 33.3 KB | 35.3 KB |
| 8 | 342,136 | QSM online | 0.02 ms | 179,795 | 42.6 KB | 32.7 KB | 34.7 KB |
| 8 | 342,136 | bespoke | 0.07 ms | 127,266 | 37.5 KB | 47.6 KB | 32.91 MB |
| 8 | 342,136 | ranked | 0.06 ms | 394,719 | 11.7 KB | 41.4 KB | 43.4 KB |
| 8 | 342,136 | LTA do | 71.08 ms | 277,200 | 19.4 KB | 1.18 MB | 1.20 MB |
| 8 | 342,136 | LTA materialized | 356.54 ms | 112,936 | 58.0 KB | 199.4 KB | 175.8 KB |
| 8 | 342,136 | LTA fused | 355.83 ms | 111,456 | 56.3 KB | 199.6 KB | 176.0 KB |
| 10 | 8,567,224 | naive | 0.20 ms | 1,913 | 3.97 MB | 33.4 KB | 35.5 KB |
| 10 | 8,567,224 | QSM online | 0.03 ms | 139,808 | 53.6 KB | 32.7 KB | 34.7 KB |
| 10 | 8,567,224 | bespoke | 0.10 ms | 69,854 | 57.5 KB | 54.3 KB | 74.04 MB |
| 10 | 8,567,224 | ranked | 0.07 ms | 302,517 | 14.3 KB | 43.2 KB | 45.3 KB |
| 10 | 8,567,224 | LTA do | 88.30 ms | 233,495 | 23.6 KB | 1.47 MB | 1.52 MB |
| 10 | 8,567,224 | LTA materialized | 430.83 ms | 89,208 | 72.1 KB | 227.4 KB | 203.8 KB |
| 10 | 8,567,224 | LTA fused | 422.05 ms | 91,050 | 69.3 KB | 227.6 KB | 203.9 KB |
| 12 | 215,809,688 | naive | **timeout (30s)** | — | — | — | — |
| 12 | 215,809,688 | QSM online | 0.03 ms | 118,229 | 64.5 KB | 32.7 KB | 34.7 KB |
| 12 | 215,809,688 | bespoke | 0.10 ms | 52,289 | 77.4 KB | 56.6 KB | 118.24 MB |
| 12 | 215,809,688 | ranked | 0.08 ms | 253,498 | 16.0 KB | 45.1 KB | 47.1 KB |
| 12 | 215,809,688 | LTA do | 101.66 ms | 191,694 | 26.9 KB | 1.78 MB | 1.84 MB |
| 12 | 215,809,688 | LTA materialized | 486.62 ms | 74,372 | 85.4 KB | 255.1 KB | 231.5 KB |
| 12 | 215,809,688 | LTA fused | 490.85 ms | 76,824 | 81.5 KB | 255.2 KB | 231.6 KB |
| 20 | 90,356,263,022,904 | QSM online | 0.04 ms | 68,492 | 108.4 KB | 32.7 KB | 34.7 KB |
| 20 | 90,356,263,022,904 | bespoke | 0.15 ms | 23,546 | 157.6 KB | 73.9 KB | 303.87 MB |
| 20 | 90,356,263,022,904 | ranked | 0.12 ms | 140,412 | 25.1 KB | 52.5 KB | 54.6 KB |
| 20 | 90,356,263,022,904 | LTA do | 167.76 ms | 121,021 | 42.6 KB | 3.02 MB | 3.13 MB |
| 20 | 90,356,263,022,904 | LTA materialized | 748.54 ms | 45,329 | 143.6 KB | 372.8 KB | 349.2 KB |
| 20 | 90,356,263,022,904 | LTA fused | 758.00 ms | 46,578 | 132.7 KB | 373.0 KB | 349.4 KB |
| 40 | 11,207,052,560,775,737,667,197,734,440 | QSM online | 0.05 ms | 34,359 | 218.0 KB | 32.7 KB | 34.7 KB |
| 40 | 11,207,052,560,775,737,667,197,734,440 | bespoke | 0.32 ms | 8,494 | 365.0 KB | 122.1 KB | 778.94 MB |
| 40 | 11,207,052,560,775,737,667,197,734,440 | ranked | 0.23 ms | 57,282 | 50.7 KB | 76.4 KB | 78.4 KB |
| 40 | 11,207,052,560,775,737,667,197,734,440 | LTA do | 333.75 ms | 59,187 | 84.0 KB | 6.15 MB | 6.41 MB |
| 40 | 11,207,052,560,775,737,667,197,734,440 | LTA materialized | 1,411.81 ms | 21,378 | 307.7 KB | 653.1 KB | 629.5 KB |
| 40 | 11,207,052,560,775,737,667,197,734,440 | LTA fused | 1,416.92 ms | 22,158 | 263.8 KB | 653.2 KB | 629.6 KB |

The ordinary bespoke generator wins at very short lengths, but LTA do overtakes
it after length four. At length 40 the generic relational compiler produces
59,187 traces/s versus 8,494/s: a 7.0x throughput win, while retaining 6.41 MB
rather than 778.94 MB after the fixed workload. It pays 334 ms once, then reuses
the compiled ECTA rank plan instead of rebuilding weighted QuickCheck choices
through every generated suffix.

The hand-ranked row remains the specialization ceiling. At length 40 it is
within 4% of LTA do in throughput and allocates only 50.7 KB per trace versus
84.0 KB. Treat that throughput difference as a tie, not a claim that a generic
compiler has defeated its own hand-coded algorithm. QSM online is the pragmatic
state-machine baseline: LTA do is 1.7x faster in this run and remains uniform
over complete traces, at the cost of a solver-backed setup phase and a larger
retained rank index.

Naive rejection cracks at length 12 for the 20,000-sample workload. At length
10 it is already 122x slower than LTA do and allocates 3.97 MB per accepted
trace.

The first benchmark run made repeated solver work visible: length four took
6.50 seconds to compile and length five timed out, despite only 115 distinct
entailment requests among 34,073 requests at length four. Caching exact
obligations for one compile and checking a generated witness directly, rather
than first turning it into a singleton automaton, cut length-four setup to 188
ms and made length five complete in 1.94 seconds.

Replacing the outcome lists with `PlanAp` removed product allocation but did
not remove the work: the old surface compiler still visited `11^6 = 1,771,561`
ranks to discover 13,760 valid traces. Retaining the applicative recipe changes
that algorithm. Children are grouped by only the refinements their parent
observes; the solver selects live key tuples, and MicroECTA counts their products
without visiting members. The same qualified-do source now reaches length 40.

The direct automaton rows isolate decoding cost. At length 40, fusing the
bottom-up `Trace` decoder saves 43.9 KB per sample—14.3%—and gives a small
throughput improvement over materializing and immediately traversing a
`LiquidTerm`. The remaining gap is in generic automaton unranking. Conversely,
LTA do's retained relational index uses 6.15 MB of setup memory versus about
653 KB for the direct automaton; reducing that compact-index constant and using
a persistent worklist in automaton pruning are the next focused opportunities.

## Equality theory cost: ECTA versus LTA

The typed-expression flagship also has a deliberately equivalent liquid
encoding in
[`Data.LTA.EqualityTypedExpressionLanguage`](common/Data/LTA/EqualityTypedExpressionLanguage.hs).
`TInt` is the refinement `v = 0` and `TBool` is `v = 1`. Each application LTA
contains candidate ground child states, and Z3 retains precisely those whose
refinements imply the operation's expected input equalities. This expresses the
same language as the ECTA's path-equality join without adding LTA-only power.

This control uses the same rank order and fixed QuickCheck seed for both
engines, draws 20,000 values per cell, and forces the complete expression tree.
The checksum matched at every depth, in addition to the LTA cardinality being
checked against the independent ECTA count.

| depth | members | engine | first sample | samples/s | alloc/sample | setup mem | retained after 20k |
| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 42 | ECTA | 0.05 ms | 2,158,429 | 3.6 KB | 36.9 KB | 37.7 KB |
| 1 | 42 | LTA equality | 4.16 ms | 1,082,720 | 6.9 KB | 61.7 KB | 38.1 KB |
| 2 | 27,054 | ECTA | 0.06 ms | 1,719,247 | 3.8 KB | 47.3 KB | 58.4 KB |
| 2 | 27,054 | LTA equality | 5.08 ms | 427,881 | 15.7 KB | 63.4 KB | 39.8 KB |
| 3 | 8,887,065,932,466 | ECTA | 0.08 ms | 878,966 | 5.8 KB | 61.9 KB | 137.3 KB |
| 3 | 8,887,065,932,466 | LTA equality | 5.25 ms | 143,836 | 44.8 KB | 65.2 KB | 41.6 KB |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | ECTA | 0.16 ms | 323,076 | 12.8 KB | 98.6 KB | 334.3 KB |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | LTA equality | 5.28 ms | 53,521 | 134.1 KB | 66.9 KB | 43.3 KB |

For equality alone, the ECTA is the right tool. Its setup stays below 0.2 ms;
the LTA pays about 4–5.3 ms to start Z3 and prune the guarded graph. The LTA
sampler is 2.0x slower at depth one and 6.0x slower at depth four, with 10.5x
the per-sample allocation at depth four. That allocation is the cost of
constructing an annotated `LiquidTerm` and decoding it to the same Haskell AST.
The language itself remains symbolic: even the roughly 4.95e38-member
depth-four language occupies only about 67 KB of LTA setup memory.

Measured with GHC 9.12.2 and `-O2` on the maintainer's Apple Silicon machine on
2026-09-03. Reproduce either LTA table, or all four repository tables, from the
repository root with:

```sh
cabal bench microlta-generator:state-machine-trace-speed --enable-optimization=2
cabal bench microlta-generator:typed-expression-constraint-cost --enable-optimization=2
./scripts/benchmark-generators.sh
```

## A second dependent example: safe buffer programs

[`Data.LTA.SafeBufferLanguage`](common/Data/LTA/SafeBufferLanguage.hs) gives
buffers and indexes symbolic integer names, records the surrounding Liquid
environment as solver assumptions, and generates two deliberately partial
operations:

```haskell
safeReads = LTA.node "read-at" validRead $ LTA.do
  buffer <- sourceBuffers
  function <- readFunction
  ~(_, index) <- indexes
  LTA.pure (ReadAt (bufferExpression buffer) index)

validRead buffer function index =
  withActualFor buffer (descendant function [0]) $
    index `isSubtypeOf` descendant function [1]
```

The function's input refinement is `0 <= v && v < n`. Substitution replaces
the formal `n` with the selected buffer-length symbol; Z3 then uses facts such
as `tripleLength = 3` to retain indexes 0, 1, and 2 while rejecting -1 and 3.

The same module demonstrates a two-argument dependent result. Append declares
`resultLength = n + m`, substitutes both selected buffer lengths, and uses
`refinedNodeBy` to retain the proven result refinement. A later `head` node can
therefore prove the appended buffer non-empty. The property itself needs no
precondition:

```haskell
withZ3Assuming solverDeclarations solverAssumptions $ \solver -> do
  Right compiled <- LTA.compile solver safePrograms
  quickCheck $ LTA.forAll compiled $ \program ->
    programIsSafe program && safeResult program == Just (runProgram program)
```

The specs enumerate all 14 accepted programs, verify exact append lengths, and
run the partial interpreter through QuickCheck. This is the distinction from
an ECTA key: the accepted combinations depend on arithmetic implication under
an environment, not equality of a finite classification tag.

## Refinement shrinking, similarity, and pools

A refined pool contributes potential local replacements. Compilation asks Z3
whether the current refinement implies each candidate refinement. Strict
implication is a shrink; logically equivalent entries shrink toward the earlier
pool rank to keep the graph acyclic.

The refinement is a trusted annotation on the Haskell value. The generic
library cannot prove that an arbitrary `a` satisfies a Liquid Fixpoint
predicate without an explicit encoding for `a`; callers that require that proof
must validate the encoding before constructing the pool.

Those local replacements are lifted through `node` products. The complete LTA
guard is then decisive: a replacement that makes the whole tree invalid is
never handed to QuickCheck. The compiler follows its shrink edges through that
invalid intermediate and reconnects any valid descendants.

For the example, the raw product is:

```text
(0,0)  accepted
(0,1)  rejected: non-negative does not entail exactly-one
(1,0)  accepted
(1,1)  accepted
```

`(1,1)` therefore shrinks first to `(1,0)` and can reach `(0,0)` without ever
emitting `(0,1)`. `samplePool n native` does the same thing for a finite pool
drawn once from a native QuickCheck generator. Repeated draws remain repeated
ranks, retaining empirical weight, while implication supplies semantic shrink
edges.

`compiledSupport` records which lower layer backs the ranked plan.
`EqualitySupport` contains the ECTA-shaped generic FTA returned by semantic
pruning; `RelationalSupport` contains the native hash-consed ECTA built by the
grouped surface compiler. `Data.Tree.Gen` and `Data.Tree.Gen.QuickCheck` provide
the shared sampling and shrinking machinery. Weights influence sampling but do
not duplicate replay ranks. Transition refinements are part of the support
alphabet, so replay cannot invent a new annotation for an existing constructor.

Similarity minimisation remains separate and opt-in because dropping a
syntactically different value is often the wrong trade-off for testing. Declare
the non-liquid type class when semantic representatives are what you want:

```haskell
Right representatives <-
  LTA.minimizePoolBy solver operationKind candidates
```

`minimizePoolBy` represents the entries as a one-state LTA, invokes the core
`similarity` and `minimize` procedures, then turns the retained transitions back
into a pool. Within each class, a subtype replaces its supertype, equivalent
entries keep the earlier rank, and incomparable entries remain. The generator
therefore does not carry a second imitation of LTA minimization; it is an
adapter over the automaton operation. Ordinary pools are never reduced
implicitly.

## Recursive LTAs

The core accepts recursive LTAs as long as guards do not point into cyclic
states. QuickCheck still needs a finite run, so unfold with an explicit
constructor-depth bound and then compile normally:

```haskell
Right bounded  = LTA.fromAutomatonUpToDepth 6 recursiveLTA
Right compiled <- LTA.compile solver bounded
```

Depth zero keeps nullary transitions; every recursive constructor consumes one
unit. Ranks remain deterministic inside the bounded language.

The compiler discovers every implication relation inside a pool, which is
quadratic in the number of distinct pool refinements. That is useful for small
semantic universes. A production version should let a native value shrinker
propose a sparse candidate graph for large sampled pools, with Z3 validating
only those edges.

Enter the repository's `nix-shell` to place Z3 on `PATH`, then run the complete
example:

```sh
cabal run liquid-pairs
```
