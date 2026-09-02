# microlta-generator

`microlta-generator` is the Liquid Tree Automata adapter for the ranked engine
in `microecta-generator`. Building the language is pure. `compile` checks a
surface-DSL language; `compileAutomaton` performs transition-level LTA pruning,
then counts and unranks the reduced graph. Both use Liquid Fixpoint/Z3 only at
the compilation boundary and return a pure `Compiled` value.

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
Right compiled <- LTA.compile solver liquidPairs

quickCheck $ LTA.forAll compiled (uncurry (>=))
replayed = LTA.select failingRank compiled
```

Applicative construction retains a `Data.Tree.Gen` rank plan. A pair of
languages with cardinalities `m` and `n` is represented by one `PlanAp` and a
mixed-radix decoder, not a list of `m * n` outcomes. The surface `compile` path
still walks those ranks when an arbitrary Haskell function such as
`refinedNodeBy (a -> Refinement)` makes the refinement depend on an opaque
value. That is an explicit generator-layer cost, not part of LTA semantics.

The automaton path avoids that scan:

```haskell
Right compiled <- LTA.compileAutomaton solver automaton
term <- LTA.select replayRank compiled
```

`microlta.prune` first removes invalid transitions from the LTA itself.
Dynamic programming then computes state cardinalities, and the selected rank
walks those counts to construct one accepted `LiquidTerm`. This is the same
materialization boundary as MicroECTA: the graph stays symbolic; only the term
being observed is materialized.

Semantic guards are compiled away by partitioning the states reached at their
observed positions. A residual syntactic `Same` guard is different: arbitrary
subtree equality is not an ordinary FTA language, so `compileAutomaton` returns
`ResidualGuard` instead of multiplying independent child counts. Such a guard
must stay in the ECTA-style constrained layer until a constraint-aware counter
is selected.

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

The surface compiler checks every frozen candidate rank, removes those whose
complete guard is false, and returns a pure language. This is useful when the
specification starts from arbitrary Haskell pools. A language already expressed
as an LTA should use `compileAutomaton`, so pruning happens on transitions
instead.

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
values stay ordinary. The actual specification is an acyclic LTA whose states
are indexed by `(prefix length, output stack)`. Command input/output contracts
are reusable child states. A layer proposes possible preceding states and
result states; the liquid guard decides which transitions survive:

```haskell
stepTransitions prefixLength output =
  [ Transition "step" (stateRefinement output)
      [ traceState (prefixLength - 1) input
      , commandState contractRank
      ]
      (validStep (argument 0) (argument 1))
  | input        <- stackStates
  , contractRank <- [0 .. contractCount - 1]
  ]

validStep previous command =
  allOf
    [ previous `isSubtypeOf` command
    , withActualFor previous (descendant command [0]) $
        descendant command [1] `isSubtypeOf` root
    ]

Right compiled <- compileTracesOfLength solver length
```

The first guard says that the preceding trace's output state inhabits the next
command's input space. The second substitutes that actual state for the
command's formal `model` and proves its output formula implies the new trace
root. With the top stack type in the low bits, for example, pushing an integer
has output `v = 2 * model + 1`, while `Add` accepts two leading integer tags and
has output relation `model = 2 * v + 1`.

The stack depth is bounded only to keep the state space finite. There is one
liquid schema per operation; candidate step transitions reference those schemas
instead of expanding complete command sequences. The graph grows linearly with
trace length. This is where the LTA is materially clearer than an ECTA: a
bounded ECTA could tabulate every valid state pair, but it cannot state and
reuse the dependent arithmetic transition itself.

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

The typed stack-machine benchmark separates five useful baselines:

- **naive** draws uniformly from all nine raw commands at every position and
  rejects the complete sequence if abstract replay fails;
- **QSM online** follows the normal state-machine-testing shape: choose a
  command admitted by the current model, advance the model, and continue;
- **bespoke** is ordinary compositional QuickCheck code which weights every
  valid next command by its number of complete suffixes;
- **ranked** is the strongest handwritten control: it duplicates the count and
  global-unrank algorithm in application code and constructs `Trace` directly;
- **LTA** compiles the dependent transition schemas with Z3, then samples the
  accepted ranked language without further solver calls.

Naive rejection, bespoke, ranked, and LTA are uniform over the same exact trace
language. QSM online has the same support but intentionally has a different
distribution: choosing uniformly at each prefix gives extra probability to
traces passing through states with fewer valid continuations. That is usually
the right engineering trade in state-machine testing. As in
[quickcheck-state-machine](https://well-typed.com/blog/2019/01/qsm-in-depth/),
the complete trace is generated before execution; after a failure,
`qsmTraceShrinks` removes commands and replays the remainder so dependencies
whose producers disappeared are rejected.

Each successful cell draws 20,000 traces. It runs in a fresh process with a
30-second wall-clock limit and is the median of three runs. The first-sample
column includes all setup—in the LTA row, that means starting Z3, checking the
transition guards, pruning and counting the automaton, and drawing once.
Steady-state sampling is pure. After an engine times out at one length, the
harness skips its larger cells and reports `after timeout`.

The crossover and deep-scaling rows are:

| length | members | engine | first sample | samples/s | alloc/sample | retained after 20k |
| ---: | ---: | --- | ---: | ---: | ---: | ---: |
| 8 | 342,136 | naive | 0.07 ms | 6,216 | 1.23 MB | 35.3 KB |
| 8 | 342,136 | QSM online | 0.02 ms | 181,177 | 42.6 KB | 34.7 KB |
| 8 | 342,136 | bespoke | 0.08 ms | 127,999 | 37.5 KB | 32.91 MB |
| 8 | 342,136 | ranked | 0.06 ms | 407,407 | 11.7 KB | 43.4 KB |
| 8 | 342,136 | LTA | 356.11 ms | 116,904 | 56.1 KB | 176.0 KB |
| 10 | 8,567,224 | naive | 0.22 ms | 1,891 | 3.97 MB | 35.5 KB |
| 10 | 8,567,224 | QSM online | 0.03 ms | 141,073 | 53.6 KB | 34.7 KB |
| 10 | 8,567,224 | bespoke | 0.10 ms | 71,529 | 57.5 KB | 74.04 MB |
| 10 | 8,567,224 | ranked | 0.07 ms | 291,592 | 14.3 KB | 45.3 KB |
| 10 | 8,567,224 | LTA | 417.44 ms | 92,226 | 69.7 KB | 204.0 KB |
| 12 | 215,809,688 | naive | **timeout (30s)** | — | — | — |
| 12 | 215,809,688 | QSM online | 0.03 ms | 117,655 | 64.5 KB | 34.7 KB |
| 12 | 215,809,688 | bespoke | 0.10 ms | 52,819 | 77.4 KB | 118.24 MB |
| 12 | 215,809,688 | ranked | 0.08 ms | 247,927 | 16.0 KB | 47.1 KB |
| 12 | 215,809,688 | LTA | 481.34 ms | 77,779 | 82.6 KB | 231.7 KB |
| 20 | 90,356,263,022,904 | QSM online | 0.04 ms | 67,903 | 108.4 KB | 34.7 KB |
| 20 | 90,356,263,022,904 | bespoke | 0.15 ms | 24,013 | 157.6 KB | 303.87 MB |
| 20 | 90,356,263,022,904 | ranked | 0.13 ms | 138,917 | 25.1 KB | 54.6 KB |
| 20 | 90,356,263,022,904 | LTA | 738.57 ms | 47,230 | 139.1 KB | 349.4 KB |
| 40 | 11,207,052,560,775,737,667,197,734,440 | QSM online | 0.05 ms | 34,504 | 218.0 KB | 34.7 KB |
| 40 | 11,207,052,560,775,737,667,197,734,440 | bespoke | 0.32 ms | 8,663 | 365.0 KB | 778.94 MB |
| 40 | 11,207,052,560,775,737,667,197,734,440 | ranked | 0.22 ms | 58,076 | 50.7 KB | 78.4 KB |
| 40 | 11,207,052,560,775,737,667,197,734,440 | LTA | 1,400.42 ms | 21,706 | 298.8 KB | 629.7 KB |

The ordinary bespoke generator wins at short lengths, but LTA overtakes it at
length nine. At length 40 the LTA produces 21,706 traces/s versus 8,663/s:
2.5x the throughput, while retaining about 630 KB rather than 779 MB after the
fixed workload. This is the clear amortisation win: the generic compiler pays
1.4 seconds once, then reuses its pruned count table instead of rebuilding
weighted QuickCheck choices through every generated suffix.

The ranked row is the necessary ceiling on that claim. A bespoke author who
manually reproduces count-and-unrank reaches 58,076 traces/s and allocates only
50.7 KB per trace, because it constructs `Trace` directly. LTA is buying the
reusable liquid specification and generic compiler, not claiming to outrun a
perfect specialization of its own algorithm. QSM online is the pragmatic
state-machine baseline: it is 1.6x faster than LTA at length 40, but it gives up
uniformity over complete traces and delegates minimisation to failure-time
shrinking.

Naive rejection cracks at length 12 for the 20,000-sample workload. At length
10 it is already 49x slower than LTA and allocates 3.97 MB per accepted trace.

The first benchmark run made repeated solver work visible: length four took
6.50 seconds to compile and length five timed out, despite only 115 distinct
entailment requests among 34,073 requests at length four. Caching exact
obligations for one compile and checking a generated witness directly, rather
than first turning it into a singleton automaton, cut length-four setup to 188
ms and made length five complete in 1.94 seconds.

Replacing the outcome lists with `PlanAp` removes that allocation, but does not
remove the work: the surface compiler still has to visit `11^6 = 1,771,561`
ranks to discover 13,760 valid traces, so length six still exceeds 30 seconds.
That experiment isolates the real requirement from the paper. The flagship
therefore builds an LTA with state-indexed trace layers, runs semantic
transition pruning, and counts the reduced graph before unranking.

At length 40 the pruned LTA represents roughly 1.12e28 traces in about 653 KB of
setup memory. Sampling materializes one liquid term and decodes it to one
`Trace`; it does not retain the language. The remaining 298.8 KB of allocation
per sample is the price of that intermediate annotated term, visible in the
gap to the hand-ranked control.

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
| 1 | 42 | ECTA | 0.05 ms | 2,179,837 | 3.6 KB | 36.9 KB | 37.7 KB |
| 1 | 42 | LTA equality | 4.24 ms | 1,147,908 | 6.5 KB | 61.7 KB | 38.0 KB |
| 2 | 27,054 | ECTA | 0.06 ms | 1,704,884 | 3.8 KB | 47.3 KB | 58.4 KB |
| 2 | 27,054 | LTA equality | 4.59 ms | 483,068 | 14.6 KB | 63.4 KB | 39.8 KB |
| 3 | 8,887,065,932,466 | ECTA | 0.09 ms | 880,243 | 5.8 KB | 61.9 KB | 137.3 KB |
| 3 | 8,887,065,932,466 | LTA equality | 4.66 ms | 170,889 | 41.4 KB | 65.1 KB | 41.5 KB |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | ECTA | 0.14 ms | 319,270 | 12.8 KB | 98.6 KB | 334.3 KB |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | LTA equality | 5.44 ms | 54,354 | 124.2 KB | 66.9 KB | 43.3 KB |

For equality alone, the ECTA is the right tool. Its setup stays below 0.15 ms;
the LTA pays about 4–5.5 ms to start Z3 and prune the guarded graph. The LTA
sampler is 1.9x slower at depth one and 5.9x slower at depth four, with 9.7x
the per-sample allocation at depth four. That allocation is the cost of
constructing an annotated `LiquidTerm` and decoding it to the same Haskell AST.
The language itself remains symbolic: even the roughly 4.95e38-member
depth-four language occupies only about 67 KB of LTA setup memory.

Measured with GHC 9.12.2 and `-O2` on the maintainer's Apple Silicon machine on
2026-09-02. Reproduce either LTA table, or all four repository tables, from the
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
predicate without an explicit encoding for `a`; a typed frontend could supply
that check later.

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

`compiledSupport` returns the LTA containing only accepted witnesses. Its
automaton is a specialization of `Data.Tree.FTA`; `Data.Tree.Gen` and
`Data.Tree.Gen.QuickCheck` provide the shared sampling and shrinking machinery.
Weights influence sampling but do not duplicate replay ranks. Transition
refinements are part of the support alphabet, so replay cannot invent a new
annotation for an existing constructor.

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
