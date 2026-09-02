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

## Sampling performance

The typed stack-machine example has three exact-uniform implementations:

- **naive** draws uniformly from all nine raw commands at every position and
  rejects the complete sequence if abstract replay fails;
- **bespoke** tracks `StackState` directly and weights each valid command by
  the exact number of complete suffixes following its output state; and
- **LTA** compiles the dependent transition schemas with Z3, then samples the
  accepted ranked language without further solver calls.

The suffix weights are essential. Merely choosing uniformly among the commands
valid at the current state would bias traces whose later states have fewer
continuations. All three rows instead sample the same uniform language at each
exact length. The `members` column is computed by an independent state-model
recurrence and checked against the compiled LTA cardinality in the specs.

Each successful cell draws 100,000 traces. It runs in a fresh process with a
30-second wall-clock limit and is the median of three runs. The first-sample
column includes all setup—in the LTA row, that means starting Z3, checking the
transition guards, pruning and counting the automaton, and drawing once.
Steady-state sampling is pure. After an engine times out at one length, the
harness skips its larger cells and reports `after timeout`.

| length | members | engine | first sample | samples/s | alloc/sample | setup mem | retained after 100k |
| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 4 | naive | 0.02 ms | 578,272 | 13.6 KB | 32.7 KB | 34.7 KB |
| 1 | 4 | bespoke | 0.02 ms | 2,384,700 | 3.4 KB | 2.0 KB | 35.2 KB |
| 1 | 4 | LTA | 15.02 ms | 735,559 | 10.1 KB | 121.4 KB | 97.8 KB |
| 2 | 22 | naive | 0.02 ms | 274,936 | 28.5 KB | 32.8 KB | 34.8 KB |
| 2 | 22 | bespoke | 0.03 ms | 1,094,499 | 7.2 KB | 36.6 KB | 40.5 KB |
| 2 | 22 | LTA | 170.99 ms | 420,950 | 16.6 KB | 126.0 KB | 102.4 KB |
| 3 | 132 | naive | 0.02 ms | 163,278 | 48.4 KB | 32.9 KB | 34.9 KB |
| 3 | 132 | bespoke | 0.04 ms | 737,724 | 10.5 KB | 38.4 KB | 71.8 KB |
| 3 | 132 | LTA | 192.68 ms | 271,996 | 23.6 KB | 134.4 KB | 110.8 KB |
| 4 | 556 | naive | 0.04 ms | 69,814 | 111.2 KB | 32.9 KB | 35.0 KB |
| 4 | 556 | bespoke | 0.05 ms | 541,023 | 14.3 KB | 40.3 KB | 207.2 KB |
| 4 | 556 | LTA | 231.26 ms | 205,382 | 30.0 KB | 144.7 KB | 121.1 KB |

Lengths five through ten expose both scaling boundaries:

| length | members | engine | first sample | samples/s | alloc/sample | setup mem | retained after 100k |
| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 5 | 3,104 | naive | 0.05 ms | 41,911 | 185.3 KB | 33.0 KB | 35.1 KB |
| 5 | 3,104 | bespoke | 0.06 ms | 419,192 | 17.3 KB | 42.6 KB | 944.4 KB |
| 5 | 3,104 | LTA | 251.57 ms | 169,950 | 36.2 KB | 154.2 KB | 130.5 KB |
| 6 | 13,760 | naive | 0.07 ms | 20,300 | 383.2 KB | 33.1 KB | 35.2 KB |
| 6 | 13,760 | bespoke | 0.06 ms | 329,427 | 21.4 KB | 44.0 KB | 4.18 MB |
| 6 | 13,760 | LTA | 291.36 ms | 145,107 | 42.5 KB | 164.1 KB | 140.5 KB |
| 7 | 73,528 | naive | 0.07 ms | 12,002 | 651.9 KB | 33.2 KB | 35.2 KB |
| 7 | 73,528 | bespoke | 0.07 ms | 251,143 | 25.6 KB | 47.3 KB | 20.26 MB |
| 7 | 73,528 | LTA | 311.73 ms | 124,512 | 49.4 KB | 176.5 KB | 152.8 KB |
| 8 | 342,136 | naive | 0.08 ms | 6,107 | 1.24 MB | 33.3 KB | 35.3 KB |
| 8 | 342,136 | bespoke | 0.08 ms | 166,756 | 32.1 KB | 47.6 KB | 72.82 MB |
| 8 | 342,136 | LTA | 352.95 ms | 108,619 | 55.7 KB | 191.4 KB | 167.8 KB |
| 9 | 1,783,112 | naive | 0.08 ms | 3,566 | 2.14 MB | 33.4 KB | 35.4 KB |
| 9 | 1,783,112 | bespoke | 0.09 ms | 116,389 | 41.2 KB | 52.2 KB | 166.76 MB |
| 9 | 1,783,112 | LTA | 372.90 ms | 98,781 | 62.0 KB | 204.0 KB | 180.4 KB |
| 10 | 8,567,224 | naive | **timeout (30s)** | — | — | — | — |
| 10 | 8,567,224 | bespoke | 0.09 ms | 81,168 | 51.1 KB | 54.3 KB | 265.52 MB |
| 10 | 8,567,224 | LTA | 414.58 ms | 89,463 | 69.2 KB | 216.5 KB | 192.9 KB |

Naive rejection therefore cracks at length ten for this fixed workload. Length
nine only just completes: 3,566 traces/s means one 100,000-sample cell takes
about 28.0 seconds, is 33x slower than bespoke generation, and allocates 2.14
MB per accepted trace. At length ten only about 0.25% of the raw command
sequences are valid, so the next cell crosses the 30-second boundary.

The first benchmark run made repeated solver work visible: length four took
6.50 seconds to compile and length five timed out, despite only 115 distinct
entailment requests among 34,073 requests at length four. Caching exact
obligations for one compile and checking a generated witness directly, rather
than first turning it into a singleton automaton, cuts length-four setup to 188
ms and makes length five complete in 1.94 seconds.

Replacing the outcome lists with `PlanAp` removes that allocation, but does not
remove the work: the surface compiler still has to visit `11^6 = 1,771,561`
ranks to discover 13,760 valid traces, so length six still exceeds 30 seconds.
That experiment isolates the real requirement from the paper. The current
flagship therefore builds an LTA with state-indexed trace layers, runs semantic
transition pruning, and counts the reduced graph before unranking.

The result reaches length ten in 415 ms of setup while representing 8,567,224
traces in about 217 KB. Sampling materializes one liquid term and decodes it to
one `Trace`; it does not retain the language. At length ten this path produces
89,463 traces/s, about 10% faster than the handwritten exact-uniform generator
on this workload, while naive rejection has already timed out. The remaining
per-sample allocation—69.2 KB versus 51.1 KB bespoke—is the cost of constructing
the selected `LiquidTerm` before decoding the Haskell trace, not of expanding
the other 8.5 million members.

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
| 1 | 42 | ECTA | 0.11 ms | 1,946,283 | 3.7 KB | 40.6 KB | 37.3 KB |
| 1 | 42 | LTA equality | 4.34 ms | 989,511 | 6.3 KB | 61.5 KB | 37.9 KB |
| 2 | 27,054 | ECTA | 0.15 ms | 1,535,037 | 4.2 KB | 52.0 KB | 55.0 KB |
| 2 | 27,054 | LTA equality | 4.85 ms | 425,559 | 13.8 KB | 63.1 KB | 39.5 KB |
| 3 | 8,887,065,932,466 | ECTA | 0.20 ms | 742,087 | 7.1 KB | 68.4 KB | 130.3 KB |
| 3 | 8,887,065,932,466 | LTA equality | 5.11 ms | 147,449 | 38.9 KB | 64.6 KB | 41.0 KB |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | ECTA | 0.44 ms | 264,967 | 16.9 KB | 108.2 KB | 299.6 KB |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | LTA equality | 7.19 ms | 47,897 | 116.2 KB | 66.1 KB | 42.5 KB |

For equality alone, the ECTA is the right tool. Its setup stays below half a
millisecond; the LTA pays about 4–7 ms to start Z3 and prune the guarded graph.
The LTA sampler is 2.0x slower at depth one and 5.5x slower at depth four, with
6.9x the per-sample allocation at depth four. That allocation is the cost of
constructing an annotated `LiquidTerm` and decoding it to the same Haskell AST.
The language itself remains symbolic: even the roughly 4.95e38-member
depth-four language occupies only about 66 KB of LTA setup memory.

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
