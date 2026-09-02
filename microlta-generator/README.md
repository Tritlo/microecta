# microlta-generator

`microlta-generator` is the Liquid Tree Automata adapter for the ranked engine
in `microecta-generator`. Building the language is pure. `compile` is the one
imperative boundary: it asks Liquid Fixpoint/Z3 which guarded witnesses are
valid and which pool refinements imply one another, then returns a pure
`Compiled` value.

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

The compiler checks every frozen candidate once, removes those whose complete
guard is false, and returns a pure language. This is semantic pruning at the
finite QuickCheck boundary: invalid values never reach a property.

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
values stay ordinary. The LTA stores the input state as each command root's
refinement and its dependent output state as a child refinement. A trace node's
result refinement is its final stack type:

```haskell
extendTrace previousTraces =
  LTA.refinedNodeBy "step" (stateRefinement . traceFinalState) validStep $ LTA.do
    previous <- previousTraces
    command  <- commandContracts
    LTA.pure (predictStep previous command)

validStep previous command =
  allOf
    [ previous `isSubtypeOf` command
    , withActualFor previous (descendant command [0]) $
        descendant command [1] `isSubtypeOf` root
    ]
```

The first guard says that the preceding trace's output state inhabits the next
command's input space. The second substitutes that actual state for the
command's formal `model` and proves its output formula implies the new trace
root. With the top stack type in the low bits, for example, pushing an integer
has output `v = 2 * model + 1`, while `Add` accepts two leading integer tags and
has output relation `model = 2 * v + 1`.

The stack depth is bounded only to make the QuickCheck language finite. There
is one symbolic schema per operation, not one transition per concrete
input/output pair. This is where the LTA is materially clearer than an ECTA: a
bounded ECTA could tabulate every stack shape, but it cannot state and reuse the
dependent arithmetic transition itself.

Following the
[quickcheck-state-machine workflow](https://well-typed.com/blog/2019/01/qsm-in-depth/),
the whole trace is generated before execution. Every retained event predicts
its before-state, response space, and after-state. The specs enumerate all 132
accepted traces of length three, replay every one through an independent
abstract model and a separate concrete integer/Boolean interpreter, and verify
that shrinking never violates a later command's stack precondition. The final
QuickCheck property therefore has no implication or `suchThat` filter.

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
guards and shrink implications, compiling the accepted language, and drawing
once. Steady-state sampling is pure.

| length | members | engine | first sample | samples/s | alloc/sample | setup mem | retained after 100k |
| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 4 | naive | 0.02 ms | 585,840 | 13.6 KB | 32.7 KB | 34.7 KB |
| 1 | 4 | bespoke | 0.01 ms | 2,391,143 | 3.4 KB | 2.0 KB | 35.2 KB |
| 1 | 4 | LTA | 7.10 ms | 2,334,540 | 3.4 KB | 62.8 KB | 39.1 KB |
| 2 | 22 | naive | 0.02 ms | 278,497 | 28.5 KB | 32.8 KB | 34.8 KB |
| 2 | 22 | bespoke | 0.02 ms | 1,049,307 | 7.2 KB | 34.1 KB | 40.5 KB |
| 2 | 22 | LTA | 48.58 ms | 1,955,187 | 3.7 KB | 75.7 KB | 51.3 KB |
| 3 | 132 | naive | 0.02 ms | 160,202 | 48.4 KB | 32.9 KB | 34.9 KB |
| 3 | 132 | bespoke | 0.03 ms | 738,585 | 10.5 KB | 34.9 KB | 71.8 KB |
| 3 | 132 | LTA | 563.00 ms | 1,305,960 | 4.1 KB | 133.7 KB | 106.7 KB |
| 4 | 556 | naive | 0.04 ms | 69,257 | 111.2 KB | 32.9 KB | 35.0 KB |
| 4 | 556 | bespoke | 0.05 ms | 527,348 | 14.3 KB | 35.9 KB | 207.2 KB |
| 4 | 556 | LTA | 6,584.83 ms | 697,355 | 4.0 KB | 354.4 KB | 325.5 KB |

The trade-off is clean. LTA setup grows from 7 ms to 6.6 seconds over these
four lengths because solver work is front-loaded, but it remains below the
30-second boundary. Once compiled, the length-four LTA is about 10x faster
than whole-sequence rejection and 1.3x faster than the bespoke generator,
while allocating about 28x and 3.6x less per sample respectively. Whether that
setup amortizes is therefore visible rather than hidden.

Measured with GHC 9.12.2 and `-O2` on the maintainer's Apple Silicon machine on
2026-09-02. Reproduce this table, or all three FTA/ECTA/LTA tables, from the
repository root with:

```sh
cabal bench microlta-generator:state-machine-trace-speed --enable-optimization=2
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

Similarity minimisation is separate and opt-in because dropping a syntactically
different value is often the wrong trade-off for testing. Declare the
similarity class when semantic representatives are what you want:

```haskell
Right representatives <-
  LTA.minimizePoolBy solver operationKind candidates
```

Within each class, a strict subtype replaces its supertype, equivalent entries
keep the earlier rank, and incomparable entries remain. This mirrors the LTA
paper's minimisation rule without silently reducing ordinary QuickCheck
coverage.

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
