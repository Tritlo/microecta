# microlta-generator

The LTA adapter uses `microfta-generator` for shared ranked generation and
`microecta-generator` for grouped equality joins. `microfta` supplies the
ordinary transition graph, and `microlta` supplies liquid semantics. Neither
FTA package depends on this adapter or on a solver.

Describe candidate values and their refinements. Add a guard with named child
arguments. Call `compile` once, then use pure sampling, replay, and shrinking.
The compiler retains symbolic counts and constructs selected values on demand.
Unsupported guards return an error.

## A complete first program

This program generates safe divisions. It rejects the zero denominator before
it evaluates the division.

```haskell
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}

import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.Guard (requires)
import Data.LTA.LiquidFixpoint (integerDeclarations, withZ3)
import Data.LTA.Refinement (integer, value, (./=.), (.==.))
import qualified Test.QuickCheck as QC

main :: IO ()
main = withZ3 (integerDeclarations ["v"]) $ \solver -> do
  let nonZero = value ./=. integer 0
      denominators = LTA.pool
        [ LTA.refined (0 :: Integer) "zero" (value .==. integer 0)
        , LTA.refined 1 "one" (value .==. integer 1)
        , LTA.refined 2 "two" (value .==. integer 2)
        ]
      divisions =
        LTA.node "divide" (\denominator -> denominator `requires` nonZero) $ LTA.do
          denominator <- denominators
          LTA.pure (denominator, 12 `div` denominator)
  compiled <- LTA.compile solver divisions >>= either (fail . LTA.explain) pure
  QC.quickCheck $ LTA.forAll compiled $ \(denominator, quotient) ->
    denominator /= 0 && quotient == 12 `div` denominator
  print $ fmap LTA.generatedValue $ LTA.unrank compiled 0
```

Use the packages `base`, `microlta`, `microlta-generator`, and `QuickCheck`.
Install Z3 and put it on `PATH`. The public refinement helpers do not require a
Liquid Fixpoint import. `value` is the conventional refinement variable `v`;
`variable "input"` names another expression. Declare each variable's sort before
compilation. `integerDeclarations` declares integer variables, and
`withZ3Assuming` adds ambient facts when a contract depends on external inputs.
The lower-level solver API accepts other sorts and custom entailment callbacks.

The caller must ensure that each refinement describes its Haskell value.
The compiler proves implications between these annotations. It does not inspect
an arbitrary Haskell value to prove its annotation. Mapping a generator changes
its Haskell value and retains the term and refinement that justify its guards.

Run the checked introductory example from the workspace:

```sh
nix-shell --run 'cabal run lta-safe-division'
```

[`SafeDivision.hs`](https://github.com/Tritlo/microecta/blob/main/microlta-generator/examples/SafeDivision.hs) also checks ambient assumptions,
exact replay, and semantic pool shrinking. CI runs it and the automaton example.

## Construction and compilation

`fromDatatypeUpToDepth` accepts a derived
`TypedFTA (Refinement, LiquidConstraint) a`. Use `annotateDatatype` to supply
the refinement and constraint for each constructor. The datatype supplies its
fields and recursive structure. The existing LTA compiler supplies accepted
terms, exact replay, and valid shrinking; the retained codec supplies `a`.
The caller must still justify the refinements assigned to each constructor.

The natural-number example in `examples/AutomatonInterop.hs` derives its
recursive grammar, annotates zero and successor, and uses the generated
datatype in safe divisions. For handwritten graphs, `Data.LTA.annotateFTA`
adds liquid labels and constraints without repeating states or child lists.

Finite counting, structural ambiguity checks, direct value decoding, depth
bounds, and ordinary automaton shrinking use the shared FTA implementation.
Liquid guard evaluation, refinement grouping, and Boolean equality
interpretation remain in this package.

Each qualified do-block describes independent direct children. Its adjacent
`node` supplies the constructor and guard. Guard arguments have the same order
as the child generators. A named guard must take exactly one argument per
child; write `_` for an unused child. An argument-count mismatch is a construction
error, including when the source is empty. Raw `LiquidConstraint` values remain
available and retain the paper's Boolean meaning for missing paths.

`node` uses the universal result refinement. `refinedNode` supplies a fixed
result refinement. `refinedNodeByRoots` computes one from child labels and
refinements with a single function. `refinedNodeBy` computes one from the
Haskell result. Only the explicit `validOutcomes` diagnostic accepts that
value callback; compilation rejects it.
Dependent child choices do not belong in the applicative block. Express their
relationship in the guard, for example `actual `isSubtypeOf` expected`,
`argument `requires` nonZero`, or
`withActualFor actual formal dependentResultCheck`.
`descendant argument [1]` selects the argument's second child.

`isSameTermAs` normally requires exact subtree equality. Inside `withActualFor`,
it compares views with the formal symbol replaced by the actual symbol,
including free variables in refinement annotations. The generated terms and
values stay unchanged. Several replacements in `withActualsFor` apply
simultaneously. Compilation can decide this scoped equality on observed leaves.
Scoped equality on compound subtrees remains unsupported by the compiler.

`compile` retains original source order and source weights. It groups candidates
by the observations a guard needs, then indexes the accepted source ranks.
This can represent a language larger than a machine integer without traversing
its members. Bounded automata use symbolic counts for nested equality,
negation, disjunction, and overlapping alternatives. Each distinct accepted
term has one rank, and unranking constructs only the selected term.

Compilation has no cardinality limit and no enumerating fallback. Its cost can
still grow with the number of distinct observation groups or equality contexts.
Value-computed refinements and unresolved guards return errors. For example,
substitution guards that need the identity of compound actual terms remain
unsupported. `explain` describes each error. An undecidable acceptance guard is
an error. An undecidable optional shrink implication omits the unproved edge.

Repeated pool entries retain separate ranks and sampling weight. `frequency`
multiplies each branch's occurrence weights; it does not assign equal probability
to branches of different sizes. Mapping two members to the same value does not
merge their ranks. Replay is deterministic for a fixed language and source
order. A changed pool, bound, or specification can change the ranks.

Pool shrinks weaken a refinement. Equivalent refinements move toward earlier
pool entries. Composite sources keep these semantic shrinks and search through
rejected intermediate candidates to return accepted targets. Imported automata
use structural shrinks that strictly reduce tree node count. All returned
shrinks stay in the compiled language. Sampling, replay, and shrinking make no
solver calls.

## Import an LTA

`fromLTA` is the escape hatch for an existing automaton. It takes an explicit
maximum tree height; leaves have height zero. It preserves the shared graph
until compilation and composes with ordinary sources:

```haskell
boundedTerms = LTA.fromLTA 6 automaton

wrapped = LTA.node "wrap" (\child -> child `requires` desiredRefinement) $ LTA.do
  term <- boundedTerms
  LTA.pure (decode term)

compiled <- LTA.compile solver wrapped >>= either (fail . LTA.explain) pure
```

Each distinct accepted annotated term has one rank, even when several runs
accept it. Equal Haskell values obtained from different terms remain distinct.
An empty or negative-bound import is an empty source and can occur beside a
nonempty alternative. Recursive automata are bounded before counting. Ambiguous
runs count each accepted term once. Boolean subtree equality uses symbolic
intersections and complements after semantic pruning. Residual semantic or
scoped compound-equality guards return an error.

[`AutomatonInterop.hs`](https://github.com/Tritlo/microecta/blob/main/microlta-generator/examples/AutomatonInterop.hs) constructs a recursive
automaton with `Data.LTA.Syntax`, imports it, and composes it with a refined pool:

```sh
nix-shell --run 'cabal run lta-automaton-interop'
```

`support` explicitly enumerates an ordinary source. An unresolved `fromLTA`
source instead returns `SourceRequiresCompilation`; inspect `compiledSupport`
after compilation. `validOutcomes` explicitly enumerates checked candidates and
has no materialization limit. These observers are for small diagnostic inputs.

## Advanced compilation APIs

`compileRelational` exposes native grouped ECTA order and structural shrinking.
It accepts unit-weight alternatives and reports guards that its observations
cannot decide. Its ranks and shrink policy differ from the default compiler's
source order and semantic shrinking.

`compileAutomaton` handles finite automata. `compileAutomatonUpToDepth` first
bounds recursive automata. Both retain symbolic counts for Boolean subtree
equality after semantic pruning. Their `With` variants fold each selected
transition directly into a domain value and leave the term witness lazy.
Use `compile` with `fromLTA` for a bounded source that composes with other sources.

The authoritative representation remains an LTA. Pruning returns an LTA;
`pruneToECTA` is an optional lowering for positive conjunctive equality. Negated
or disjunctive equality stays in the LTA and uses the symbolic counter. Core
`denotationAtMost` remains an explicit bounded reference evaluator.

## Frozen native pools

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
Independent pool sizes multiply: the example describes 32 x 8 candidate pairs.
The default compiler groups the observations needed by the guard. Use smaller
pools when every candidate has a distinct observation.

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
[`OpaquePoolSpec`](https://github.com/Tritlo/microecta/blob/main/microlta-generator/test/Data/LTA/OpaquePoolSpec.hs) compares this with the
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

The default compiler checks these contracts through grouped observations where
possible. It uses complete candidates when the contract needs them. Both paths
return a pure language with the same source ranks and semantic shrink policy.

## Flagship: typed state-machine traces

[`Data.LTA.StateMachineTraceLanguage`](https://github.com/Tritlo/microecta/blob/main/microlta-generator/common/Data/LTA/StateMachineTraceLanguage.hs)
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

Right compiled <- LTA.compile solver (tracesOfLength length)
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
[`Data.LTA.SizedVectorLanguage`](https://github.com/Tritlo/microecta/blob/main/microlta-generator/common/Data/LTA/SizedVectorLanguage.hs): a
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
  LTA.refinedNodeByRoots "take" resultRefinement validTake $ LTA.do
    result    <- possibleLengths maximumLength
    _function <- takeFunction
    count     <- possibleLengths maximumLength
    input     <- children
    LTA.pure $ SizedVector
      (Take (numberValue count) $ vectorExpression input)
      (numberRefinement result)

resultRefinement ((_, refinement) : _) = refinement
resultRefinement [] = true

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

The recorded measurements in this section and the equality-theory comparison
below predate the standard-tree migration. They used the earlier `LiquidTerm`
representation. Run the benchmark commands below to measure the current code.

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
  `Tree LiquidSymbol`, then decodes it to `Trace`;
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
throughput improvement over materializing and immediately traversing the
earlier `LiquidTerm`. The remaining gap is in generic automaton unranking. Conversely,
LTA do's retained relational index uses 6.15 MB of setup memory versus about
653 KB for the direct automaton; reducing that compact-index constant and using
a persistent worklist in automaton pruning are the next focused opportunities.

## Equality theory cost: ECTA versus LTA

The typed-expression flagship also has a deliberately equivalent liquid
encoding in
[`Data.LTA.EqualityTypedExpressionLanguage`](https://github.com/Tritlo/microecta/blob/main/microlta-generator/common/Data/LTA/EqualityTypedExpressionLanguage.hs).
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

[`Data.LTA.SafeBufferLanguage`](https://github.com/Tritlo/microecta/blob/main/microlta-generator/common/Data/LTA/SafeBufferLanguage.hs) gives
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
`refinedNodeByRoots` to retain the proven result refinement. A later `head` node can
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

For a two-entry pool ordered as `[nonNegative, exactOne]` and a pair guard
``left `isSubtypeOf` right``, the raw product is:

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
grouped surface compiler. `Data.Ranked` and `Data.Ranked.QuickCheck` provide
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
states. QuickCheck needs a finite language, so compile with an explicit
tree-height bound:

```haskell
Right compiled <- LTA.compileAutomatonUpToDepth solver 6 recursiveLTA
```

Depth zero keeps nullary transitions. Every parent-to-child edge consumes one
unit, including edges outside a cycle. A negative bound or empty language
returns `EmptyGenerator`. Ranks remain deterministic inside the bounded
language.

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
