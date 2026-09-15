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
