# Formalization findings

Source revision: `dbc6955a9b1fe9de92acc167301342915916f307`.
All three findings reproduce against this revision with the public APIs.
Run [repro/Counterexamples.hs](repro/Counterexamples.hs) from the repository root:

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc lean/repro/Counterexamples.hs'
```

## 1. Similarity reduction can remove every accepted term

Source: [Refinement/Minimize.hs](../microcfta/src/Data/CFTA/Refinement/Minimize.hs),
`applyStep`, `finiteTransition`, `losesFinal`, and `productiveStates`
(lines 242–271 and 313–321).

Use leaf states `A = {a}` and `B = {b}`, with equal refinements and the same
type class. The standard `refinementSubtypingOn` adapter recognizes the leaf
types as equivalent. The root transition is `f[A,B]` with guard
`Not (Same [0] [1])`.

The original language is `{f(a,b)}`. The minimizer selects `a` as the
representative of `b`, removes `b`, and copies the parent as `f[A,A]`.
Its only structural term is `f(a,a)`, which fails the guard.

Observed results:

```text
denotationAtMost original       = Right [f(a,b)]
denotationAtMost after minimize = Right []
denotationAtMost after reduce   = Right []
```

The reproduction prints the terms using `Data.Tree`'s `Show` instance.
The notation above abbreviates those trees. This is a completeness failure.
It is stronger than the expected loss of exact terms during minimization:
there is no representative solution left. Pruning before minimization does
not prevent it. The productivity check only inspects child-state reachability;
it does not check whether a finite run satisfies its guards.

[`similarity_guard_counterexample`](MicroCFTA/Counterexamples.lean) proves the
semantic failure for explicit before and after automata. The proof covers all
finite terms, not only the depth used by the Haskell reproduction. The Haskell
reproduction establishes that the implementation performs the problematic
rewrite. A full Lean translation of the minimizer is not claimed.

Proposed repair: require representative replacement to preserve each affected
context's guards, or conservatively skip rewrites when this cannot be shown.
A stronger root-nonemptiness check would detect this example but would not
alone preserve every required query or type class. Type subtyping is not a
congruence for syntactic disequality.

## 2. Repeated Holds paths are treated as independent values

Source: [Refinement/Evaluate.hs](../microcfta/src/Data/CFTA/Refinement/Evaluate.hs),
`evaluateWith (Holds targets formula)` (lines 194–207).

The evaluator creates a new solver formal for every argument occurrence.
It adds each selected refinement as an assumption. It does not add alias
equalities when two arguments refer to the same path.

The reproduction uses:

```haskell
Holds [path [0], path [0]]
  (variable (contractTermName 0) .== variable (contractTermName 1))
```

The child refinement is `v >= 0`. Both arguments denote the same child, so the
contract is reflexive. The evaluator instead asks whether two independent
nonnegative values must be equal.

```text
evaluateConstraint = No
compileWith >>= cardinality = Left EmptyGenerator
```

Expected: `Yes` and `Right 1`. This is a completeness failure, not evidence
that positive `Holds` proofs accept invalid contracts. The general Lean theorem
`independent_holds_sound` proves the conservative direction.
`holds_alias_counterexample` proves that the reverse direction fails.

Proposed repair: use one value per distinct path, or retain the indexed formals
and add equalities for repeated paths. Keep the substitution and binder scope
consistent. The relational integer compiler substitutes target expressions
directly; the complete evaluator must agree with that path identity.

## 3. Observing a built atomic child changes its size semantics

Source:
[Refinement/Internal/Compile.hs](../microcfta-generator/src/Data/CFTA/Gen/Refinement/Internal/Compile.hs),
`groupBuilt` (lines 366–394).

Use an atomic equal choice between leaf `a` with value `0` and tree `wrap(b)`
with value `1`. Both choices have atomic size one. Wrap the source in an
`outer` node. Compare no guard with the tautological observation
`requires (argument 0) (const true)`.

```text
source sizes                      [Just 1, Just 1]
parent without observation        [Just 1, Just 1]
parent with observation           [Just 1, Just 2]
values upToSize 1, without         Right [0,1]
values upToSize 1, with            Right [0]
pmf upToSize 1, without            Right [(0,1 % 2),(1,1 % 2)]
pmf upToSize 1, with               Right [(0,1 % 1)]
```

The observation also creates a shrink from the second rank to the first.
Under size bound one, the second value's probability changes from `1/2` to
zero. This affects term coverage, bounded probabilities, and shrinking.

The earlier loss of unbounded outcome weights is repaired: `groupBuilt` now
reads `outcomeMass` and reconstructs scaled frequencies. The remaining defect
comes from rebuilding each term with `node` and `withChildren`. These operations
recover structural sizes instead of the original atomic boundary.

The probability module proves both exact conditional masses in
`atomic_size_bound_preserves_distribution` and
`reconstructed_size_bound_changes_distribution`. The Haskell reproduction
also prints the exact `pmf` before and after the observation.

Proposed repair: retain the original member size metadata and atomic boundary
when partitioning built generators. Apply atomic reconstruction only to atomic
sources; making every rebuilt member atomic would corrupt non-atomic sizes.
Check size classes and bounded sampling as well as the unbounded masses.

## Interpretation limits

The findings prevent certification of the whole design. They do not invalidate
the checked finite-tree semantics or the probability identities.

`Not (Satisfies ...)` and `Not (Holds ...)` use formula refutation, which is
stronger than failure of entailment. This is an explicit API extension. It is
not classified as a defect. Guard proofs must not assume that these negative
atoms are the classical complements of their positive forms.

No production fixes are included. The proof package and reproductions record
the current behavior so each repair can be reviewed against a precise claim.
