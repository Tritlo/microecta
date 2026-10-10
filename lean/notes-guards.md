# Guard and reduction audit

`MicroCFTA/Guards.lean` uses Lean 4.34.1 and `Std`. It has no `sorry`,
`admit`, custom axiom, or `native_decide`. The module states its external
obligations as theorem parameters.

## Source map

| Haskell source | Lean result | Boundary |
| --- | --- | --- |
| `microcfta/src/Data/CFTA/Refinement/Verdict.hs`: `negateVerdict`, `andVerdict`, `orVerdict` | Verdict algebra and `conjunction_supports`, `disjunction_supports` | Pure operations; IO and evaluation order are not modeled. |
| `microcfta/src/Data/CFTA/Refinement/Evaluate.hs`: `evaluateWith` | `evaluate_supports`, `evaluate_ext`, `evaluate_double_negation` | Boolean guard structure; each atomic decision is a parameter. Binary connectives model the list folds. No SMT solver, substitution resolver, or path lookup is certified. |
| `microcfta/src/Data/CFTA/Constraint.hs`: `splitGuard` | `splitGuard_preserves` | The split retains neutral `Top` nodes. Haskell removes those nodes. The verdict identity laws prove that removal safe. |
| `microcfta/src/Data/CFTA/Refinement/Prune.hs`: `groupVariants`, `specializeNode`, `pruneSemantic` | `groupByKey_cover`, `groupByKey_disjoint`, `grouping_homogeneous`, `partition_discharge_preserves`, `partition_cover_preserves` | Exact finite key partition is verified. The Haskell observation trie must cover the original language and provide sufficient keys. This module does not prove that implementation correspondence. |
| `microcfta/src/Data/CFTA/Refinement/Evaluate.hs`: `substituteTerm` and `Same` | `substitution_preserves_equality`, `substitution_reflects_equality` | Equality survives any uniform map. Disequality requires an injective map. General symbol substitution is not injective. Capture avoidance in Liquid Fixpoint is not formalized. |
| `microcfta/src/Data/CFTA/Refinement/Evaluate.hs`: `Holds` | `independent_holds_sound`, `holds_alias_counterexample`, `aliased_formals_restore_completeness` | Two occurrences of one path must denote one value. The current evaluator instead declares one fresh formal per occurrence. |
| `microcfta/src/Data/CFTA/Refinement/Minimize.hs`: representative substitution | `representative_preservation_is_not_language_equality`, `representative_replacement_can_destroy_all_guarded_terms` | Type-based representative selection is not exact language preservation. Negative equality can also prevent preservation of any accepted term. |

`discharge_preserves` permits `Unknown` only when the original guard remains.
The Haskell pruner also returns an error for some unknown decisions. An error
is not an accepted reduced automaton. The theorem does not assert termination
of recursive pruning or correctness of its memo tables.

## Repeated paths in Holds

The complete evaluator constructs formals from `[0 .. length targets - 1]`.
It assumes the selected refinement for each formal. It adds no equalities for
repeated paths. For

```haskell
Holds [path [0], path [0]]
  (variable (contractTermName 0) .== variable (contractTermName 1))
```

and a child with refinement `true`, its query is `true => x0 == x1`.
The intended query has one value and is reflexive. Independent formals reject
this valid contract. The Lean counterexample uses a two-value domain, so the
failure does not depend on an SMT implementation. The general theorem
`independent_holds_sound` also proves that independent formals are conservative
for positive proofs. This defect loses completeness; it does not establish
unsound positive contract acceptance.

The relational integer compiler uses a different translation:
`Refinement/Internal/Compile.hs`, `Holds targets formula`, substitutes every
formal with `targetTerm` at its target. Repeated targets produce the same
expression. The shared Haskell reproduction confirms that complete evaluation returns
`No` and compilation returns `Left EmptyGenerator` for the repeated-path
tautology. A comparison with the integer-pool route remains separate.

## Formula refutation is not Boolean complement

`Not (Satisfies p formula)` checks that the refinement at `p` implies the
negated formula. `Not (Holds paths formula)` uses the same rule. These semantics
are explicit in the current API documentation.

A broad refinement can prove neither a formula nor its negation.
`refutation_is_stronger_than_failure` proves this over `Bool`. An inconsistent
refinement proves both, as `empty_refinement_proves_both` shows. Thus excluded
middle and noncontradiction cannot be used as simplifications of these atoms.
The Lean guard semantics takes separate positive and negative atomic meanings.
It does not assume that they are complements.

`Same` and `Entails` retain Boolean complement semantics. They are the atoms
in the supplied LTA paper. The extra `Satisfies` and `Holds` operations therefore
need their stated extension semantics when relating implementation and paper.
This difference alone is not an implementation error.

## Minimization requires compatibility with guards

The executed counterexample uses a root transition
`f[A, B]`, with `A = {a}` and `B = {b}`, guarded by
`Not (Same [0] [1])`. Give both leaves the same refinement type. A subtype
relation may then choose `a` to replace `b`.

The original accepted term is `f(a,b)`. Removing `b` empties `B`. Redirecting
its parent to `A` adds `f[A,A]`, whose only term fails the negative equality.
Both children remain structurally productive. The current productivity checks
ignore guard acceptance. Semantic pruning retains the negative equality as a
residual, so preceding minimization with pruning does not establish the missing
compatibility condition.

`MicroCFTA/Counterexamples.lean` imports the finite-run automaton semantics.
It proves that the original automaton accepts `f(a,b)`, that the reduced
automaton accepts no finite term at any depth, and that its root remains
structurally productive. The final theorem is
`similarity_guard_counterexample`.

The shared Haskell reproduction in `repro/Counterexamples.hs` confirms the
implementation result with the standard `refinementSubtypingOn` adapter:
original denotation contains `f(a,b)`; both `minimize` and `reduce` return a
successful result with an empty denotation. The live reproduction connects the
Haskell rewrite to the before and after automata. The Lean proof certifies
their semantic difference. No full translation of the minimizer is claimed.

## Paper obligations

The supplied ECTA paper, Definition 3.18 and Theorem 3.20, claims exact denotation
preservation for static equality reduction. Its language-preservation obligation
fits the partition proofs here.

The supplied LTA paper, Section 4.2, removes similar terms and retains subtype
representatives. Exact term-language equality is not its objective. Appendix
Lemma 5 instead asserts that suitable representatives remain. This claim needs
compatibility with all enclosing constraints. An arbitrary public `Subtyping`
callback and arbitrary Boolean guards do not provide that property.

Appendix Lemmas 2 and 3 each contain a `Proof.` heading without an argument in
the supplied PDF text. This spike supplies explicit local proof obligations; it
does not use those paper claims as axioms.

## Historical checks

The historical loss of outcome weights in `groupBuilt` is repaired in the current
source: it reads `outcomeMass`, computes a common denominator, and uses the
scaled weights. Reconstructed atomic size remains a separate obligation.

Reflexive `Same p p` is excluded from the positive equality cache, so its path
existence condition remains a residual. A proof or implementation that replaces
it by `Top` without proving path existence would be invalid.
