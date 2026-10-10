# microcfta Lean spike

The current design does not satisfy all three requested correctness properties.
This spike provides checked proofs of the core mathematical operations and three
reproduced implementation counterexamples. It is not a proof of the complete
Haskell implementation.

Audited source: `dbc6955a9b1fe9de92acc167301342915916f307`.
Toolchain: Lean 4.34.1. Dependencies: Lean's bundled `Std` and `Lean` libraries.

## Results against the request

| Requirement | Proved | Current implementation finding |
| --- | --- | --- |
| Generate every required term | The executable Lean enumerator contains exactly the accepted terms within its height bound. Every accepted finite term appears at some bound, including for cyclic graphs. | Repeated paths in `Holds` can reject a tautology and empty a generator. Similarity minimization can remove the last accepted term. |
| Correct probabilities | Exact finite distributions, weighted choices, products, conditioning, duplicate-output aggregation, and mass-preserving grouping. Acceptance is equivalent to positive probability at some bound for the Lean uniform-run sampler. | Observing a built atomic child can change its sizes. A size bound then changes output probabilities from `1/2, 1/2` to `1, 0`. |
| Valid optimizations | Synchronous intersection, immediate-child equality sharing, strict-prefix equality rejection, guard splitting, grouping identities, and selected integer-counting identities. | `minimize` and `reduce` can preserve structural productivity while eliminating all guarded solutions. General pruning and counting implementations still have proof obligations. |

See [FINDINGS.md](FINDINGS.md) for the three reproductions, consequences, and
proposed repairs. The Haskell libraries remain at the audited source revision.

## Build and inspect

From this directory:

```sh
lake build
```

`lean-toolchain` pins the installed version. The package needs no external Lean
dependencies. In the restricted WSL environment, the `elan` wrapper failed while
querying its default channel. The installed binary worked:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake build
```

The default target imports every proof module and runs
[`MicroCFTA/Audit.lean`](MicroCFTA/Audit.lean). The audit checks the transitive
axiom dependencies of every theorem in the `MicroCFTA` namespace, including
generated theorems. It permits only `propext`, `Classical.choice`, and
`Quot.sound`. A placeholder proof, a native evaluation axiom, or a project
axiom makes the build fail. A temporary theorem with `sorry` was used to verify
that the audit rejects `sorryAx`. That temporary file is outside this project.

## Proof map

| File | Principal results |
| --- | --- |
| [Language.lean](MicroCFTA/Language.lean) | `mem_enumerate_iff`, `accepts_iff_eventually_enumerated`, `accepts_intersect_iff`, `pathEquality_correct`, `strict_prefix_paths_not_equal`, `equality_sharing_preserves_terms` |
| [Probability.lean](MicroCFTA/Probability.lean) | `split_pair`, `pair_split`, `uniform_tickets_probability`, `frequency_probability`, `eventMass_condition`, `regrouping_preserves_distribution`, `join_group_pair_probability` |
| [Integration.lean](MicroCFTA/Integration.lean) | `samples_probability`, `event_probability`, `accepted_has_rank`, `rank_is_accepted`, `accepts_iff_eventually_positive` |
| [Guards.lean](MicroCFTA/Guards.lean) | `evaluate_supports`, `splitGuard_preserves`, `groupByKey_cover`, `partition_discharge_preserves`, `independent_holds_sound`, `holds_alias_counterexample` |
| [Lattice.lean](MicroCFTA/Lattice.lean) | `signed_correct`, `normalize_divisor`, `project_pair`, `firstMaximum_unique`, `firstMaximum_exists`, `intervalSum_antiderivative` |
| [Counterexamples.lean](MicroCFTA/Counterexamples.lean) | `similarity_guard_counterexample`: the original language is nonempty, the rewritten graph remains structurally productive, and its accepted language is empty at every depth. |

Detailed correspondence and limitations are in
[language notes](notes-language.md), [probability notes](notes-probability.md),
and [guard notes](notes-guards.md).

`Lattice.lean` corresponds to `Refinement/Lattice.hs` as follows:

- `signed_correct` verifies polarity propagation, conjunction products, and
  inclusion-exclusion for Boolean formulas. Lists represent signed-map entries.
- `normalize_divisor` verifies division of a linear inequality by a positive
  common divisor, including floor division of a negative offset.
- `tightest_offset` and `opposite_inconsistent` justify two normalization steps.
- `project_pair` verifies one Fourier-Motzkin projection step.
- `firstMaximum_exists` and `firstMaximum_unique` verify the strict tie rule
  for a selected lower bound. The upper-bound rule follows by negating values.
- `intervalSum_antiderivative` verifies telescoping over intervals that can
  start at negative integers. Its discrete-antiderivative equation is a premise.

These results do not prove the concrete `Map` simplification, feasibility
recursion, complete polyhedral elimination, Bernoulli/Faulhaber construction,
`pointCount`, `pointAt`, or `pointRank` implementations.

## Meaning of the main theorem

`Language.Accepts` is an independent inductive relation on finite trees.
`Language.enumerate` computes bounded Cartesian products and checks each guard
on its complete tree. The main language theorem proves their equivalence.
A Lean leaf has height one; Haskell depth `d` corresponds to Lean fuel `d + 1`.
Finite terms and finite transition lists suffice. The state graph can be cyclic.

The integration theorem normalizes one ticket per enumerated run. A term with
several accepting runs receives the sum of their masses. Thus the theorem
establishes uniformity over runs, not distinct terms. It does not assert that
arbitrary Haskell generators use this distribution. The separate probability
module proves weighted-distribution identities with explicit preconditions.

The SMT solver and concrete refinement evaluator are outside the language
proof. Guards have a supplied Boolean interpretation there. `Guards.lean`
separately states what sound atomic decisions and sufficient observations must
provide. In particular, observation coverage and homogeneity are premises of
the pruning theorems. They are not proved for the Haskell observation trie.

Other remaining boundaries include recursive binder conversion, interning,
union-find enumeration, memoization, recursive size tables, machine-integer
conversions, binary searches, callback contracts, the random backend, and
shrinking. The Lean definitions are handwritten reference algorithms. There is
no verified translation or extraction connecting all Haskell code to them.

## Papers

The term semantics follows the supplied LTA paper's Figure 6 and the ECTA
paper's finite-term denotation. ECTA reduction requires exact language
preservation. LTA similarity minimization deliberately removes terms and needs
a weaker representative-preservation property. The new counterexample
violates even nonemptiness preservation for the public Boolean-guard API.

The supplied LTA appendix's Lemmas 2 and 3 have proof headings without proof
arguments. They are not used as axioms. The proofs here also do not formalize
the paper's source-language typing judgment or assume that arbitrary library
functions satisfy their refinements.

Source PDF SHA-256 values:

```text
lta.pdf  f3a84b08cfce95747dac5148f28a9092115bfe3144880ca13e2258531a1f9463
ecta.pdf 34572866be0bc8e86a546f712ffb2666fe641d133417a895ecbdee5d8f6e1ebf
```

## Validation

- The complete Lean package builds. The axiom audit passes.
- The three Haskell counterexamples run with Z3 inside `nix-shell`.
- Existing suites pass: 257 core, 182 generator, and 127 refinement examples;
  566 total, zero failures. These passing suites do not cover the findings.
- Fourmolu accepts the reproduction. Cabal-gild accepts both audited packages.

The Haskell commands run from the repository root:

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal build lib:microcfta lib:microcfta-generator -j1'
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc lean/repro/Counterexamples.hs'
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal test microcfta:unit-tests microcfta-generator:gen-tests microcfta-generator:refinement-tests -j1 --test-show-details=direct'
```

The host compiler path resolves the existing Nix/GHC `-lgmp` linker failure on
this WSL host. The reproduction is a standalone audit artifact. It does not
add a package test suite.

## Next proof obligations

1. Repair the three findings and add their cases to the existing test suites.
2. State the contextual compatibility required of similarity replacements.
   Type subtyping alone is insufficient for arbitrary Boolean guards.
3. Prove the concrete symbolic counter and recursive size-table recurrences.
4. Prove the observation trie preserves language coverage, guard meaning,
   masses, and size classes.
5. Verify the complete lattice eliminator and rank/select implementation.
6. Establish an implementation correspondence through a translation, extraction,
   or a narrower verified core. Differential tests can support this work but
   cannot replace the correspondence proof.
