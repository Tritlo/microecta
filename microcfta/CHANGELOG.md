# Changelog

## 0.1.0.0 - Unreleased

Initial release. `microcfta` consolidates an ordinary tree automaton engine,
equality-constrained tree automata, and liquid tree automata into one package
with one representation. The equality layer descends from `microecta`, which
remains a separate ECTA-only package.

- `Data.CFTA` and `Data.CFTA.Interned`: the explicit-state and interned
  automata, parameterized by a constraint theory. Ordinary automata use `()`.
  Recognition, depth bounds, product intersection, union, templates, paths,
  datatype derivation with `HasFTA`, and level-by-level enumeration with
  `terms` and `termsUpToM` live here.
- `Data.CFTA.Equality`: equality-constrained automata as
  `Node symbol EqConstraints`, with reduction, membership, template
  restriction, and enumeration with unification variables. An automaton with
  no equality constraint and no recursion is enumerated by the shared
  enumerator.
- `Data.CFTA.Refinement`: liquid tree automata over Liquid Fixpoint
  refinements, with the paper's Boolean guard language, actual-for-formal
  position substitution, transition-level semantic pruning, similarity,
  minimization, recursive states under the acyclic-guard restriction, a
  bounded reference denotation on the shared enumerator, and the Z3
  entailment in `Data.CFTA.Refinement.LiquidFixpoint`.
- `Data.CFTA.Symbol`: interned text symbols shared by every layer.

### Differences from microecta 0.1.0.0

- The type of an ECTA is `Node symbol EqConstraints`; there is no separate
  ECTA node type. `edgeEcs` is `edgeConstraint`, and the FTA views return
  `FTAViewError`.
- Concrete terms are `Data.Tree.Tree` from `containers`, and partial or
  truncated enumeration uses `PartialSymbol symbol` rather than inventing
  symbols in the caller's alphabet.
- The hash-consing and memo tables are immutable maps updated atomically, so
  building automata from several threads is safe. Edge joins are keyed on the
  symbol itself rather than on its hash.
- `getAllTerms` truncates at recursion and lists an unconstrained node through
  the shared enumerator, so each such term appears once.
- The term-search application layer is not part of the library.
