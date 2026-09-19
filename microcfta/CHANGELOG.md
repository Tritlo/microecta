# Changelog

## 0.1.0.0 - Unreleased

Initial release. `microcfta` consolidates the ordinary tree automaton engine,
the equality-constrained tree automata of `microecta`, and liquid tree
automata into one package with one representation. It supersedes
`microecta` 0.1.0.0.

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

### Migrating from microecta 0.1.0.0

- Import `Data.CFTA.Equality` instead of `Data.ECTA`, `Data.ECTA.Paths`, and
  `Data.ECTA.Term`. The type of an ECTA is `Node symbol EqConstraints`; the
  `Node`, `Edge`, and `Mu` patterns exported by `Data.CFTA.Equality` fix the
  constraint. `edgeEcs` is `edgeConstraint`, and `toFTA` and `toTree` return
  `FTAViewError`.
- Concrete terms are `Data.Tree.Tree` from `containers`. Replace the `Term`
  type with `Tree` and the `Term` constructor with `Node`. `Show` and `Read`
  use the standard `Node` record format.
- Partial and truncated enumeration uses `PartialSymbol symbol` rather than
  inventing symbols such as `v0` in the caller's alphabet.
  `getAllTruncatedTerms` distinguishes concrete symbols from `UVarHole`, and
  `expandPartialTermFrag` marks `TruncatedRecursion`.
- `getAllTerms` truncates at recursion and yields the marker term `Mu`;
  unfold with `unfoldBounded` first. It lists a node with no recursion and no
  equality constraint through the shared enumerator, so each such term appears
  once.
- The hash-consing and memo tables are immutable maps updated atomically, so
  building automata from several threads is safe. Edge joins are keyed on the
  symbol itself rather than on its hash, so a colliding `Hashable` instance can
  no longer drop an alternative.
- The expandable-variable scan is one pass over the UVar slots, which halved
  the time and allocation of constrained enumeration.
- Fixed `unfoldBounded` looping on a negative bound, `maxIndegree` returning
  `minBound` for an empty node, and enumeration of an automaton whose root is
  a `Mu`.
- The term-search compatibility layer is `Data.CFTA.Example.TermSearch.*`.
