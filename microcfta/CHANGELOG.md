# Changelog

## 0.1.0.0 - Unreleased

Initial release. `microcfta` consolidates an ordinary tree automaton engine,
equality-constrained tree automata, and liquid tree automata into one package
with one representation. The equality layer descends from `microecta`, which
remains a separate ECTA-only package.

- `Data.CFTA` and `Data.CFTA.Interned`: the explicit-state and interned
  automata, parameterized by a constraint theory. Ordinary automata use `()`.
  Recognition, depth bounds, product intersection, union, templates, paths,
  datatype derivation with `HasFTA`, constructor annotation by name with
  `annotateConstructors`, and level-by-level enumeration with
  `terms` and `termsUpToM` live here.
- `Data.CFTA.Equality`: equality-constrained automata as
  `Node symbol EqConstraints`, with reduction, membership, template
  restriction, and enumeration with unification variables. An automaton with
  no equality constraint and no recursion is enumerated by the shared
  enumerator.
- `Data.CFTA.Enumeration`: one enumerator for every theory. `terms` solves
  path equalities by unification and stops at recursion, `plainTerms` lists an
  automaton without constraints lazily by depth, and `runs` returns each
  accepting run with the residual constraints it must satisfy. The pruning
  oracles are `termsPrune` and `termsPruneWith`.
- Enumeration removes duplicate terms with a hash set, so `terms` and
  `termsUpToM` of `Data.CFTA` need `Hashable symbol`. With an optimized
  `hashable`, this takes less than half the time of an ordered set on the
  ambiguous enumeration benchmarks.
- `Data.CFTA.Symbol`: interned text symbols shared by every layer.
- Each equality class caches its hash, and path tries hash without a list
  conversion, so interning an edge no longer rehashes its constraint's trie.
  Class completion in `mkEqConstraints` is an in-package union-find, which
  removes the `equivalence` dependency. Over the core benchmark suite this
  cut allocation by 46% and instructions by 41%. The unfolding of each
  recursive node is shared, so repeated listings of a `Mu` do not rebuild it.
  The intersection memo hashes its recursive environment once, the common
  `Symbol`/`EqConstraints` instantiation has its own memo tables, and the
  equality reduction restricts and edits every required path of an edge in
  one traversal, which cut a further 15% of instructions and 17% of
  allocation on that suite.
- `Data.CFTA.Interned.fromFTA` imports a recursive graph as `Mu` nodes, and
  `boundDepth` bounds an interned graph by tree depth;
  `Data.CFTA.Enumeration.plainTermsAtMost` lists a graph up to a depth without
  building the bounded graph. The reduction in
  `Data.CFTA.Equality.Operations` narrows children by the `equalities` of any
  constraint theory.

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
- `terms` truncates at recursion and lists an unconstrained node through
  the shared enumerator, so each such term appears once.
- `reduceEqConstraints` repeats its pass over an edge's classes until the
  children stop changing, so its result is a fixpoint. One pass could leave
  children that a second call narrowed further.
- The term-search application layer is not part of the library.
- The `Pretty` class and the path-trie `Ord` instance are gone; `show` the
  constraint, or compare equality classes by their path lists.
