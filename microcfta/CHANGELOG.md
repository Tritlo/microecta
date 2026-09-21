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
- `Data.CFTA.Enumeration`: one enumerator for every theory. `terms` solves
  path equalities by unification and stops at recursion, `plainTerms` lists an
  automaton without constraints lazily by depth, and `runs` returns each
  accepting run with the residual constraints it must satisfy. The pruning
  oracles are `termsPrune` and `termsPruneWith`.
- `Data.CFTA.Symbol`: interned text symbols shared by every layer.

### Differences from microecta 0.1.0.0

- Concrete terms are `Data.Tree.Tree` from `containers`, and partial or
  truncated enumeration uses `PartialSymbol symbol` rather than inventing
  symbols in the caller's alphabet.
- The hash-consing and memo tables are immutable maps updated atomically, so
  building automata from several threads is safe. Edge joins are keyed on the
  symbol itself rather than on its hash.
- `terms` truncates at recursion and lists an unconstrained node through
  the shared enumerator, so each such term appears once.
- The term-search application layer is not part of the library.
- The `Pretty` class and the path-trie `Ord` instance are gone; `show` the
  constraint, or compare equality classes by their path lists.
