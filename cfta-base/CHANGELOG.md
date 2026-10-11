# Changelog

## 0.1.0.0 - Unreleased

Initial release, moved out of `cfta`:

- `Data.CFTA.Index`: the newtypes of indexes, ranks, counts, sizes, and
  weights, and the mixed-radix arithmetic of ranks.
- `Data.CFTA.Term` and `Data.CFTA.Path`: concrete terms and child-index paths.
- `Data.CFTA.Internal.Tree`: the tree searches over rows of alternatives.
- `Data.CFTA.Internal.UnionFind`: a persistent union-find.

A test suite states the contract of each module: the rank arithmetic, terms
against the rose trees that they replace, the tree searches against the
direct recursion, and the union-find against `equivalence`.
