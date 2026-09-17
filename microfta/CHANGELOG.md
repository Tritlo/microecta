# Changelog

## 0.1.0.0 - Unreleased

Initial release.

- Concrete terms use `Data.Tree.Tree` from `containers`.
- `Data.Tree.FTA`: checked explicit-state finite tree automata with
  ranked-alphabet validation, cycle inspection, depth bounding, reachable
  product intersection, and term enumeration by depth.
- `Data.Tree.FTA.Interned`: the constraint-parameterized interned engine that
  the ECTA and LTA packages build on. Interning, recursion, traversal, union,
  and structural intersection are shared; `Constraint` supplies the theory.
- `Data.Tree.FTA.Generic`: derive a regular tree grammar, term codecs, and
  constructor metadata from an algebraic datatype with `Generic`, with
  explicit finite domains for atomic fields. `Atomic` and `atomic` declare
  further atomic types.
- `Data.Tree.FTA.Interned.Cache` and `Data.Tree.FTA.Interned.Memo`: the
  process-global interning and memoization tables the engine uses.
