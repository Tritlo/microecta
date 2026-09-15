# Changelog

## 0.1.0.0 - Unreleased

Initial release.

- `Data.Tree.Term`: the shared first-order term type.
- `Data.Tree.FTA` and `Data.Tree.FTA.Syntax`: checked explicit-state finite
  tree automata with ranked-alphabet validation, cycle inspection, depth
  bounding, and reachable product intersection.
- `Data.Tree.FTA.Interned`: the constraint-parameterized interned engine that
  the ECTA and LTA packages build on. Interning, recursion, traversal, union,
  and structural intersection are shared; `Constraint` supplies the theory.
- `Data.Tree.FTA.Generic`: derive a regular tree grammar, term codecs, and
  constructor metadata from an algebraic datatype with `Generic`, with
  explicit finite domains for atomic fields.
- `Data.Interned.Extended.HashTableBased`, `Data.Memoization`,
  `Utility.Fixpoint`, and `Utility.HashJoin`: the process-global interning and
  memoization tables the engine uses.
