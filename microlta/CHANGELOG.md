# Changelog

## 0.1.0.0 - Unreleased

Initial release.

- `Data.LTA`: liquid tree automata over Liquid Fixpoint refinements, with the
  paper's Boolean guard language, actual-for-formal position substitution,
  transition-level semantic pruning, similarity, minimization, recursive
  states under the acyclic-guard restriction, and a reference denotation.
- `Data.LTA.Guard`, `Data.LTA.Syntax`, and `Data.LTA.Refinement`: guard
  syntax in terms of constructor arguments, handwritten transition rows, and
  refinement expression helpers.
- `Data.LTA.LiquidFixpoint`: Z3 entailment through Liquid Fixpoint.
- `Data.LTA.ECTA`: an optional lowering of the positive-equality fragment of
  a reduced LTA to `microecta`.
