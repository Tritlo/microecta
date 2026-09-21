# microcfta

Constrained finite tree automata for Haskell. One interned, hash-consed graph
`Node symbol constraint` describes a set of trees, a checked explicit-state
view `FTA state symbol constraint` names its states, and the constraint
parameter selects how much a transition can say:

| Constraint | Type | The transition says | Layer |
| --- | --- | --- | --- |
| none | `()` | These constructor shapes exist. | `Data.CFTA`, `Data.CFTA.Interned` |
| path equality | `EqConstraints` | These child positions hold the same term. | `Data.CFTA.Equality` |
| refinement | `LiquidConstraint` | This position's refinement implies that predicate. | `Data.CFTA.Refinement` |

The ordinary layer is a finite tree automaton (FTA). The equality layer is the
equality-constrained tree automaton (ECTA) of Koppel, Guo, de Vries,
Solar-Lezama and Polikarpova, [*Searching Entangled Program Spaces*, Proc.
ACM Program. Lang. 6(ICFP), 2022](https://doi.org/10.1145/3547622); its
engine descends from the [`microecta`](https://hackage.haskell.org/package/microecta)
package, which remains a separate, ECTA-only line. The refinement layer is the liquid tree automaton (LTA) of Mishra and
Jagannathan, with Liquid Fixpoint refinements and Z3 entailment. Concrete
terms are `Data.Tree.Tree` from `containers`.

- **Start with your datatype.** Derive `HasFTA` to get a grammar, constructor
  metadata, and codecs between Haskell values and constructor trees.
- **Restrict a language.** Choose finite literal domains, bound tree depth,
  intersect grammars, and restrict to a template.
- **Share repeated structure.** Interned nodes reuse equal subgraphs across
  construction and operations.
- **Add constraints only where you need them.** An automaton with no
  constraints is enumerated by the plain level-by-level enumerator. Equality
  constraints are propagated by reduction and solved by unification during
  enumeration. Refinement guards are discharged by pruning with a solver.

Language cardinality, random sampling, replay, and shrinking belong to the
separate `microcfta-generator` package.

## Module guide

| Module | Use it for |
| --- | --- |
| `Data.CFTA.Path` | Child-index paths, and reading, editing, and requiring positions in a graph. |
| `Data.CFTA.Symbol` | Interned text symbols that compare and hash by identity. |
| `Data.CFTA.Constraint` | Conjunction, the unconstrained value, and known contradictions. |
| `Data.CFTA.Equality.Constraint` | Equality constraints over paths and their tries. |
| `Data.Tree` from `containers` | Concrete constructor trees. |
