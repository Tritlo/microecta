# Language proof scope

`MicroCFTA/Language.lean` imports `Std` only. Lean 4.34.1 checks the module.
The model is a new executable reference interpreter. It is not an extraction
of the Haskell implementation.

## Checked results

- `mem_products`: ordered Cartesian products contain exactly the pointwise
  choices. Child arity is part of this result.
- `mem_enumerate_iff`: a term occurs in bounded enumeration if and only if it
  has an accepting run and its height is at most the fuel. A leaf has height
  one in this module. Haskell depth `d` corresponds to fuel `d + 1`.
- `accepts_iff_eventually_enumerated`: every accepted finite term occurs at
  some finite fuel. States can refer to themselves. No acyclicity assumption
  is required. Outgoing transition lists and child lists must be finite.
- `enumerate_mono`: increasing the bound preserves terms.
- `accepts_intersect_iff`: synchronous product accepts exactly the intersection
  of two languages. Product edges require equal symbols and arities. Their
  children are paired and their guards are conjoined.
- `mem_enumerate_intersect_iff`: the same intersection result holds at each
  common height bound.
- `pathEquality_correct`: the executable guard requires two existing, equal
  subterms. Equal failed lookups do not establish path equality.
- `strict_prefix_paths_not_equal`: a finite tree cannot satisfy an equality
  between a path and a strict extension of that path. This justifies rejection
  of a class that contains prefix-related paths.
- `equality_sharing_preserves_terms`: for two immediate children, enumeration
  followed by an equality filter has the same term set as enumeration of the
  child-language intersection followed by use of that one child at both
  positions. The proof retains the shared choice.

These are general proofs. They are not bounded example checks. `Accepts` is an
inductive finite-run relation. `enumerate` is a separate executable function.
The completeness proof does not assume that the enumerator contains all
accepted terms.

## Source correspondence

| Lean definition or result | Haskell or paper counterpart | Limit |
| --- | --- | --- |
| `Accepts` | LTA Figure 6; `Refinement/Denotation.hs:49`; `Internal/Tree.hs:267` | A guard is a total Boolean function of its complete term. Solver `Unknown` and effects are outside this model. |
| `enumerate` and `mem_enumerate_iff` | `Internal/Tree.hs:174`; `Refinement/Denotation.hs:76` | The Lean implementation builds bounded Cartesian products. It does not use exact-level tables or suspended UVars. |
| Fuel and term height | `Interned/Operations.hs:216`, `boundDepth` | The theorem states the required behavior. The graph rewrite in `boundDepth` is not itself translated. |
| `intersect` | `Interned/Operations.hs:318`, `:332`, and `:469` | The model uses explicit state pairs. Haskell recursive binder reconstruction, memoization, and `conjoinConstraints` remain proof obligations. |
| `Term.atPath`, `PathsEqual` | ECTA Definitions 3.1 and 3.2; `Data.CFTA.Path` | Paths use natural-number child indices. Negative Haskell indices are outside the model. |
| `strict_prefix_paths_not_equal` | ECTA consistency discussion after Definition 3.3; `Equality/Constraint.hs:316` | This proves rejection of a direct strict-prefix conflict. Closure and detection of indirect conflicts remain outside the model. |
| `equality_sharing_preserves_terms` | `Enumeration.hs:166`, `intersectUVarValue`; `Enumeration.hs:427`, `enumerateEdge` | This proves the mathematical operation for two immediate children. It does not verify the union-find store, arbitrary suspended paths, or expansion scheduling. |

`Enumeration.terms`, `termsWith`, and `runs` are not concrete-language
interpreters for unrestricted recursive constrained graphs. They stop at `Mu`.
`terms` also leaves residual guards undecided. The Haskell comments state these
limits. The Lean soundness theorem does not apply to recursion markers emitted
by those APIs. Bound the graph and decide every guard before comparing the
concrete accepted language.

A reflexive `Same p p` guard requires path existence. The Haskell code keeps
that case as a residual guard. In contrast, `mkEqConstraints` discards classes
with fewer than two distinct paths. The existing constraint tests explicitly
require that behavior. Thus `pathEquality_self_iff` models the `Same` guard,
not a singleton class passed through `mkEqConstraints`. ECTA Definition 3.2
states existence for a nonempty path equivalence class, so this is a semantic
restriction to record when translating paper-level classes.

The enumeration lists can repeat a term when multiple runs accept it. All
language theorems concern membership. They do not establish list order, term
uniqueness, or a uniform term distribution. A probability proof must state
whether it counts runs or distinct terms.

## Validation

The direct compiler command is:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/Language.lean
```

The project build also checks this module. The principal theorems were inspected
with `#print axioms`. Their dependencies contain only Lean's standard
`propext`, `Quot.sound`, and, for some proofs, `Classical.choice`. No proof uses
`sorry`, `admit`, a custom axiom, or `native_decide`.

No implementation error was established by the language module inspection.
The root spike report records independent findings from guard and generator
validation. The source correspondence limits above prevent a claim that the
entire current Haskell design has been proved sound.
