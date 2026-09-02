# microlta

`microlta` is the Liquid Tree Automata layer over `Data.Tree.FTA`. A transition
has a ranked constructor, its Liquid Fixpoint refinement, child states, and a
Boolean guard. Refinement implication is discharged through the small
`Entailment` boundary; `Data.LTA.LiquidFixpoint.withZ3` supplies the reusable Z3
implementation.

Handwritten FTAs and LTAs deliberately have the same shape:

```haskell
import Data.LTA.Guard (requires, unconstrained)
import Data.LTA.Refinement ((.>=.))
import qualified Data.LTA.Syntax as LTA

numbers =
  LTA.automaton expression
    [ LTA.row expression
        [ LTA.transition "sqrt" nonNegative [number]
            (\argument -> argument `requires` nonNegative)
        ]
    , LTA.row number
        [LTA.transition "zero" nonNegative [] unconstrained]
    ]
  where
    nonNegative = value .>=. 0
```

The lambda receives symbolic child positions in transition order. Useful guard
phrases are:

- ``candidate `requires` predicate`` for an ordinary precondition;
- ``actual `isSubtypeOf` expected`` for semantic subtyping;
- ``actual `isSameTermAs` expected`` for ECTA-style structural equality;
- `withActualFor actual formal guard` for dependent result types; the actual
  symbol is assumed to satisfy the refinement carried by its whole subtree;
- `allOf`, `anyOf`, and `notGuard` for Boolean composition.

Raw paths and guard constructors remain available for generated automata.

Cycles are legal. A guard may not inspect a position whose state participates
in a cycle, matching the paper's restriction that keeps solver obligations
finite. `refinementRelation` and `semanticIntersection` expose the semantic
comparison used by pruning and similarity minimisation.

`prune solver automaton` is the first paper-style reduction pass. It discharges
guards from transition refinements, replaces successful guards with `Top`, and
removes failed or newly dead transitions to a fixed point. It works on the
automaton graph: no accepted tree is constructed. The current small core
handles semantic positions whose reachable transitions share one root
refinement. Constructor symbols may differ because ordinary entailment does
not inspect them; actual/formal substitution positions must also share the
value-naming symbol. This covers ground-type states, dependent command schemas,
and state-indexed trace layers. It reports `NonHomogeneousGuardPosition` where
the full paper algorithm must perform semantic intersection and split states,
and
`StructuralGuardNeedsIntersection` where ECTA equality intersection is needed.
Those errors are deliberate boundaries, not silent enumeration fallbacks.
