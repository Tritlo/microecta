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

`prune solver automaton` is the paper's semantic-intersection reduction pass.
For every semantic guard, it partitions the transition sets reached at the
observed positions by refinement. Actual/formal positions are partitioned by
both refinement and value-naming symbol. It then retains precisely the
partition combinations whose entailment succeeds, replaces that semantic
guard with `Top`, and removes newly dead transitions to a fixed point. Nested
positions produce shared state splits; complete accepted terms are never
constructed.

Syntactic `Same` constraints remain on the resulting LTA because equality
between arbitrary subtrees cannot generally be compiled into a regular FTA.
When `Same` is one conjunct, independent semantic conjuncts are still reduced.
The generator adapter consequently refuses to multiply child counts while such
a residual guard remains; it never silently counts the unconstrained product.
