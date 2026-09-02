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
finite. `semanticIntersection` exposes Equation 4 directly: it retains the
antecedent transition only when that refinement entails the consequent. It is
directional, not a symmetric logical meet.

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

## Similarity and minimization

`similarity` and `minimize` are core automaton operations corresponding to the
paper's S-Trans/S-Eq and M-Trans/M-LTA rules. A `Subtyping` callback receives
the current LTA and compares the type sub-automata associated with two program
transitions. This supports source languages that represent an expression's type
as a distinguished child state, as the paper does:

```haskell
let sourceSubtyping = Subtyping $ \current left right ->
      compareTypeStates current left right
Right related <- similarity sourceSubtyping automaton
Right reduced <- pure $ minimize automaton related
```

`reduce solver sourceSubtyping automaton` runs the complete static reduction
phase in the paper's order: `prune`, `similarity`, then `minimize`. Transition
discovery remains a source-language frontend concern; it is not smuggled into
the generator.

For a smaller frontend that stores the complete result-type refinement on the
program transition, `refinementSubtypingBy` supplies the common adapter. Its
projection represents the non-liquid type shape and can exclude structural
transitions:

```haskell
let sourceSubtyping = refinementSubtypingBy solver $ \transition ->
      typeClass (transitionSymbol transition)
Right related <- similarity sourceSubtyping automaton
Right reduced <- pure $ minimize automaton related
```

`similarityPairs` exposes the inferred directed `(subtype, supertype)` pairs as
stable `TransitionId`s. Minimization removes each supertype transition and
redirects incoming child-state edges to the retained subtype target. Equivalent
types keep the first transition in table order, and incomparable types remain.

The paper's construction gives a representative program transition its own
target state. `minimize` checks that invariant before a cross-state redirect:
if the removed target also owns an unrelated surviving transition, it returns
`SharedSimilarityTarget` instead of silently discarding that language. Multiple
alternatives in one target row remain safe when their representative is in that
same row, which is the shape used by compact handwritten LTAs.
