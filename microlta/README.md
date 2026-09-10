# microlta

`microlta` is the Liquid Tree Automata layer over `Data.Tree.FTA`. A transition
has a ranked constructor, its Liquid Fixpoint refinement, child states, and the
paper's Boolean constraint language. Syntactic `Same` and semantic `Entails`
remain LTA atoms under substitution, negation, conjunction, and disjunction.
Refinement implication is discharged through the small `Entailment`
boundary; `Data.LTA.LiquidFixpoint.withZ3` supplies the reusable Z3
implementation.

The complete pair `(constructor, refinement)` is one ranked-alphabet symbol,
not metadata outside the automaton. This can represent the paper literally: in
Figure 12 each formula is a nullary symbol such as
`LiquidSymbol "predicate" phi`, and the `f` transition relates its two formula
children. The generator DSL also offers a compressed convention in which a
program constructor carries its result refinement directly. That convention is
a surface encoding, not the definition of LTA.

`mkAutomatonWithFinals` accepts the paper's arbitrary non-empty final-state set.
It normalizes that set to one fresh state by taking the union of the original
final rows, exactly preserving Figure 6's denotation.

The literal Figure 12 shape is therefore ordinary Haskell data:

```haskell
figure12 =
  mkAutomaton qf
    [ (qf,
        [ Transition "f" true [qPredicate, qPredicate]
            (semanticConstraint (Entails (path [0]) (path [1])))
        ])
    , (qPredicate,
        [ Transition "predicate" phi1 [] unconstrainedConstraint
        , Transition "predicate" phi2 [] unconstrainedConstraint
        , Transition "predicate" phi3 [] unconstrainedConstraint
        ])
    ]
```

Here the three `(predicate, phi)` pairs are three distinct nullary alphabet
symbols. They are not a Haskell pool hidden behind `relate`.

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
- `allOf`, `anyOf`, and `notGuard` for Boolean composition, including `Same`.

`Satisfies position predicate` is a conservative convenience extension for the
common paper pattern `position Entails literalPredicate`. It avoids adding an
otherwise uninteresting predicate child to every surface DSL node; the literal
Figure 12 encoding can continue to use `Entails` between two tree positions.

Raw paths and guard constructors remain available for generated automata.

`denotationAtMost` is the small, materializing implementation of Figure 6. It
works for cyclic LTAs under an explicit tree-height bound and is the semantics
oracle against which optimized pruning and generation can be checked.

Cycles are legal. A guard may not inspect a position whose state participates
in a cycle, matching the paper's restriction that keeps solver obligations
finite. `semanticIntersection` exposes Equation 4 directly: it retains the
antecedent transition only when that refinement entails the consequent. It is
directional, not a symmetric logical meet.

`prune solver automaton` implements both rules behind the paper's pruning pass
and returns another LTA.
For `P-Syn-Eq`, it uses the ordinary `Data.Tree.FTA.intersectWith` product to
narrow the first position to the structural language also admitted at the
second. For `P-Sem-Ent`, it partitions transition sets at the observed positions
by refinement; actual/formal positions are partitioned by both refinement and
value-naming symbol. It retains precisely the combinations whose entailment
succeeds, replaces that semantic guard with `Top`, and removes newly dead
transitions to a fixed point. Nested positions produce shared state splits;
complete accepted terms are never constructed.

`pruneToECTA solver automaton` is a separate optimization. After ordinary LTA
pruning, it lowers residual `Top`, positive `Same`, and conjunctions of those
atoms to MicroECTA `EqConstraints`. Product intersection can remove disjoint
choices, but equality between independently selected arbitrary subtrees is not
in general a regular tree language. A negated, disjunctive, or still-semantic
constraint remains an LTA and makes this optional lowering fail explicitly.
`pruneSemantics` remains as a compatibility name for `pruneToECTA`.

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
phase in the paper's order: `prune`, `similarity`, then `minimize`.

For an encoding that stores the complete result-type refinement on the program
transition, `refinementSubtypingBy` supplies a compact adapter. Its
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
Likewise, a cross-state merge from the normalized final state is rejected with
`FinalSimilarityTarget`: the paper minimizes program transitions below its
distinguished goal transition, so redirecting the goal itself would strand the
accepted representative.
