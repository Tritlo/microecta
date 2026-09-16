# microlta

`microlta` is the Liquid Tree Automata layer over `microfta`'s `Data.Tree.FTA`.
It also uses `microecta` for equality constraints and the optional ECTA bridge.
A transition
has a ranked constructor, its Liquid Fixpoint refinement, child states, and the
paper's Boolean constraint language. Syntactic `Same` and semantic `Entails`
are LTA atoms. Guards support substitution, negation, conjunction, and disjunction.
Refinement implication is discharged through the small `Entailment`
boundary; `Data.LTA.LiquidFixpoint.withZ3` supplies the reusable Z3
implementation.

`LiquidConstraint` implements the common engine's pure `Constraint` interface.
You can construct `Data.Tree.FTA.Interned.Node LiquidSymbol LiquidConstraint`
with the same interned nodes and edges used by FTA and ECTA. `fromInterned`
retains its refinements and guards, assigns explicit state names, and runs the
normal LTA validation. It rejects open graphs and guards that inspect recursive
states. Construction does not call the solver. LTA recognition, pruning, and
semantic intersection remain operations of this package.

Position substitutions apply simultaneously within each scope and avoid bound
variable capture in refinement expressions. Actual refinements remain facts
about the surrounding environment. A substitution does not rename those facts.
Equal complete actual terms share one value identity for semantic entailment.
Different actual terms with the same constructor name receive fresh solver
values with the sort declared for that name.

Bare `Same` compares the original annotated subtrees, as in ECTA. Inside a
`Substitute` scope it compares renamed views of those trees. Each scope replaces
formal constructor symbols and free names in refinement annotations with the
corresponding actual symbols. The first non-identity mapping for a repeated
formal name takes precedence. Nested scopes apply from inner to outer. Tree
shape and generated output terms stay unchanged; substitution does not splice
an actual subtree into a formal leaf. This is the library's specified
interpretation of the paper's general substitution syntax.

For equally refined leaves `x` and `y`, `Same(left,right)` rejects `pair(x,y)`.
The guard `[x/y].Same(left,right)` accepts it because both compared views contain
`x`. Refinement annotations still participate in exact syntactic comparison.
Use `withActualFor` or `withActualsFor` to scope the complete constraint,
including any cached positive equalities. Scoped equality remains an LTA guard;
it cannot be lowered directly to ordinary ECTA path equality.

`Entailment decide` retains the simple query interface. A query that needs fresh
declarations returns `Unknown` through that interface. `entailmentWithBindings`
accepts a callback that receives `(freshName, declaredName)` pairs. The Z3 adapter
declares each fresh value with the sort of `declaredName`. Generator query caches
include these bindings.

The complete pair `(constructor, refinement)` is one ranked-alphabet symbol,
not metadata outside the automaton. This can represent the paper literally: in
Figure 12 each formula is a nullary symbol such as
`LiquidSymbol "predicate" phi`, and the `f` transition relates its two formula
children. The generator DSL also offers a compressed convention in which a
program constructor carries its result refinement directly. That convention is
a surface encoding, not the definition of LTA.

`mkAutomatonWithFinals` accepts the paper's arbitrary final-state set, including
the empty set. It normalizes multiple final states to one fresh state whose row
is the union of the original final rows. An empty set becomes a fresh final
state with no transitions; a singleton needs no normalization. These cases
preserve Figure 6's denotation. The input state set can also be empty when the
final-state set is empty.

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
Named `Data.LTA.Syntax.transition` values retain construction errors until
`automaton` checks their rows. Wrap a raw `Data.LTA.Transition` in `Right` to
include it in a named-syntax row.

`denotationAtMost` is the small, materializing implementation of Figure 6. It
works for cyclic LTAs under an explicit tree-height bound and is the semantics
oracle against which optimized pruning and generation can be checked.

## Visualize the automaton

`toTree` converts the reachable graph to a finite tree with typed labels:

```haskell
toTree :: Automaton -> Tree (Either (StateView State) Transition)
```

`Left` contains a state definition or reference. `Right` contains the complete
transition, including its refinement and constraint. Map these labels to
strings before using `drawTree` from `containers`. This example defines its own
renderer and uses Liquid Fixpoint's `showpp` for refinement formulas:

```haskell
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.LTA
import Data.LTA.Refinement (true, value, (.>=.))
import Data.List (intercalate)
import qualified Data.Text as Text
import Data.Tree (drawTree)
import Language.Fixpoint.Types (showpp)

-- | A square root whose argument must have a nonnegative refinement.
graph :: Either AutomatonError Automaton
graph =
    mkAutomaton
        (State 0)
        [
            ( State 0
            ,
                [ Transition
                    "sqrt"
                    true
                    [State 1]
                    (semanticConstraint (Satisfies (path [0]) nonNegative))
                ]
            )
        ,
            ( State 1
            , [Transition "zero" nonNegative [] unconstrainedConstraint]
            )
        ]
  where
    nonNegative = value .>=. (0 :: Int)

-- | Choose state names and mark recursive and shared references.
renderNode :: StateView State -> String
renderNode view = case fmap (("q" ++) . show . unState) view of
    Expanded name -> name
    Recursive name -> "mu " ++ name
    Shared name -> "ref " ++ name

-- | Render symbols, nontrivial refinements, and complete constraints.
renderTransition :: Transition -> String
renderTransition transition =
    Text.unpack name ++ refinementLabel ++ guardLabel
  where
    Symbol name = transitionSymbol transition
    refinement = transitionRefinement transition
    refinementLabel
        | refinement == true = ""
        | otherwise = " {" ++ showpp refinement ++ "}"
    guardLabel = case constraintAsGuard (transitionConstraint transition) of
        Top -> ""
        Satisfies position predicate ->
            " [refinement("
                ++ intercalate "." (map show (unPath position))
                ++ ") entails "
                ++ showpp predicate
                ++ "]"
        guard -> " [" ++ show guard ++ "]"

-- | Draw the graph with the chosen state and transition labels.
main :: IO ()
main = do
    automaton <- either (fail . show) pure graph
    putStr $ drawTree $ fmap (either renderNode renderTransition) $ toTree automaton
```

Add `microlta`, `containers`, `text`, and `liquid-fixpoint` to the component's
`build-depends`. To run the example in this checkout, save it as `Main.hs` at
the workspace root:

```sh
cabal build microlta
cabal exec -- runghc -package=microlta -package=liquid-fixpoint Main.hs
```

This program prints:

```text
q0
|
`- sqrt [refinement(0) entails v >= 0]
   |
   `- q1
      |
      `- zero {v >= 0}
```

`renderNode` and `renderTransition` are caller code. Change them to use domain
names or a different constraint notation. The example omits only `true`
refinements and `Top` guards. `constraintAsGuard` recovers the complete
constraint, including cached equalities. Guards other than `Satisfies` use a
`Show` fallback, so the renderer retains every obligation.

`Recursive state` ends a cycle; `Shared state` refers to a state expanded
earlier. The example displays these as `mu qN` and `ref qN`. This view does not
enumerate terms or call a solver.

## Cycles and pruning

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

Pruning preserves missing observations until it evaluates the complete Boolean
guard. A missing path in an optional branch does not discard a candidate.
Semantic guards that need equality of complete compound actuals can remain on
the LTA: sparse root observations cannot always determine whether two actuals
share a value. In that case pruning retains the original transition and guard.
`accepts` and `denotationAtMost` continue to evaluate the complete terms.

`pruneToECTA solver automaton` is a separate optimization. After ordinary LTA
pruning, it lowers residual `Top`, positive `Same`, and conjunctions of those
atoms to MicroECTA `EqConstraints`. Product intersection can remove disjoint
choices, but equality between independently selected arbitrary subtrees is not
in general a regular tree language. A negated, disjunctive, or still-semantic
constraint remains an LTA and makes this optional lowering fail explicitly.

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

`similarityPairs` exposes directed `(subtype, supertype)` pairs as
`TransitionId`s. A `Similarity` also retains the exact source automaton.
`minimize` returns `StaleSimilarity` if transition contents, states, or the
accepting state have changed, including when the relation is empty.

Minimization applies a finite schedule of the paper's M-Trans rule. It resolves
transitive representatives, then considers each selected original supertype
once in table order. Each step retains existing incoming transitions and adds
copies that replace the supertype's target state with the representative's
target state in the children. Repeated occurrences of that state change
together. Later steps can copy transitions added by earlier steps. The step
removes only the selected original supertype transition and deduplicates equal
transitions. Shared target rows retain unrelated alternatives. One target can
have multiple representatives, and final transitions can participate.

Equivalent types keep the first transition in table order. When incomparable
subtypes can replace one supertype, the first inferred dominator selects its
representative. The state set and normalized final state stay unchanged. This
schedule does not promise a globally minimal automaton or an unchanged term
language.

The complete batch falls back to the original automaton if proposed redirects
make a representative depend on its removed target, a representative loses all
finite structural derivations, the last finite structural final derivation is
lost, or a copied guard would inspect a cyclic state. Successful batches remove
transitions with structurally unproductive children. These checks use graph
productivity; they do not prove that arbitrary transition guards are satisfiable.
