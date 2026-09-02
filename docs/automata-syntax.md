# FTA, ECTA, and LTA syntax

The three layers share one ranked-transition model, but each adds a different
kind of information:

| Layer | Says | Natural authoring form |
| --- | --- | --- |
| FTA | These constructor shapes exist. | `row` plus `transition` |
| ECTA | These paths contain the same term. | grouped qualified-do or `guarded` with `EqConstraints` |
| LTA | These refinements logically imply one another. | qualified-do plus a named guard lambda |

## Handwritten automata

An ordinary FTA has no annotation noise:

```haskell
FTA.automaton expression
  [ FTA.row expression
      [ FTA.transition "zero" []
      , FTA.transition "add" [expression, expression]
      ]
  ]
```

An FTA view carrying ECTA constraints changes only the transition constructor:

```haskell
FTA.guarded "pair" [atom, atom]
  (mkEqConstraints [[path [0], path [1]]])
```

An LTA adds its refinement label and lets the guard name child positions:

```haskell
LTA.transition "divide" true [integer, integer]
  (\_numerator denominator -> denominator `requires` nonZero)
```

Programmatic code can still construct raw transitions and paths.

## QuickCheck generators

ECTA dependencies are finite structural keys, so they belong inside the
qualified do-block:

```haskell
typedApplication children = ECTA.do
  build    <- functionsBySignature
  argument <- children
  ECTA.pure (build argument)
```

LTA dependencies need the solver. The do-block still builds independent child
languages, while the adjacent guard lambda names the symbolic positions in the
same order:

```haskell
safeDivision =
  LTA.node "divide" true divisionGuard $ LTA.do
    numerator   <- integers
    denominator <- integers
    LTA.pure (Divide numerator denominator)

divisionGuard :: Position -> Position -> Guard
divisionGuard _ denominator = denominator `requires` nonZero
```

This boundary is deliberate. Values bound inside the applicative block are
ordinary Haskell values; they cannot also be symbolic term positions without a
wrapper leaking through every generated type. Keeping the guard next to the
node gives the positions names, preserves ordinary generated values, and makes
dependent operations readable:

```haskell
applicationGuard result function argument =
  allOf
    [ argument `isSubtypeOf` inputType function
    , withActualFor argument (formalName function) $
        outputType function `isSubtypeOf` result
    ]
```

The alternatives considered were raw `Entails (path [2]) (path [1,1])`, an
index-taking `argument 0`, and extra predicate children. They remain possible
escape hatches, but none is the default: raw paths expose LTA machinery, numeric
arguments separate a name from its use, and predicate children alter the term
only to satisfy the API.
