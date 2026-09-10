# FTA, ECTA, and LTA syntax

The three layers share one ranked-transition model, but each adds a different
kind of information:

| Layer | Says | Natural authoring form |
| --- | --- | --- |
| FTA | These constructor shapes exist. | `FTA.node "label" $ FTA.do ...` |
| ECTA | These paths contain the same term. | `ECTA.node "label" $ ECTA.do ...` |
| LTA | These refinements logically imply one another. | `LTA.node "label" guard $ LTA.do ...` |

## The worked progression

The repository uses one running progression rather than three unrelated toy
examples:

1. [`Data.Tree.FTA.UntypedExpressionLanguage`](../microecta-generator/common/Data/Tree/FTA/UntypedExpressionLanguage.hs)
   generates integer syntax. Constructor shape is the only constraint.
2. [`Data.ECTA.TypedExpressionLanguage`](../microecta-generator/common/Data/ECTA/TypedExpressionLanguage.hs)
   adds Boolean expressions. Equality constraints connect an operation's
   signature with the result types of its children.
3. [`Data.LTA.StateMachineTraceLanguage`](../microlta-generator/common/Data/LTA/StateMachineTraceLanguage.hs)
   turns those values and operations into a typed stack machine. The result
   refinement of a trace prefix is the next command's input state, so command
   admissibility and the next stack type are dependent on the whole prefix.

The finite depth bound makes the QuickCheck language enumerable; it does not
enumerate a separate transition for every pair of states. Operations retain
symbolic schemas such as
`Stack (TInt ': TInt ': s) -> Stack (TInt ': s)`, and Z3 instantiates `s` from
the preceding trace. A bounded FTA or ECTA could tabulate the same finite
machine, but it would lose precisely this compositional input/output contract.

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

An FTA view carrying ECTA constraints uses the ECTA namespace:

```haskell
ECTA.transition "pair" [atom, atom]
  (mkEqConstraints [[path [0], path [1]]])
```

The underlying graph remains `Data.Tree.FTA.FTA`, but `EqConstraints` and its
construction syntax belong to ECTA rather than to the ordinary FTA API.

An LTA adds its refinement label and lets the guard name child positions:

```haskell
LTA.transition "sqrt" nonNegative [integer]
  (\argument -> argument `requires` nonNegative)
```

Programmatic code can still construct raw transitions and paths.

## QuickCheck generators

Every qualified do-block describes direct constructor children. The matching
`node` supplies the domain symbol and closes the block:

```haskell
pair = FTA.node "pair" $ FTA.do
  left  <- atoms
  right <- atoms
  FTA.pure (left, right)
```

ECTA dependencies are finite structural keys, so they belong inside the
qualified do-block:

```haskell
typedApplication children = ECTA.node "application" $ ECTA.do
  build    <- functionsBySignature
  argument <- children
  ECTA.pure (build argument)
```

`ECTA.node` keeps the equality constraints accumulated by the grouped block,
but replaces the generator's private join label with `"application"`.

LTA dependencies need the solver. The do-block still builds independent child
languages, while the adjacent guard lambda names the symbolic positions in the
same order:

```haskell
safeDivision =
  LTA.node "divide" divisionGuard $ LTA.do
    numerator   <- integers
    denominator <- integers
    LTA.pure (Divide numerator denominator)

divisionGuard :: Position -> Position -> LiquidConstraint
divisionGuard _ denominator = denominator `requires` nonZero
```

`LTA.node` uses the universally accepting result refinement internally. A
language that computes a more precise result uses `refinedNode` or
`refinedNodeBy`; the ordinary property-writer call contains only the meaningful
guard name.

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
