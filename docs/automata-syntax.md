# FTA, ECTA, and LTA syntax

The three layers share one ranked-transition model, but each adds a different
kind of information:

| Layer | Says | Natural authoring form |
| --- | --- | --- |
| FTA | These constructor shapes exist. | `FTA.node "label" $ FTA.do ...` |
| ECTA | These paths contain the same term. | `ECTA.node "label" $ ECTA.do ...` |
| LTA | These refinements logically imply one another. | `LTA.node "label" guard $ LTA.do ...` |

`microfta` owns ordinary terms, the common interned engine, and the FTA graph.
`Node symbol constraint` and `Edge symbol constraint` carry `()` for an FTA,
`EqConstraints` for an ECTA, or `LiquidConstraint` for liquid construction.
The constrained packages define and interpret their constraint fields.
`microfta-generator` owns
the ranked layer and `Data.Tree.FTA.Gen`. The ECTA modules belong to
`microecta` and `microecta-generator`; the LTA modules belong to `microlta`
and `microlta-generator`. Each application must declare the package whose
modules it imports. The FTA packages have no dependency on either constrained
layer.

## The worked progression

The repository uses one running progression rather than three unrelated toy
examples:

1. [`Data.Tree.FTA.UntypedExpressionLanguage`](../microfta-generator/common/Data/Tree/FTA/UntypedExpressionLanguage.hs)
   generates integer syntax. Constructor shape is the only constraint.
2. [`Data.ECTA.Gen.Example.TypedExpressionLanguage`](../microecta-generator/src/Data/ECTA/Gen/Example/TypedExpressionLanguage.hs)
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

The underlying graph remains `Data.CFTA.FTA`, but `EqConstraints` and its
construction syntax belong to ECTA rather than to the ordinary FTA API.

An LTA adds its refinement label and lets the guard name child positions:

```haskell
LTA.transition "sqrt" nonNegative [integer]
  (\argument -> argument `requires` nonNegative)
```

A named guard must take one argument per direct child, including unused
arguments. `transition` retains an argument-count error for `automaton` to
report. `automatonWithFinals` accepts any final-state set, including the empty
set. Programmatic code can still construct raw `Data.LTA.Transition` values
and paths.

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
`refinedNodeByRoots`; the ordinary property-writer call contains only the meaningful
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


## Compile once and retain an escape hatch

`LTA.compile solver language` preserves source order, occurrence weights, and
semantic pool shrinking. It groups candidates by the observations their guards
need. Bounded automata use symbolic counts for nested equality and overlapping
alternatives. Compilation reports unsupported guards and value-computed
refinements as errors. Use `explain` to render an error, and `validOutcomes`
for explicit diagnostics on small inputs. Sampling, replay, and shrinking
use the pure compiled result.

`LTA.fromLTA maximumHeight automaton` imports an existing automaton into the
same source syntax. It preserves graph sharing until compilation. Each distinct
accepted annotated term contributes one rank. Repeated ordinary pool draws keep
their separate ranks and weights. A leaf has height zero; an empty bound is an
empty source. The standalone
[`AutomatonInterop.hs`](../microlta-generator/examples/AutomatonInterop.hs)
checks this workflow with a recursive natural-number grammar.

`refinedNodeByRoots` takes one function from child root observations to the
result refinement. Compilation calls it once per observation group. The
explicit diagnostic evaluator uses the same function for each candidate.
