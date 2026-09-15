# microfta

Derive `Generic` and declare an empty `HasFTA` instance to obtain a datatype
grammar through `Data.Tree.FTA.Generic`:

```haskell
data Tree = Leaf Bool | Fork Tree Tree
  deriving Generic

instance HasFTA Tree

treeGrammar = deriveFTA @Tree
```

`deriveFTA` constructs one state per reachable type. It retains constructor
and field metadata, including record selectors, and both term codecs. It does
not enumerate values. `Int`, `Integer`, `Char`, and `Text` fields need an
explicit domain, such as `deriveFTAWith @(Maybe Int) (domain @Int [0, 1])`.
`Bool`, lists, `Maybe`, `Either`, unit, and tuples have built-in instances.
Declare an instance for each user datatype in a mutually recursive family.

Use `annotateDatatype` to add constructor constraints without repeating the
grammar. For handwritten graphs, `annotate` has access to each state and
transition. `mapSymbols` changes labels and checks their arities. Constraint
interpretation belongs to the ECTA and LTA packages.

The first derivation interface supports regular algebraic datatypes. It rejects
recursion that grows type arguments. It has no instances for function fields.
GADTs and existential fields cannot use the default `Generic` derivation.
The codecs describe the whole datatype. They do not check configured domains
or interpret annotations; the generated grammar enforces those restrictions.

`microfta` is the common tree-automaton engine. Its interned nodes and edges
carry a symbol type and a constraint type. Ordinary automata use `()` as the
constraint. ECTA and LTA supply path equalities and liquid guards. The package
has no dependency on either constrained layer or on a solver.

| Module | Purpose |
| --- | --- |
| `Data.Tree.Term` | The shared `Term` datatype and its structural instances. |
| `Data.Tree.FTA.Constraint` | Pure conjunction, the unconstrained value, and known contradictions. |
| `Data.Tree.FTA.Interned` | Shared canonical nodes and edges, recursion, traversal, union, intersection, and an explicit-state view. |
| `Data.Tree.FTA` | Checked finite-state transition graphs and ordinary recognition. |
| `Data.Tree.FTA.Syntax` | Named row and transition constructors. |

## Shared interned engine

```haskell
import qualified Data.Tree.FTA.Interned as Common
import Data.Tree.Term (Term (Term))

naturals :: Common.PlainNode String
naturals = Common.Mu $ \self -> Common.Node
  [ Common.Edge "zero" []
  , Common.Edge "successor" [self]
  ]

oneAccepted = Common.nodeRepresentsWith (\() _ -> True) naturals
  (Term "successor" [Term "zero" []])
```

`PlainNode symbol` is `Node symbol ()`. `mkEdge` accepts an explicit constraint.
The `Constraint` instance supplies conjunction and can reject a contradiction
without a solver. `nodeRepresentsWith` takes the concrete-term interpreter.
`intersect` matches symbols, conjoins constraints, and intersects child nodes.
It does not perform LTA refinement implication or semantic intersection.

`Mu` represents recursion. A recursive definition must place a constructor edge
between successive references to its binder. For example, `successor self` is
valid; `Mu id` is not a supported definition. Open recursive references are
internal construction values. `toFTA` rejects an open root.

`toFTA` exposes each reachable canonical node as one state. It retains the
constraint field and checks ranked arities. It does not enumerate terms. Pass
an acyclic unit-constraint view to `Data.Tree.FTA.Gen.fromFTA` for finite
generation. The `fta-pairs` example exercises this path without ECTA.

Interning and memo tables retain entries for the process lifetime. Each runtime
type combination has a typed table. Nodes share one identity sequence across
node tables; edges share another. Atomic insertion preserves canonical identity
when callers race. The tables do not evict entries or release a completed graph.

## Named states

Use the explicit-state interface when state names are part of the input or an
operation must inspect a transition table. ECTA operations use the interned
engine directly. They do not convert through this interface on each operation.

```haskell
import Data.Tree.FTA (FTAError, PlainFTA, accepts)
import qualified Data.Tree.FTA.Syntax as FTA
import Data.Tree.Term (Term (Term))

naturals :: Either (FTAError Int String) (PlainFTA Int String)
naturals = FTA.automaton 0
  [ FTA.row 0
      [ FTA.transition "zero" []
      , FTA.transition "successor" [0]
      ]
  ]

oneAccepted = fmap (`accepts` Term "successor" [Term "zero" []]) naturals
```

A symbol has one arity throughout a graph. Every referenced child state must
have a row. Cycles are valid. `PlainFTA` uses unit transition annotations.
Other packages can use the same graph with their own constraint annotations;
ordinary `accepts` takes a `PlainFTA` with unit annotations.

`intersect` constructs reachable product states. `intersectWith` lets the caller
combine compatible symbols and annotations. `stripGuards` forgets annotations;
it does not solve constraints.

Use `microfta-generator` for finite counting, replay, sampling, and shrinking.
Use `microecta` for equality constraints.

From the workspace root:

```sh
nix-shell --run 'cabal test microfta:unit-tests'
```
