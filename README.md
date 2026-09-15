# microecta

The workspace contains these Cabal packages:

| Package | Purpose |
| --- | --- |
| [`microfta`](microfta/README.md) | Shared interned graph, ordinary trees, FTA syntax, and datatype derivation. |
| [`microecta`](microecta/README.md) | Equality-constrained tree automata. |
| [`microecta-generator`](microecta-generator/README.md) | Indexed ECTA generation, grouped joins, replay, and shrinking. |

`microfta` provides a standalone constraint-parameterized graph.

Build and test the workspace:

```sh
cabal build all
cabal test all
```
