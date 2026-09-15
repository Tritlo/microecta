# microecta

The workspace contains these Cabal packages:

| Package | Purpose |
| --- | --- |
| [`microfta`](microfta/README.md) | Shared interned graph, ordinary trees, FTA syntax, and datatype derivation. |
| [`microfta-generator`](microfta-generator/README.md) | Ranked ordinary generation, replay, and shrinking. |
| [`microecta`](microecta/README.md) | Equality-constrained tree automata. |
| [`microecta-generator`](microecta-generator/README.md) | Indexed ECTA generation, grouped joins, replay, and shrinking. |

`microfta` provides a standalone constraint-parameterized graph.
`microecta` uses that shared graph for its equality interpretation.
`microfta-generator` provides shared rank plans and ordinary FTA generation.
`microecta-generator` uses the shared rank engine.
Bounded annotated imports count nested equality and overlapping alternatives symbolically.

Build and test the workspace:

```sh
cabal build all
cabal test all
```

Run the executable examples:

```sh
cabal run fta-pairs
cabal run ecta-finite-languages
```
