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

GHC 9.14 is the supported compiler series. The workspace selects GHC 9.14.1.
The packages require `base >=4.22 && <4.23` and `containers >=0.8 && <0.9`.

Build and test the workspace:

```sh
cabal build all
cabal test all
```

Run the executable examples:

```sh
cabal run fta-pairs
```
