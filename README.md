# microecta

The workspace contains these Cabal packages:

| Package | Purpose |
| --- | --- |
| [`microfta`](microfta/README.md) | Shared interned graph, ordinary trees, FTA syntax, and datatype derivation. |
| [`microfta-generator`](microfta-generator/README.md) | Ranked ordinary generation, replay, and shrinking. |
| [`microecta`](microecta/README.md) | Equality-constrained tree automata. |
| [`microecta-generator`](microecta-generator/README.md) | Indexed ECTA generation, grouped joins, replay, and shrinking. |
| [`microlta`](microlta/README.md) | Liquid automata, recognition, substitution, and semantic pruning. |
| [`microlta-generator`](microlta-generator/README.md) | Guarded sources, symbolic compilation, replay, and valid shrinking. |

`microfta` provides a standalone constraint-parameterized graph.
`microecta` uses that shared graph for its equality interpretation.
`microfta-generator` provides shared rank plans and ordinary FTA generation.
`microecta-generator` uses the shared rank engine.
Bounded annotated imports count nested equality and overlapping alternatives symbolically.
`microlta` interprets refinement-labelled automata with a solver.
`microlta-generator` compiles guarded sources and bounded imports into pure generation.

Build and test the workspace:

```sh
cabal build all
cabal test all
```

Enter `nix-shell` to put Z3 on `PATH` before running the LTA tests.

Run the executable examples:

```sh
cabal run fta-pairs
cabal run ecta-finite-languages
cabal run liquid-pairs
cabal run lta-safe-division
cabal run lta-automaton-interop
```
