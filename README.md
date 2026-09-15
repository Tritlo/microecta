# microecta

This repository contains four Cabal packages with a shared automaton engine:

| Package | Purpose |
| --- | --- |
| [`microfta`](microfta/README.md) | Ordinary tree automata, the shared interned graph, and datatype derivation. |
| [`microfta-generator`](microfta-generator/README.md) | Ranked ordinary generation, replay, and shrinking. |
| [`microecta`](microecta/README.md) | The small equality-constrained tree automata core. |
| [`microecta-generator`](microecta-generator/README.md) | Indexed ECTA generators with QuickCheck integration, exact replay, and structural shrinking. |

`microecta` and `microfta-generator` depend on `microfta`.
`microecta-generator` depends on `microecta` and `microfta-generator`. The core packages do not depend
on the generator packages or on QuickCheck.

`Data.Tree.FTA.Generic` derives a shared grammar, constructor metadata, and a
term codec from a regular algebraic datatype. Recursive types form graph cycles.
The ordinary generator accepts explicit depth or size bounds. Primitive fields
use caller-supplied finite domains. See the package READMEs for examples.

`microecta-generator` adds grouped equality joins, typed datatype imports, and
symbolic counting for nested equality and overlapping alternatives. Shared
rank plans preserve exact replay and generate only the selected value.

Run `cabal run ecta-finite-languages` for the combined FTA/ECTA example.

Build and test the whole workspace from the repository root:

```sh
cabal build all -j1
cabal test all -j1
```

The examples in the entry-point modules are executable. Run them with
[`doctest`](https://hackage.haskell.org/package/doctest):

```sh
cabal install doctest
cabal repl --with-repl=doctest lib:microfta
cabal repl --with-repl=doctest lib:microfta-generator
cabal repl --with-repl=doctest lib:microecta
cabal repl --with-repl=doctest lib:microecta-generator
```
