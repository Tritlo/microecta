# microecta

This repository contains two Cabal packages with a one-way dependency:

| Package | Purpose |
| --- | --- |
| [`microecta`](microecta/README.md) | The small equality-constrained tree automata core. |
| [`microecta-generator`](microecta-generator/README.md) | Indexed ECTA generators with QuickCheck integration, exact replay, and structural shrinking. |

`microecta-generator` depends on `microecta`; the core package does not depend
on the generator package or on QuickCheck.

Build and test the whole workspace from the repository root:

```sh
cabal build all -j1
cabal test all -j1
```

The examples in the two entry-point modules are executable. Run them with
[`doctest`](https://hackage.haskell.org/package/doctest):

```sh
cabal install doctest
cabal repl --with-repl=doctest lib:microecta
cabal repl --with-repl=doctest lib:microecta-generator
```
