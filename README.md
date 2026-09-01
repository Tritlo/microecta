# microecta

This repository contains four Cabal packages:

| Package | Purpose |
| --- | --- |
| [`microecta`](microecta/README.md) | A general FTA structure plus the equality-constrained tree automata core. |
| [`microecta-generator`](microecta-generator/README.md) | Shared ranked FTA generation plus ECTA-specific combinators and QuickCheck integration. |
| [`microlta`](microlta/) | Finite liquid tree automata using Liquid Fixpoint predicates and Z3 entailment. |
| [`microlta-generator`](microlta-generator/) | Compile-once liquid generators with inspectable support, replay, and shrinking. |

`Data.Tree.FTA` is the shared ranked-transition graph. An ordinary FTA uses
`()` transition guards; `Data.ECTA.FTA` retains `EqConstraints`, and
`Data.LTA` specializes the same structure with liquid guards. Constraint
theories remain in their own modules.

`microecta-generator` depends on `microecta`; the core package does not depend
on the generator package or on QuickCheck. `Data.Tree.Gen` provides exact
finite ranks, backend-independent sampling, and shrinking, while
`Data.Tree.FTA.Gen` compiles an acyclic ordinary FTA into that representation.
`microlta-generator` checks liquid guards and pool-refinement implications once,
then reuses this pure ranked layer for every sample, replay, and shrink.

Enter `nix-shell` to put Z3 on `PATH`, then run the semantic entailment example:

```sh
cabal run liquid-pairs
```

The spike recognises finite acyclic LTAs. It does not yet implement position
substitutions, recursive LTAs, synthesis, semantic intersection, or similarity
minimisation.

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
