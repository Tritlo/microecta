# microecta

This repository contains four Cabal packages:

| Package | Purpose |
| --- | --- |
| [`microecta`](microecta/README.md) | A general FTA structure plus the equality-constrained tree automata core. |
| [`microecta-generator`](microecta-generator/README.md) | Shared ranked FTA generation plus ECTA-specific combinators and QuickCheck integration. |
| [`microlta`](microlta/) | Liquid tree automata using Liquid Fixpoint predicates and Z3 entailment. |
| [`microlta-generator`](microlta-generator/) | Compile-once liquid generators with pruning, replay, semantic shrinking, and bounded recursion. |

`Data.Tree.FTA` is the shared ranked-transition graph. `Data.Tree.FTA.Syntax`
constructs ordinary or annotated FTAs with `row`, `transition`, and `guarded`.
`Data.ECTA.FTA` retains `EqConstraints`, while `Data.LTA` adds refinement-labelled
transitions and liquid guards. Constraint theories remain in their own modules.

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

`microlta` implements refinement-labelled recognition, Boolean guards,
actual-for-formal position substitutions, semantic intersection, similarity
comparison, and recursive LTAs with the paper's acyclic-guard restriction.
`microlta-generator` adds named guard syntax, finite or frozen QuickCheck pools,
semantic pruning and shrinking, opt-in similarity minimisation, and explicitly
bounded generation from recursive LTAs. It is an automata and generator library,
not the Hegel component-based synthesizer from the paper.

See [`docs/automata-syntax.md`](docs/automata-syntax.md) for the side-by-side
FTA, ECTA, and LTA construction forms and the rationale for the guard-lambda
syntax.

Build and test the whole workspace from the repository root:

```sh
cabal build all -j1
cabal test all -j1
```

The examples in the public entry-point modules are executable. Run them with
[`doctest`](https://hackage.haskell.org/package/doctest):

```sh
cabal install doctest
cabal repl --with-repl=doctest lib:microecta
cabal repl --with-repl=doctest lib:microecta-generator
cabal repl --with-repl=doctest lib:microlta
cabal repl --with-repl=doctest lib:microlta-generator
```
