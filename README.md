# microecta

`microecta` is a small equality-constrained tree automata library extracted
from `ecta`.

It keeps the core ECTA engine and the tiny term-search compatibility layer used
by downstream projects.

The intent is similar to the relationship between `microlens` and `lens`: keep
the useful core small, direct, and quick to build.

## Core API

The main entry point is `Data.ECTA`.

```haskell
import Data.ECTA
import Data.ECTA.Paths
```

An ECTA is a `Node`, which is a set of outgoing `Edge`s. An `Edge` has a symbol,
child nodes, and optional equality constraints over paths into those children.

```haskell
intType :: Node
intType = Node [Edge "Int" []]

maybeIntType :: Node
maybeIntType = Node [Edge "Maybe" [intType]]

sameChildren :: Edge
sameChildren =
  mkEdge
    "Pair"
    [intType, intType]
    (mkEqConstraints [[path [0], path [1]]])
```

Useful operations:

- `union` combines alternatives.
- `intersect` keeps terms accepted by both automata.
- `reducePartially` propagates equality constraints and removes impossible
  alternatives.
- `withoutRedundantEdges` removes alternatives implied by other alternatives.
- `getAllTerms` and `getAllTermsPrune` enumerate accepted terms.

For repeated reduction, downstream code usually wants:

```haskell
reduceFully :: Node -> Node
reduceFully = fixUnbounded (withoutRedundantEdges . reducePartially)
```

`Application.TermSearch.TermSearch` exports that helper directly.

## Term-Search Compatibility Layer

The `Application.TermSearch.*` modules are intentionally tiny. They provide only
the pieces that downstream projects still use:

- `TypeSkeleton`
- `typeToFta`
- `filterType`
- one-line type constructors such as `arrowType`, `mkDatatype`, `typeConst`,
  `genVar`, and `constFunc`

## Dependency Surface

The library dependency set is intentionally small:

- `containers`, `unordered-containers`
- `hashable`, `hashtables`, `intern`
- `mtl`, `transformers`
- `text`
- `equivalence`

`equivalence` is retained for equality-constraint closure in the path logic.

## Performance Notes

The core still uses the original hash-consing, memoization, union-find,
recursive-node, and path/equality-constraint machinery. Those are the hard parts
of ECTA and are intentionally kept.

The old dense `PathTrie` representation compiled poorly at `-O2` under a
512M compiler memory cap. `microecta` uses a sparse `PathTrie` with a compact
single-child fast path. In the current benchmark suite this preserves the
important runtime shape while allowing the library and benchmark to build at
`-O2` with the baked 512M cap.

Run the benchmark suite with:

```sh
cabal v2-bench bench:micro-bench --enable-optimization=2 --ghc-options=-O2 --benchmark-options='1 +RTS -s -M512M -RTS'
```

The benchmark harness is deliberately dependency-light and prints CSV:

```text
benchmark,cpu_seconds,repeats,checksum
```

The current optimized local snapshot, using GHC 9.12.2, multiplier `1`, and
`+RTS -s -M512M -RTS`, is about 1.11s elapsed, 5.49 GB allocated, and 4.27 MB
maximum residency. Treat that as a regression guard, not a portable absolute
number.

Use a larger first argument for longer runs:

```sh
cabal v2-bench bench:micro-bench --enable-optimization=2 --ghc-options=-O2 --benchmark-options='3 +RTS -s -M512M -RTS'
```

## Build

This package is Cabal-only.

```sh
cabal v2-build all -j1
cabal v2-test unit-tests -j1
```

The library has compiler RTS options baked in:

```text
+RTS -K512M -M512M -RTS
```

That cap is intentional: it catches compile-time memory regressions before they
kill small development environments.
