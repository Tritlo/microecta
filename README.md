# microecta

[![Hackage](https://img.shields.io/hackage/v/microecta.svg)](https://hackage.haskell.org/package/microecta-0.1.0.0)

`microecta` is a small equality-constrained tree automata library extracted
from the [`ecta`](https://hackage.haskell.org/package/ecta) package.

It keeps the core ECTA engine and the tiny term-search compatibility layer used
by downstream projects.

The intent is similar to the relationship between `microlens` and `lens`: keep
the useful core small, direct, and quick to build.

## Core API

The main entry point is `Data.ECTA`.

```haskell
import Data.ECTA
import Data.ECTA.Paths
import Data.ECTA.Term
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
- `nodeRepresents` checks concrete term membership.
- `nodeRepresentsTemplate` checks pruning-template membership; a template
  symbol named `<v>` acts as a wildcard.
- `getAllTerms` and `getAllTermsPrune` enumerate accepted terms.
- `sampleTerm` selects one accepted term without enumerating all complete terms.

## Sampling API

`startTermSearch` creates a persistent search value. `stepTermSearch` exposes
one ECTA edge choice at a time. A caller can retain unselected `TermBranch`
values and continue them later with `followTermBranch`.

`sampleTerm` implements bounded depth-first sampling over this interface. The
caller supplies the branch selector and its state, so `microecta` does not need
a random-number or property-testing dependency. Use `sampleTermSearch` with one
shared `TermSearch` when sampling repeatedly. Evaluated search prefixes and
their enumeration states are then reused. The sampler retries with bounded
backtracking if a selected branch cannot satisfy its constraints.
`sampleTermSearchByCount` avoids branch metadata when the selector needs only
the number of alternatives.

Sampling is weighted by local branch selections. It is not uniform over
distinct complete terms. Recursive callers should first construct a finite
automaton, for example with `unfoldBounded`, or set limits that report failure
at the required boundary.

`compileGenerationPlan` is a faster bounded-memory path for finite ECTAs. It
turns equality classes on any edge into shared value slots and constant-folds
finite domain terms. It also synchronizes overlapping slots, such as equality
on a record and equality on one field of that record. Each slot occurrence must
have the same reduced ECTA node. Recursive and empty nodes are rejected. Use
`sampleGenerationPlan` to sample the checked plan repeatedly.
`compileRootGenerationPlan` is a compatibility name for the same compiler.
If an earlier random choice cannot extend through overlapping slots, sampling
returns `GenerationPlanInconsistentSlots`. The search API remains the complete
backtracking path.

## Construction DSL

`Data.ECTA.DSL` presents ECTA construction as a symbolic generator. `choose`
draws one future value from a typed `Pool`. Reusing the returned `Value` means
that every use must receive the same term. The elaborator turns that sharing
into ECTA equality constraints.

```haskell
{-# LANGUAGE OverloadedStrings #-}

import Data.ECTA.DSL qualified as DSL

data Pair = Pair String String

data NoRefs s = NoRefs

values :: DSL.Pool String
values = DSL.elements [("A", "A"), ("B", "B")]

pairGenerator :: DSL.Generator Pair NoRefs
pairGenerator = DSL.generator $ do
  value <- DSL.choose values
  pair <- DSL.construct "Pair" $
    Pair
      <$> DSL.field "left" value
      <*> DSL.field "right" value
  pure (pair, NoRefs)

pairEcta :: Either [DSL.DslError] Node
pairEcta = DSL.elaborateGenerator pairGenerator []

decodePair :: Term -> Either String Pair
decodePair = DSL.decodeGenerated pairGenerator
```

For repeated finite sampling, `compileGenerator` retains the decoder and runs
static reduction before it compiles the generation plan. The reduction
intersects different languages contributed for one equal value. This is useful
when independent generators expose overlapping domains.

```haskell
compiledPair :: Either DSL.GeneratorCompileError (DSL.CompiledGenerator Pair)
compiledPair = DSL.compileGenerator pairGenerator []

samplePair randomState compiled =
  DSL.sampleGenerator drawIndex randomState compiled
```

The selector passed to `sampleGenerator` has the same type as the selector for
`sampleGenerationPlan`: `Int -> g -> (Int, g)`.

`Fields s` is applicative, so ordinary Haskell constructors decode the generated
term. `Pool a` carries a raw ECTA domain and its decoder. `Value s a` keeps the
symbolic identity and decoder together. `Gen s` allocates identities but does
not sample anything.

Use `reference` when an independently authored typed source must relate two
separate values. Named sources use qualified `field` names and remain useful
for policy or schema compilers that do not share Haskell values. The low-level
`schema`, `alternative`, `child`, `choice`, `recursive`, and `embedRaw`
functions remain available for direct raw ECTA construction.

## Pruning API

`getAllTermsPrune` exposes partially enumerated `TermFragment`s to pruning
oracles. `Data.ECTA` also exports `fragRepresents`, the helper used by the
original pruning path to compare those fragments against known concrete
`Term`s.

A pruning oracle receives the caller's state, the UVar being expanded, and
either:

- `Right node`, before that ECTA node is expanded
- `Left fragment`, after a `TermFragment` has been produced

Return `True` to discard the current nondeterministic branch, or `False` to
keep enumerating with the updated state.

```haskell
prunedTerms :: [Term] -> Node -> [Term]
prunedTerms forbidden =
  getAllTermsPrune () $ \() _ event ->
    case event of
      Right node ->
        pure (any (nodeRepresentsTemplate node) forbidden, ())
      Left fragment -> do
        represented <- fragRepresents True fragment forbidden
        pure (represented, ())
```

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
- small type constructors and helpers: `arrowType`, `mkDatatype`, `typeConst`,
  `genVar`, and `constFunc`

## Module Map

- `Data.ECTA` is the main ECTA API: node and edge construction, intersection,
  reduction, traversal, and enumeration.
- `Data.ECTA.DSL` builds decoded symbolic generators. Reused values and
  independently authored typed or named sources elaborate to raw ECTAs.
- `Data.ECTA.Paths` and `Data.ECTA.Term` expose the public path, equality
  constraint, symbol, and concrete term types used by `Data.ECTA`.
- `Application.TermSearch.*` is the small compatibility layer for downstream
  term-search-shaped type encodings.
- `Data.ECTA.Internal.*` contains the equality-constrained tree automata
  engine. These modules are exposed for downstream code that already relies on
  lower-level operations, but new code should start with `Data.ECTA`.
- `Data.Interned.Extended.HashTableBased`, `Data.Memoization`,
  `Data.Persistent.UnionFind`, and `Utility.*` are support modules used by the
  engine. Import them directly only when extending or debugging the internals.

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

The suite covers the current high-risk core paths:

- path lookup in term-search-shaped nodes
- equality-constraint construction and descent
- finite and recursive intersection
- recursive-path reduction
- filtered term-search reduction and enumeration

The current optimized local snapshot, using GHC 9.12.2, multiplier `1`, and
`+RTS -s -M512M -RTS`, is about 5.436 GB allocated, 4.29 MB maximum residency,
and roughly 1.1-1.2s elapsed on the maintainer machine. Treat that as a
regression guard, not a portable absolute number.

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
