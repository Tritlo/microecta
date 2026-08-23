# microecta

[![Hackage](https://img.shields.io/hackage/v/microecta.svg)](https://hackage.haskell.org/package/microecta)

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
- `nodeRepresentsTemplate` checks whether a node could produce a term matching
  a template, where the symbol `<v>` is a wildcard and missing template
  children are unconstrained.
- `getAllTerms` and `getAllTermsPrune` enumerate accepted terms. Both stop at
  an unconstrained `Mu`, which appears as the marker term `Mu`; unfold with
  `unfoldBounded` first to see past the recursion.

## Pruning API

`getAllTermsPrune` lets a caller drop branches of the enumeration before they
are explored. It calls an oracle twice around every UVar, passing the caller's
own state, the UVar, and either:

- `Right node`, before that ECTA node is expanded
- `Left fragment`, after a `TermFragment` has been produced

Return `True` to discard the current nondeterministic branch, or `False` to
keep enumerating with updated state.

What makes a term worth rejecting is entirely the caller's business.
`microecta` supplies the callbacks, `expandPartialTermFrag` to read a partial
term (unexpanded holes render as `<vN>`), and `nodeRepresentsTemplate` to ask
whether an ECTA node could produce a term matching a template — and no opinion
about which shapes matter.

```haskell
-- Drop any branch whose partial term already contains a forbidden symbol.
prunedTerms :: [Symbol] -> Node -> [Term]
prunedTerms forbidden =
  getAllTermsPrune () $ \() _ event ->
    case event of
      Right _ -> pure (False, ())
      Left fragment -> do
        partial <- expandPartialTermFrag fragment
        pure (any (`occursIn` partial) forbidden, ())
  where
    occursIn s (Term s' ts) = s == s' || any (occursIn s) ts
```

A `Right node` decision covers a whole UVar, so it removes every term under
that hole at once; use `Left fragment` when the choice has to be made per
branch.

The oracle's state is threaded down each nondeterministic branch separately,
which is what makes deferred checks work. When a check cannot be settled
because the fragment still holds an unexpanded hole, park it in that state
under the hole's `getUVarRepresentative` and settle it when the oracle is
called with `Left fragment` for that UVar — which is guaranteed to happen
before the branch completes.

`getAllTermsPruneWith` adds a say in which hole is expanded next, so a parked
check can be settled before the branch it will kill is enumerated:

```haskell
-- Expand a hole some parked check is waiting on, if one is available.
resolveParkedFirst :: ExpansionOrder (IntMap [Term])
resolveParkedFirst parked candidates =
  listToMaybe [uv | uv <- candidates, uvarToInt uv `IntMap.member` parked]
```

This steers order only. It cannot make a hole expandable early, and a UVar
that is not among the candidates is ignored. For an oracle whose rejections
are monotone — once a branch can be rejected it stays rejectable — it changes
how much work is done, not which terms come out.

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

Construct ECTAs and run ECTA operations from one thread. The process-global
hash-consing and memo tables are deliberately simple and fast, but they are not
synchronized for concurrent mutation. Once a value has been constructed,
ordinary pure reads are safe; do not concurrently build nodes or force new
memoized operations.

This is not a theoretical caution, and it does not announce itself. Building
the same node from several threads on four capabilities produced two different
identities for one structurally identical node in three runs out of eight: no
exception, no crash, just two values that are structurally equal and compare
unequal. Everything downstream of that -- `Eq`, `Ord`, `Set` and `Map`
membership, memoization, `intersect` -- is then quietly wrong.

The likeliest way to hit this is a parallel test runner. `tasty` executes
independent tests concurrently by default, and `hspec` does under `parallel`.
If a property builds ECTAs, running it that way is unsafe even though nothing
in your code looks concurrent. Run such properties sequentially.

### Memory

Those tables never evict. Retained memory is proportional to the number of
*distinct* nodes, edges and symbols the process has ever constructed, and to
the memoized operations run over them. It is not proportional to the amount of
work done: repeating operations on values that already exist retains nothing
further.

Measured on the maintainer machine, holding the shape of the work fixed and
scaling only the count:

| workload | 4k iterations | 16k | 64k |
| --- | --- | --- | --- |
| intersect + reduce over a fixed symbol set | 0.1 MB | 0.1 MB | 0.1 MB |
| building fresh nodes, no memoized operations | 2.0 MB | 6.6 MB | 20.4 MB |
| both: fresh nodes, intersect + reduce | 6.6 MB | 17.2 MB | 69.8 MB |

The first row is the case to aim for. The others grow without bound, and there
is no way to release them: a long-running process that keeps building
*distinct* ECTAs will grow until it runs out of memory. This is the trade
hash-consing makes -- it is what buys O(1) equality and the memoized graph
algorithms -- but it makes `microecta` a poor fit for a long-lived service that
constructs unboundedly many unrelated automata. Batch work in a process that
exits, or keep the set of distinct nodes bounded.

#### Why there is no `clearCaches`

Two escape hatches were tried and rejected on measurement.

Emptying the memo tables while keeping the intern cache is *safe* -- every
memoized function here is pure, so dropping entries costs recomputation and
nothing else -- but it recovers almost nothing. Most of what those tables hold
is interned nodes, which the intern cache retains regardless, and the registry
needed to find the tables is itself unbounded. Clearing every 1000 iterations
of the third workload above moved live bytes by about 3%.

Emptying the intern cache is not safe at all. Identity comes from it: two
structurally equal nodes interned either side of a clear get different `Id`s
and compare unequal, silently. It would only be sound when no `Node`, `Edge` or
`Symbol` from before the clear is still reachable, which nothing can check.

The real fix is a cache that holds its entries weakly, so unreferenced nodes are
collected and the table pruned by finalisers. That is the standard treatment --
[Filliâtre and Conchon, *Type-Safe Modular Hash-Consing*
(2006)](https://usr.lmf.cnrs.fr/~jcf/publis/hash-consing2.pdf) -- and
[`hashcons`](https://hackage.haskell.org/package/hashcons) implements it for
Haskell with weak pointers and stable names. `microecta` does not do this, and
neither does the [`intern`](https://hackage.haskell.org/package/intern) package
it depends on for symbols, whose cache is also strong and monotonic. Moving to
weak caches is a design change rather than a patch, so it is not in this
release.

The old dense `PathTrie` representation compiled poorly at `-O2`, to the point of
exhausting small development machines. `microecta` uses a sparse `PathTrie` with
a compact single-child fast path. In the current benchmark suite this preserves
the important runtime shape while letting the library and benchmark build at
`-O2` inside a 512M compiler heap. CI enforces that budget so a regression fails
there rather than in a downstream build; the cap is deliberately not baked into
the library's `ghc-options`, where it would cap GHC for everyone who depends on
this package.

Run the benchmark suite with:

```sh
cabal v2-bench bench:micro-bench --enable-optimization=2 --benchmark-options='1 +RTS -s -M512M -RTS'
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
`+RTS -s -M512M -RTS`, is about 4.76 GB allocated, 4.33 MB maximum residency,
and roughly 0.85-0.88s elapsed on the maintainer machine. Treat that as a
regression guard, not a portable absolute number.

Use a larger first argument for longer runs:

```sh
cabal v2-bench bench:micro-bench --enable-optimization=2 --benchmark-options='3 +RTS -s -M512M -RTS'
```

## Build

This package is Cabal-only.

```sh
cabal v2-build microecta -j1
cabal v2-test microecta:unit-tests -j1
```

`-j1` is a suggestion, not a requirement: optimized builds of the core are
memory-hungry, and one unit of parallelism keeps a whole workspace build inside a
small machine's memory. Drop it if you have the headroom.

To reproduce the compile-time memory budget CI enforces:

```sh
cabal v2-build lib:microecta --enable-optimization=2 \
  --ghc-options='+RTS -K512M -M512M -RTS'
```
