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

An ECTA is a `Node symbol`, which is a set of outgoing `Edge symbol`s. An edge
has a symbol, child nodes, and optional equality constraints over paths into
those children. `Symbol` is the supplied interned text alphabet; its `IsString`
instance keeps the usual `OverloadedStrings` syntax.

```haskell
intType :: Node Symbol
intType = Node [Edge "Int" []]

maybeIntType :: Node Symbol
maybeIntType = Node [Edge "Maybe" [intType]]

sameChildren :: Edge Symbol
sameChildren =
  mkEdge
    "Pair"
    [intType, intType]
    (mkEqConstraints [[path [0], path [1]]])
```

The alphabet can instead be an ordinary datatype. Edge construction needs
`Hashable` and `Typeable` for type-safe hash-consing; building a node from
existing edges needs only `Typeable`, and inspecting an existing node needs
neither. Operations that rebuild edges, such as intersection and reduction,
therefore carry both constraints. `getAllTermsWith` takes the value to use when
recursion is truncated, so the datatype does not need an `IsString` instance:

```haskell
import Data.Hashable (Hashable)
import GHC.Generics (Generic)

data NatSymbol = Zero | Succ | Recursion
  deriving (Eq, Generic, Show)

instance Hashable NatSymbol

zeroOrOne :: Node NatSymbol
zeroOrOne = Node [Edge Zero [], Edge Succ [Node [Edge Zero []]]]

terms :: [Term NatSymbol]
terms = getAllTermsWith Recursion zeroOrOne
```

Useful operations:

- `union` combines alternatives.
- `intersect` keeps terms accepted by both automata.
- `reducePartially` propagates equality constraints and removes impossible
  alternatives.
- `withoutRedundantEdges` removes alternatives implied by other alternatives.
- `nodeRepresents` checks concrete term membership.
- `matchesTemplate` checks a concrete term against an explicit `Template`.
- `termsMatching` restricts a node to the accepted terms matching a template,
  while preserving its equality constraints.
- `getAllTerms` and `getAllTermsPrune` enumerate accepted terms. Both stop at
  an unconstrained `Mu`, which appears as the marker term `Mu`; unfold with
  `unfoldBounded` first to see past the recursion.

Templates do not overload ordinary symbols. `Hole` matches a complete
subtree, `TemplateNode` and `AnyNode` require exact arity, and
`TemplatePrefix` and `AnyPrefix` constrain only the leading children:

```haskell
unaryF = TemplateNode "f" [Hole] :: Template Symbol
anyF = TemplatePrefix "f" [] :: Template Symbol
```

## Pruning API

`getAllTermsPrune` lets a caller drop branches of the enumeration before they
are explored. It calls an oracle twice around every UVar it expands, passing
the caller's own state, the UVar, and either:

- `Right node`, before that ECTA node is expanded
- `Left fragment`, after a `TermFragment` has been produced

A bare unconstrained `Mu` stops enumeration without being expanded and
therefore produces neither callback.

Return `True` to discard the current nondeterministic branch, or `False` to
keep enumerating with updated state.

What makes a term worth rejecting is entirely the caller's business.
`microecta` supplies the callbacks, `expandPartialTermFrag` to read a partial
term, and no opinion about which shapes matter. Its `PartialSymbol` alphabet
keeps concrete symbols, unexpanded `UVarHole`s, and `TruncatedRecursion`
distinct; no placeholder can collide with a real symbol. `Term` is a functor,
so a caller that deliberately wants one concrete alphabet can materialize a
partial term with `fmap resolvePartial`.

```haskell
-- Drop any branch whose partial term already contains a forbidden symbol.
prunedTerms :: [Symbol] -> Node Symbol -> [Term Symbol]
prunedTerms forbidden =
  getAllTermsPrune () $ \() _ event ->
    case event of
      Right _ -> pure (False, ())
      Left fragment -> do
        partial <- expandPartialTermFrag fragment
        pure (any (`occursIn` partial) forbidden, ())
  where
    occursIn s (Term (ConcreteSymbol s') ts) =
      s == s' || any (occursIn s) ts
    occursIn s (Term _ ts) = any (occursIn s) ts
```

A `Right node` decision covers a whole UVar, so it removes every term under
that hole at once. The fact that `termsMatching template node` is non-empty
only proves that some terms match; it does not justify dropping the whole
node. Use `Left fragment` when the choice has to be made per branch.

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
reduceFully :: Node Symbol -> Node Symbol
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

Building ECTAs is safe from any thread. The hash-consing and memoization
tables are immutable maps in `IORef`s: reads never block, and atomic updates
retain the winning interned value, so one structure keeps one identity however
many threads raced for it.

It was not always so. Before 0.2.0.0 the tables were mutable and unsynchronized,
and building one structurally identical node from several threads on four
capabilities produced two different identities in 16 runs out of 20 -- no
exception, no crash, just two values that are structurally equal and compare
unequal, after which `Eq`, `Ord`, `Set` membership, memoization and `intersect`
were all quietly wrong. That mattered most for a parallel test runner: `tasty`
runs independent tests concurrently by default and `hspec` does under
`parallel`, so a property could be run that way without anything in the user's
code looking concurrent. The same probe now reports no disagreement in 25 runs.

Recursive-node shapes are computed before entering the interning cache and
stored in the uninterned description. Hashing and equality reuse that shape,
while the candidate value remains lazy during the atomic update; forcing it
there could build and intern further nodes.

The replacement is not a novel design. The `intern` package, already a
dependency here for interned text, has kept its caches as immutable maps in
`IORef`s updated atomically for years. It also shards them 1024 ways
to cut write contention, which this does not yet do; if a workload ever turns
out to be write-bound across many threads, that is the next step.

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
| building fresh nodes, no memoized operations | 1.9 MB | 6.2 MB | 27.2 MB |
| both: fresh nodes, intersect + reduce | 5.3 MB | 30.5 MB | 105.8 MB |

Those last two rows are roughly half again what the pre-0.2.0.0 mutable tables
retained, which is what the immutable maps cost: a HAMT node carries more
overhead per entry than a slot in a flat mutable table. It buys thread safety
and, on the core benchmark, less of everything else: 0.77s and 4,765 MB before
0.2.0.0 against 0.30s and 2,161 MB now. Holding the cache fixed and adding only
the stored shape accounts for 0.69s and 4,317 MB of that, so the swap away from
the mutable table is the larger half. The tables are read far more often than
written, and a pure lookup in a HAMT beats an IO-boxed probe into a cuckoo
table.

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

### Limits

Measured by scaling one dimension at a time until it stopped being practical,
on the maintainer machine with a 20-second budget per point.

Two things have a ceiling worth knowing about.

**Enumerating an unfolded recursive automaton.** For a three-edge recursive
type, `getAllTerms (unfoldBounded k t)` gives 677 terms at `k = 5` in a
millisecond, 458,330 at `k = 6` in a second, and does not finish `k = 7` in
twenty. The language grows faster than exponentially in the unfolding depth, so
this is the shape of the problem rather than a defect: reach for
`countAtSize` and `unrank` from `microecta-generator` when you want to work
with a large language without materializing it.

**Equality constraints whose paths nest.** Congruence saturation in
`mkEqConstraints` is quadratic per round and iterates to a fixpoint, so classes
that pair paths which are prefixes of one another cost about 4.7x per level
added: 0.14s at depth 8, 0.77s at 9, 3.4s at 10, 16.4s at 11.

The cost is in the nesting, not the count. A thousand independent classes over
depth-two paths -- the shape term search and `apply` actually produce -- take
0.04s, and both use depth two with a handful of classes. If you are building
constraints by hand and they nest more than about ten deep, that is the wall.

Everything else measured flat over the range tried: intersecting two recursive
types up to ten branches each, intersecting two 12,800-edge finite nodes,
2,560 disjoint constraint classes, reducing a 64-link constrained chain, and
counting or unranking a bounded recursive generator.

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
`+RTS -s -M512M -RTS`, is about 2.16 GB allocated, 4.34 MB maximum residency,
and roughly 0.30s elapsed on the maintainer machine. Treat that as a
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
