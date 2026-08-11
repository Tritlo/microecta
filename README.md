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

## Indexed generator adapter

`Data.ECTA.Gen` turns a finite indexed source into an ECTA whose leaves contain
stable indices, not generated values. `Functor` and `Applicative` composition
preserve that symbolic structure, so ordinary `ApplicativeDo` builds ECTA
products. Alongside the ECTA, the generator tracks an exact cardinality and a
rank-to-outcome selector; applicative products multiply their counts rather
than materializing their Cartesian products.

`match` generates two values under a reified key equality: in
`match (authenticatedUser :==: fileOwner) authentication filesystem`, the
`:==:` keeps both projections as data, so the match can group each input by
its own key, encode the shared keys as an actual ECTA equality constraint,
count the matching group products, and unrank directly into the selected
group. `:&&:` conjoins several equalities. `match` accepts arbitrary value
projections, so discovering its groups requires enumerating the input ranks;
conditioning three or more generators is the keyed layer's job (`elementsBy`
and `apply`).

`ECTAGenBy key a` is the explicit grouping-preserving path for nested or very
large languages. The `key` is the type returned by the classifier and used to
decide which groups may be joined; it is not part of the generated `a`. Matching
key values receive equal internal labels on constrained ECTA paths. `elementsBy`
records those initial keys, and grouped generators support ordinary `fmap`.
`regroupBy` changes the classification without enumerating values, `sizeBy`
returns the stored cardinality of every group, and `atKey` selects one group as
an ordinary conditional generator. An operation of any arity is classified by
a `Sig`, a heterogeneous list of argument keys plus a result key, e.g.
`leftKey :* rightKey :* KNil :-> resultKey`. `apply` matches each signature
key with the corresponding argument family, equates their paths in one ECTA
edge holding one equality constraint per argument, and retains the result key
for later equality constraints. The operation family holds functions (`fmap`
a compiling function onto it); the argument families arrive as an `Args`
chain. `ungroup` returns an ordinary `ECTAGen` with
the same exact distribution. Stable source order and ascending key order give
deterministic replay ranks.

```haskell
functionsBySignature :: ECTAGenBy (Sig '[Type, Type] Type) BinaryFunctionInstance
functionsBySignature = ECTAGen.elementsBy signature functionInstances

signature function =
  argument1Type function :* argument2Type function :* KNil :-> resultType function

atomsByType :: ECTAGenBy Type TypedExpression
atomsByType = ECTAGen.elementsBy expressionType atoms

applicationGen children =
  ECTAGen.apply (compile <$> functionsBySignature) (children :& children :& ANil)

depthFour = applicationGen depthThree
```

Both layers also support qualified do-notation through `Data.ECTA.Gen.Do`,
which `Data.ECTA.Gen.QuickCheck` re-exports. Enable `QualifiedDo` together
with `ApplicativeDo`; statements must stay independent, and the final
statement must use the qualified `ECTAGen.pure`. A grouped block chooses the
operation family first and then one argument per signature component in
order; whatever the arity, it builds exactly one `apply` join:

```haskell
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE QualifiedDo #-}

authentication :: ECTAGen Authentication
authentication = ECTAGen.do
  user <- generatedUser
  method <- ECTAGen.elements [Password, Token]
  ECTAGen.pure (Authentication user method)

applicationGen children = ECTAGen.do
  op <- functionsBySignature
  x <- children
  y <- children
  ECTAGen.pure (compile op x y)
```

Impossible shapes fail at compile time with an explanation: a statement using
an earlier bound value, an unqualified `pure` ending, a missing operation
argument, or a fallible pattern.

Every transparent generator samples compositionally by rank, including exact
non-uniform `frequency` and conditioned joins; sampling never materializes the
final Cartesian product. `cardinality` and `unrank` expose deterministic replay,
while `countBy` reports exact coverage of ranked outcomes. Both `countBy` and
`pmf` enumerate every rank because their projections or complete result values
are not retained groups. The `ECTAGenBy` path avoids that work when a caller
supplies the reusable classification structure up front.
The optional `microecta:quickcheck` sublibrary exposes `toGen`, plus
`toGenWithRank` when the sampled replay rank is needed.

```haskell
import Data.ECTA.Gen.QuickCheck (ECTAGen)
import Data.ECTA.Gen.QuickCheck qualified as ECTAGen

joined :: ECTAGen (Authentication, Filesystem)
joined =
  ECTAGen.match
    (authenticatedUser :==: fileOwner)
    authentication
    filesystem
```

```haskell
replay :: Either ECTAGenError Authentication
replay = ECTAGen.unrank authentication 42

coverage :: Either ECTAGenError (Map UserId Integer)
coverage = ECTAGen.countBy authenticatedUser authentication
```

`fromIndexed` is the transparent boundary for a FEAT-style finite enumeration:
it needs only a cardinality and a stable function from an integer index to a
value. `elements` is the corresponding list convenience function.

`fromGen` embeds an ordinary `QuickCheck.Gen` as an explicitly opaque region.
Opaque regions still compose and sample, but cannot be inspected with `pmf`;
joining through one falls back to QuickCheck rejection. Opaque regions also
have no replay rank. There is deliberately no `Monad` or `Selective` instance.
This keeps inspectable applicative regions inside ECTA and makes the loss of
structure explicit.

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
- `Data.ECTA.Gen` is the indexed, applicative ECTA generator core.
- `Data.ECTA.Gen.QuickCheck` adds the opaque `fromGen` boundary and samples
  generators through the optional `microecta:quickcheck` sublibrary.
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
The optional `microecta:quickcheck` sublibrary adds `QuickCheck`.

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
