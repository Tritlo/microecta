# microfta-generator

`microfta-generator` provides ranked generation and the ordinary FTA adapter.
It depends on `microfta`. It has no ECTA, LTA, or solver dependency.

| Module | Purpose |
| --- | --- |
| `Data.Ranked` | Finite ranks, weighted sampling, replay, and structural shrinking. |
| `Data.Ranked.QuickCheck` | QuickCheck sampling and properties over a ranked language. |
| `Data.Tree.FTA.Gen` | Ordinary FTA compilation and constructor-based source recipes. |
| `Data.Tree.FTA.Gen.QuickCheck` | FTA sampling, properties, and qualified do-notation. |
| `Data.Ranked.Internal.*` | Shared decoder, sampler, size, and shrink implementation, in the public `internal` sublibrary used by the constrained adapters. |

Run the complete example from the workspace root:

```sh
nix-shell --run 'cabal run fta-pairs'
```

`examples/FinitePairs.hs` derives the pair datatype with the finite `Int`
domain `[0, 1]`.
It checks all replay ranks and samples the accepted pairs with QuickCheck.
It also constructs the same language with `Common.Node String ()`, converts
the shared graph with `Common.toFTA`, and checks the imported generator.

`FTA.node "pair"` closes an applicative child block. Each binding supplies one
direct child. Enable `ApplicativeDo` and `QualifiedDo`, and finish the block
with `FTA.pure`. Child generators must be independent.

`fromFTA` compiles an ordinary acyclic FTA. Its ranks identify accepting
derivations. An ambiguous automaton can assign several ranks to the same term.
Transition alternatives have equal branch weights; this does not guarantee
equal probability for every complete term.
Use `Data.Tree.FTA.Interned.toFTA` first when the source is an interned graph.
That view retains shared states. It does not enumerate the term language.

`fromFTAUpToDepth` also accepts recursive automata. A leaf has depth zero.
The compiler bounds the shared graph and preserves transition and child order.
`fromFTAUpToSize` bounds the total number of tree nodes. Its ranks are ordered
by size, and it samples uniformly over those ranks. Both imports count accepting
runs. An empty bounded language returns `EmptyFTALanguage`.

Recursive size indexing and finite automaton rank shrinking belong to
`Data.Tree.FTA.Gen.Internal.*`. ECTA retains its constraint and ambiguity
checks before using the shared index. LTA uses the ordinary shrinker only
after it has removed transition constraints.

`Data.Ranked` is independent of automaton representation. `Indexed` describes
a finite rank domain. `WeightedIndexed` separates replay ranks from sampling
tickets. Its callbacks must obey the documented rank and weight invariants.
Counting and replay do not require enumerating the entire source.

The `Internal` modules live in the public `internal` sublibrary. They are an
integration interface for the ECTA and LTA adapters, which depend on
`microfta-generator:{microfta-generator, internal}`. Their exports are not
covered by the PVP contract of the main library. Ordinary applications should
use the public construction modules.

`fromDatatypeUpToDepth` and `fromDatatypeUpToSize` combine a derived grammar
with its retained decoder. They return ordinary `FTAGen` values. Replay keeps
the constructor term and the typed value at the same rank. Decoding a selected
value does not enumerate any other member. Depth counts constructors, including
primitive fields: a `Leaf Bool` term has depth one and two tree nodes.

Build, test, and benchmark from the workspace root:

```sh
nix-shell
cabal test microfta-generator:unit-tests
cabal bench microfta-generator:untyped-expression-speed --enable-optimization=2
```

Code that previously imported `Data.Ranked` or `Data.Tree.FTA.Gen` through
`microecta-generator` must now declare `microfta-generator` in `build-depends`.
The module names and rank/sampling contracts are unchanged.

## Generate a language up to a depth bound

This complete example derives a grammar with `microfta`, then generates every
expression with literals `0` and `1` up to constructor-tree depth 3:

```haskell
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import GHC.Generics (Generic)

import qualified Data.Tree.FTA.Gen as Gen
import Data.Tree.FTA.Generic (HasFTA, deriveFTAWith, domain)

-- | Arithmetic expressions with integer literals.
data Expr = Lit Int | Add Expr Expr
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | Print every expression in a depth-bounded language.
main :: IO ()
main = do
    datatype <- either (fail . show) pure $ deriveFTAWith @Expr (domain @Int [0, 1])
    language <- either (fail . show) pure $ Gen.fromDatatypeUpToDepth 3 datatype
    mapM_ (either (fail . show) print . Gen.unrank language) [0 .. Gen.cardinality language - 1]
```

Add both `microfta` and `microfta-generator` to your component's
`build-depends`. In this checkout, save the program as `Main.hs` at the
workspace root and run:

```sh
cabal build microfta-generator
cabal exec -- runghc -package=microfta -package=microfta-generator Main.hs
```

The output is:

```text
Lit 0
Lit 1
Add (Lit 0) (Lit 0)
Add (Lit 0) (Lit 1)
Add (Lit 0) (Add (Lit 0) (Lit 0))
Add (Lit 0) (Add (Lit 0) (Lit 1))
Add (Lit 0) (Add (Lit 1) (Lit 0))
Add (Lit 0) (Add (Lit 1) (Lit 1))
Add (Lit 1) (Lit 0)
Add (Lit 1) (Lit 1)
Add (Lit 1) (Add (Lit 0) (Lit 0))
Add (Lit 1) (Add (Lit 0) (Lit 1))
Add (Lit 1) (Add (Lit 1) (Lit 0))
Add (Lit 1) (Add (Lit 1) (Lit 1))
Add (Add (Lit 0) (Lit 0)) (Lit 0)
Add (Add (Lit 0) (Lit 0)) (Lit 1)
Add (Add (Lit 0) (Lit 0)) (Add (Lit 0) (Lit 0))
Add (Add (Lit 0) (Lit 0)) (Add (Lit 0) (Lit 1))
Add (Add (Lit 0) (Lit 0)) (Add (Lit 1) (Lit 0))
Add (Add (Lit 0) (Lit 0)) (Add (Lit 1) (Lit 1))
Add (Add (Lit 0) (Lit 1)) (Lit 0)
Add (Add (Lit 0) (Lit 1)) (Lit 1)
Add (Add (Lit 0) (Lit 1)) (Add (Lit 0) (Lit 0))
Add (Add (Lit 0) (Lit 1)) (Add (Lit 0) (Lit 1))
Add (Add (Lit 0) (Lit 1)) (Add (Lit 1) (Lit 0))
Add (Add (Lit 0) (Lit 1)) (Add (Lit 1) (Lit 1))
Add (Add (Lit 1) (Lit 0)) (Lit 0)
Add (Add (Lit 1) (Lit 0)) (Lit 1)
Add (Add (Lit 1) (Lit 0)) (Add (Lit 0) (Lit 0))
Add (Add (Lit 1) (Lit 0)) (Add (Lit 0) (Lit 1))
Add (Add (Lit 1) (Lit 0)) (Add (Lit 1) (Lit 0))
Add (Add (Lit 1) (Lit 0)) (Add (Lit 1) (Lit 1))
Add (Add (Lit 1) (Lit 1)) (Lit 0)
Add (Add (Lit 1) (Lit 1)) (Lit 1)
Add (Add (Lit 1) (Lit 1)) (Add (Lit 0) (Lit 0))
Add (Add (Lit 1) (Lit 1)) (Add (Lit 0) (Lit 1))
Add (Add (Lit 1) (Lit 1)) (Add (Lit 1) (Lit 0))
Add (Add (Lit 1) (Lit 1)) (Add (Lit 1) (Lit 1))
```

`fromDatatypeUpToDepth` compiles the bounded grammar and retains the decoder
for `Expr`. `cardinality` gives the number of replay ranks. `unrank` constructs
the member at a zero-based rank. The example prints all 38 expressions in
rank order. It handles replay errors before printing each `Expr` value.

As in the `microfta` README, the bound includes the `Int` child of `Lit`.
`Lit 0` has depth one. An `Add` of two literals has depth two. At depth three,
either child of the outer `Add` can itself be an `Add`.

Change `fromDatatypeUpToDepth 3` to `fromDatatypeUpToDepth 4` to generate a
larger language:

| Maximum depth | Number of expressions |
| --- | ---: |
| 2 | 6 |
| 3 | 38 |
| 4 | 1,446 |

Each next depth permits the two literals and every ordered pair of expressions
from the previous depth: `2 + n * n` choices. The rank decoder constructs the
selected values from the compiled grammar.

The QuickCheck adapter adds random sampling and shrinking. Counts and replay
ranks identify accepting derivations; an ambiguous handwritten grammar can
give one term several ranks. This derived expression grammar is unambiguous.

For another complete example, see
[`FinitePairs.hs`](examples/FinitePairs.hs), or run
`cabal run fta-pairs` from the workspace root.
