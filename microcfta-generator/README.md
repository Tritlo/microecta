# microcfta-generator

Ranked generation, random sampling, replay, and shrinking for the automata of
[`microcfta`](../microcfta/README.md), with QuickCheck integration. There is
one generator type, `Gen symbol constraint a`, and one facade per constraint
theory:

| Module | Purpose |
| --- | --- |
| `Data.CFTA.Gen` | The generator: sources, constructors, choices, joins, recursion, imported automata and datatypes, exact inspection, replay, and shrinking, for every theory. |
| `Data.CFTA.Gen.QuickCheck` | Sampling and properties over a generator, and frozen pools. |
| `Data.CFTA.Gen.Do` | Qualified applicative do-notation, re-exported by the three `QuickCheck` facades; `FTAGen.do`, `ECTAGen.do`, and `LTAGen.do` are this module under the facade's alias. |
| `Data.CFTA.Gen.Error` | The one failure vocabulary, and `explain`. |
| `Data.CFTA.Ranked`, `Data.CFTA.Ranked.QuickCheck` | Finite ranks, weighted sampling, replay, and structural shrinking, independent of automata. |
| `Data.CFTA.Gen.Internal.*`, `Data.CFTA.Ranked.Internal.*` | The engine: static and recursive languages, joins, symbolic counting, decoders, samplers, sizes, and shrinking; exposed for integration, not covered by the PVP contract. |

## Ordinary generators

Run the complete example from the workspace root:

```sh
nix-shell --run 'cabal run cfta-pairs'
```

[`examples/FinitePairs.hs`](examples/FinitePairs.hs) derives the pair datatype with the finite `Int`
domain `[0, 1]`.
It checks all replay ranks and samples the accepted pairs with QuickCheck.
It also constructs the same language as an interned `Common.PlainNode String`,
imports it with `fromAutomaton`, and checks the imported generator.

`FTAGen.node "pair"` closes an applicative child block with one constructor.
Each binding supplies one direct child. Enable `ApplicativeDo` and
`QualifiedDo`, and finish the block with `FTAGen.pure`. Child generators must be
independent. `leaf value symbol` is a constructor without children, and
`oneof` and `frequency` choose between generators; an empty alternative is
skipped, not an error.

`fromAutomaton` reads an interned automaton as a generator of the terms it
accepts. An acyclic automaton gives a finite generator with one rank per
distinct term: where alternatives overlap or an equality reaches below
direct children, the count is symbolic, and ranks order constructors by the
symbol's `Ord`. A cyclic automaton gives a recursive generator counted by
size, the number of term nodes; it must be unambiguous, because its count
sums over accepting runs. `fromAutomatonUpToDepth` bounds the automaton by
constructor depth first, a leaf having depth zero, and `upToSize` bounds any
generator to the members of at most a given number of source choices, in
size-major rank order. Use `Data.CFTA.Interned.fromFTA` first when the source
is an explicit-state automaton; the import is total and retains shared states.

`fromDatatype` reads a derived grammar as a generator of its values,
recursive when the datatype is, and `fromDatatypeUpToDepth` bounds it by
constructor depth. The value and its constructor term share one rank, and
the codec runs only when a selected value is demanded. Depth counts
constructors, including primitive fields: a `Leaf Bool` term has depth one
and two tree nodes.

`Data.CFTA.Ranked` is independent of automaton representation. `Indexed`
describes a finite rank domain, and `fromIndexed` is the generator over it.
Counting and replay do not require enumerating the entire source.

### Generate a language up to a depth bound

This complete example derives a grammar with `microcfta`, then generates every
expression with literals `0` and `1` up to constructor-tree depth 3:

```haskell
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import GHC.Generics (Generic)

import qualified Data.CFTA.Gen as FTAGen
import Data.CFTA.Generic (HasFTA, deriveFTAWith, domain)

-- | Arithmetic expressions with integer literals.
data Expr = Lit Int | Add Expr Expr
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | Print every expression in a depth-bounded language.
main :: IO ()
main = do
    datatype <- either (fail . show) pure $ deriveFTAWith @Expr (domain @Int [0, 1])
    let language = FTAGen.fromDatatypeUpToDepth 3 datatype
    total <- either (fail . FTAGen.explain) pure $ FTAGen.cardinality language
    mapM_ (either (fail . FTAGen.explain) print . FTAGen.unrank language) [0 .. total - 1]
```

Add both `microcfta` and `microcfta-generator` to your component's
`build-depends`. In this checkout, save the program as `Main.hs` at the
workspace root and run:

```sh
cabal build microcfta-generator
cabal exec -- ghc -package microcfta -package microcfta-generator -e main Main.hs
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

As in the `microcfta` README, the bound includes the `Int` child of `Lit`.
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
ranks identify distinct terms; an ambiguous handwritten grammar is counted
symbolically, so one term still has one rank.

For another complete example, see
[`FinitePairs.hs`](examples/FinitePairs.hs), or run
`cabal run cfta-pairs` from the workspace root.
