# microfta-generator

`microfta-generator` provides ranked generation and the ordinary FTA adapter.
It depends on `microfta`. It has no ECTA, LTA, or solver dependency.

| Module | Purpose |
| --- | --- |
| `Data.Tree.Gen` | Finite ranks, weighted sampling, replay, and structural shrinking. |
| `Data.Tree.Gen.QuickCheck` | QuickCheck sampling and properties over a ranked language. |
| `Data.Tree.FTA.Gen` | Ordinary FTA compilation and constructor-based source recipes. |
| `Data.Tree.FTA.Gen.QuickCheck` | FTA sampling, properties, and qualified do-notation. |
| `Data.Tree.Gen.Internal.*` | Shared decoder, sampler, size, and shrink implementation, in the public `internal` sublibrary used by the constrained adapters. |

Run the complete example from the workspace root:

```sh
cabal run fta-pairs
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
checks before using the shared index.

`Data.Tree.Gen` is independent of automaton representation. `Indexed` describes
a finite rank domain. `WeightedIndexed` separates replay ranks from sampling
tickets. Its callbacks must obey the documented rank and weight invariants.
Counting and replay do not require enumerating the entire source.

The `Internal` modules live in the public `internal` sublibrary. They are an
integration interface for constrained adapters, which depend on
`microfta-generator:{microfta-generator, internal}`. Their exports are not
covered by the PVP contract of the main library. Ordinary applications should
use the public construction modules.

`fromDatatypeUpToDepth` and `fromDatatypeUpToSize` combine a derived grammar
with its retained decoder. They return ordinary `FTAGen` values. Replay keeps
the constructor term and the typed value at the same rank. Decoding a selected
value does not enumerate any other member. Depth counts constructors, including
primitive fields: a `Leaf Bool` term has depth one and two tree nodes.

Build and test from the workspace root:

```sh
cabal test microfta-generator:unit-tests
```
