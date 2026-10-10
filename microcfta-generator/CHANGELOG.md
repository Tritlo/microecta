# Changelog

## 0.1.0.0 - Unreleased

Initial release. `microcfta-generator` is one generator over the constrained
tree automata of `microcfta`, with QuickCheck integration.

- `Data.CFTA.Gen`: one generator type, `Gen symbol a`, for every kind of
  automaton. An ordinary generator is `FTAGen symbol a`, that is
  `Gen symbol a`; the equality and refinement facades fix the symbol in
  `ECTAGen` and `LTAGen`. Sources (`elements`, `leaf`,
  `namedElements`, `fromIndexed`, `fromGen`), constructors closed with
  `node`, `frequency` and `oneof`, `match` and `relate` joins, the grouped
  layer with `Sig` signatures and `apply`, recursion with `recur`, `atomic`,
  and `upToSize`, and exact inspection: `cardinality`, `values`, `unrank`,
  `termAt`, `support`, `inspect` with `drawInspection`, size counts, `pmf`,
  structural `shrinkRank`, and `smallerMembers`. A generator keeps every
  construction failure as one `GenError` with `explain`, and `orFail` fails
  with that text.
- `Data.CFTA.Gen.QuickCheck`: `toGen`, `toGenWithRank`, `forAll` with
  size-minimal counterexamples, `sized`, and the frozen pools `samplePool`
  and `freeze`. `Data.CFTA.Gen.Do`: qualified applicative do-notation for
  every theory.
- Imported automata: `fromAutomaton` reads an acyclic automaton as a finite
  generator with one rank per distinct term, counted symbolically where
  alternatives overlap or equalities reach below direct children, and a
  cyclic automaton as a recursive generator counted by size.
  `fromAutomatonUpToDepth` bounds first. `fromDatatype` and
  `fromDatatypeUpToDepth` read derived grammars of any theory.
- `Data.CFTA.Ranked`: finite ranks, weighted sampling, replay, and structural
  shrinking, independent of automata, with `Data.CFTA.Ranked.QuickCheck`.
- The engine modules `Data.CFTA.Gen.Internal.*` and the ranked internals
  `Data.CFTA.Ranked.Internal.*` are exposed for integration and stay outside
  the PVP contract.
