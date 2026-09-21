# Changelog

## 0.1.0.0 - Unreleased

Initial release. `microcfta-generator` consolidates the ordinary, equality,
and refinement generators into one package over `microcfta`.

- `Data.CFTA.Ranked`: finite ranks, weighted sampling, replay, and structural
  shrinking, independent of automata, with QuickCheck integration in
  `Data.CFTA.Ranked.QuickCheck`.
- `Data.CFTA.Gen`: compilation of acyclic ordinary automata, depth and size
  bounds for recursive ones, derived datatypes with retained decoders, and the
  `FTA.node`/`FTA.do` construction syntax.
- `Data.CFTA.Gen.Equality`: equality-constrained sources, `match` and
  `relate` joins, retained key groups with `Sig` signatures, recursive
  languages with size-major ranks, generator inspection, and size-minimal
  counterexamples in `forAll`. The engine underneath is generic in the symbol
  type; `support` and `termAt` return graphs and terms over
  `Data.CFTA.Gen.Label`, which wraps user symbols in `Label` and types the
  engine's private labels as constructors instead of reserving symbol names.
- `Data.CFTA.Gen.Refinement`: refinement-constrained sources compiled once
  with a solver into pure sampling, replay, and shrinking; imported LTAs;
  frozen native pools; semantic pool shrinking; and bounded generation from
  recursive LTAs.
- The former `internal` sublibraries are exposed modules of the one library:
  `Data.CFTA.Ranked.Internal.*`, `Data.CFTA.Gen.Internal.*`, and
  `Data.CFTA.Gen.Equality.Internal.Symbolic`. They remain outside the PVP
  contract.
- The package has three test suites, `plain-tests`, `equality-tests`, and
  `refinement-tests`, and one copy of the generator benchmark harness.
- The three layers share one vocabulary. `Data.CFTA.Gen.Error` holds the one
  `GenError` and its `explain`; a construction failure lives inside the
  generator value, so `frequency`, `oneof`, and the imports return the
  generator and the observers return `Either GenError`. Every layer imports
  its own interned automaton with `fromAutomaton`, `fromAutomatonUpToDepth`,
  and `fromAutomatonUpToSize`, returns an interned node from `support`, and
  has `shrinkRank` and `smallerMembers`. One `Data.CFTA.Gen.Do` serves every
  layer's qualified do-blocks.
- `ECTAGen a` has no backend parameter: an opaque source is a QuickCheck
  generator, and `Data.CFTA.Gen.Equality.QuickCheck` keeps only what is
  QuickCheck-specific. `lowerVia` lowers a transparent generator through any
  sampling backend for exact distributions.
- The refinement compiler takes the core's interned LTA. A pruned automaton
  without constraints is counted as an ordinary automaton on its explicit
  view and everything else symbolically, so `CompiledSupport` has one
  automaton constructor and `ResidualGuard` reports a guard the symbolic
  counter cannot interpret.
