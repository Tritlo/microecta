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
  counterexamples in `forAll`.
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
