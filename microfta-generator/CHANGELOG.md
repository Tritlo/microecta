# Changelog

## 0.1.0.0 - Unreleased

Initial release.

- `Data.Ranked`: backend-independent finite ranked generators with exact
  cardinalities, stable replay ranks, weighted sampling, and structural
  shrinking that never proposes a larger member.
- `Data.Tree.FTA.Gen` and `Data.Tree.FTA.Gen.Do`: compile an acyclic ordinary
  FTA, or bound a cyclic one by depth or size, into a ranked generator; build
  generators from derived datatype grammars with `fromDatatypeUpToDepth` and
  `fromDatatypeUpToSize`.
- `Data.Ranked.QuickCheck` and `Data.Tree.FTA.Gen.QuickCheck`: sampling,
  replay, and shrinking through QuickCheck.
- The `internal` sublibrary holds the decoder, sampler, size index, and shrink
  implementation that `microecta-generator` and `microlta-generator` build on.
  Its modules are not covered by the PVP contract of the main library.
