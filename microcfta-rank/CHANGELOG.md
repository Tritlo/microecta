# Changelog

## 0.1.0.0 - Unreleased

Initial release. `Data.CFTA.Ranked` and `Data.CFTA.Ranked.Internal.*`, moved
out of `microcfta-generator`: ranked languages with exact cardinalities, a
bijection between ranks and members, sizes that count pays, weighted
samplers, and structural shrinking. The test suite that was
`Data.CFTA.RankedSpec` of the generator states their contract. The QuickCheck
backend, `Data.CFTA.Ranked.QuickCheck`, stays in `microcfta-generator`.
