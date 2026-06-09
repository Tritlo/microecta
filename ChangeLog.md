# Changelog for microecta

## Unreleased changes

- Extracted the small ECTA core and term-search compatibility layer into a
  Cabal-only package.
- Added sparse path tries, a dependency-light benchmark harness, and baked
  compile-time RTS caps so optimized builds stay inside the 512M target.
- Documented the main API, pruning callbacks, module map, dependency surface,
  and benchmark baseline.
