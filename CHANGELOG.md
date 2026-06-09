# Changelog

## 0.1.0.0 - 2026-06-09

* Initial release of microecta
* Extract the small ECTA core and term-search compatibility layer into a
  Cabal-only package.
* Add ECTA pruning
* Add sparse path tries, a dependency-light benchmark harness, and baked
  compile-time RTS caps so optimized builds stay inside the 512M target.
* Document the main API, pruning callbacks, module map, dependency surface,
  and benchmark baseline.
