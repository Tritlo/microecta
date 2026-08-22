# Changelog

## 0.1.1.0 - Unreleased

* Fix path compression in `Data.Persistent.UnionFind`: `find` rebuilt the
  forest from the map it read before recursing, discarding every compression
  the recursive call had made, so only the first link of a chain was ever
  flattened. Representatives were always correct, but repeated `find` on a deep
  chain did more work than it should have.
* Stop baking `+RTS -K512M -M512M -RTS` into the library's `ghc-options`. The
  cap aborted GHC itself, so a compile-time memory regression became a hard
  build failure for anyone depending on this package, including Hackage's
  documentation builder. CI enforces the same budget, where a regression is a
  signal rather than someone else's broken build.
* Raise the `base` lower bound to 4.21, matching `tested-with` and the floor
  that `containers >=0.7` already implied. The previous 4.13 bound claimed
  support back to GHC 8.8, which no configuration ever built.
* Make contradictory equality constraints safe to pretty-print, replace
  partial test and enumeration paths with explicit cases, and enable strict
  warnings on GHC 9.12 and 9.14.
* Correct the `equivalence` lower bound to 0.4.1, the first release exporting
  the `classes` operation used by the library.
* `createMu` drops a recursive node whose variable does not occur in its
  body, so `Mu $ \r1 -> Mu $ \_r2 -> Node [Edge "f" [r1]]` is the same node
  as `Mu $ \r1 -> Node [Edge "f" [r1]]`. `intersect` already avoided
  introducing such nodes; this covers every recursive node however it was
  built. `createMuDontCleanup` keeps the old behaviour, for tests that need
  a redundant node to exist. Ported from jkoppel/ecta 7614877 by Edsko de
  Vries, which never landed upstream.
* Add `dropEdgeConstraints` and `dropConstraints`, which drop equality
  constraints from an edge or a whole node. The result over-approximates the
  language, so it is for cases where the constraints are not what is being
  studied. Ported from jkoppel/ecta 059cafa by James Koppel.
* Relax package lower bounds to less precise minor-version floors while keeping
  the existing upper bounds.
* Move the package into the repository's two-package Cabal workspace without
  changing the exposed core API.

## 0.1.0.0 - 2026-06-09

* Initial release of microecta
* Extract the small ECTA core and term-search compatibility layer into a
  Cabal-only package.
* Add ECTA pruning
* Add sparse path tries, a dependency-light benchmark harness, and baked
  compile-time RTS caps so optimized builds stay inside the 512M target.
* Document the main API, pruning callbacks, module map, dependency surface,
  and benchmark baseline.
