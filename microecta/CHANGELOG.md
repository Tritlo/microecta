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
* Breaking: remove `fragRepresents`, and with it the enumerator's private
  pruning bookkeeping (`pruneDeps` and the `EnumerationState` field behind it,
  `getPruneDeps`, `getPruneDepsOf`, `addPruneDep`, `deletePruneDep`, and the
  hint-ordered variant of `enumerateFully'`). `fragRepresents` hard-coded one
  downstream project's term encoding - `app` with two leading type children,
  `filter`, unary-by-symbol - inside the general enumeration core, and the
  bookkeeping duplicated the oracle state `getAllTermsPrune` already threads
  down each branch. An oracle keeps its own pending checks in that state
  instead, parking them under a hole's `getUVarRepresentative` and settling
  them when it is called for that UVar, and matches terms however it likes.
  Deciding which terms are interesting is no longer this library's business.
* Add `getAllTermsPruneWith` and the `ExpansionOrder` it takes, which let a
  caller say which of the currently expandable UVars to expand next. This
  replaces the removed `usePruneHints` flag, which read the enumerator's own
  pending-check map and could not survive its removal, with an
  encoding-agnostic hook: an oracle that parks checks returns the candidate one
  is waiting on and settles it before enumerating the branch it will kill.
  Returning 'Nothing', or a UVar that is not a candidate, leaves the order to
  the enumerator; the hook cannot make a UVar expandable before it is ready.
  `noExpansionPreference` is the default.
* Export `edgeEcs`, `UVar`, `uvarToInt`, `getUVarRepresentative`, and
  `expandPartialTermFrag` from `Data.ECTA`. An edge's equality constraints can
  now be read back through the same module that reads its symbol and children,
  and a pruning oracle can be given a type signature and can write the
  deferred-check pattern above without reaching into `Data.ECTA.Internal`.
* Breaking: drop `pathHeadUnsafe`, `pathTailUnsafe`,
  `completedSubsumptionOrdering`, and `subsumptionOrderedEclasses` from
  `Data.ECTA.Paths`. The first three remain in `Data.ECTA.Internal.Paths`; the
  last was unused everywhere and is gone.
* Document that ECTAs must be built from one thread, in `Data.ECTA` and in
  `Data.Interned.Extended.HashTableBased`, rather than only in the README, and
  refresh the benchmark baseline in the README to what the suite currently
  measures.
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
