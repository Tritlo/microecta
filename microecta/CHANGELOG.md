# Changelog

## 0.2.0.0 - Unreleased

This is a major bump rather than 0.1.1.0 because the pruning API lost members;
see the two entries marked breaking below. Nothing that only builds ECTAs,
reduces them, or enumerates them needs to change.

* Fix `unfoldBounded` looping forever on a negative bound. Only `0` was
  matched, so a negative count decremented without end. Zero or less now
  unfolds nothing, which is what the bound already meant.
* Fix `maxIndegree` returning `minBound :: Int` for a node with no normal
  nodes to count, such as `EmptyNode` -- the identity of the `Max` monoid
  leaking out as if it were an answer. It returns 0.
* Fix enumeration of an automaton whose root is a `Mu` -- what `createMu`
  returns, and the idiomatic way to write a recursive automaton.
  `getAllTerms` returned `[]`, claiming the language was empty, and
  `getAllTruncatedTerms` raised "UVar has not been enumerated". The root UVar
  holds an unconstrained `Mu`, which is where enumeration stops, so it is never
  expanded; both functions now truncate it exactly as they already truncated a
  `Mu` nested under an edge. `getAllTerms` yields the marker term `Mu` and
  `getAllTruncatedTerms` yields the hole `v0`. Their documentation now states
  that they truncate at recursion, and points at `unfoldBounded`.
* Remove `getTermFragForUVar`, which was partial and is now unused;
  `rootTermFrag` replaces its one caller.
* `toPathTrie` reports its own precondition -- distinct paths, none a prefix of
  another -- instead of failing inside `pathHeadUnsafe`, whose message named
  neither the function nor the precondition. Repeated paths violate it too,
  which the previous wording did not make clear.
* `EqConstraints` is no longer a record, so its derived `Show` renders
  positionally (`EqConstraints [...]` rather than
  `EqConstraints {getEclasses = [...]}`). It has no `Read` instance, so this
  affects display only.
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
  `Data.ECTA.Paths`. `completedSubsumptionOrdering` remains in
  `Data.ECTA.Internal.Paths`; the other three are gone entirely, the two
  `Unsafe` ones having had `toPathTrie` as their only caller.
* Document that ECTAs must be built from one thread, in `Data.ECTA` and in
  `Data.Interned.Extended.HashTableBased`, rather than only in the README, and
  refresh the benchmark baseline in the README to what the suite currently
  measures.
* `memo2` keys one table by the argument pair instead of nesting two unary
  tables. The nested form allocated a fresh hash table for every distinct first
  argument -- about a kilobyte each before storing an entry -- which a heap
  profile showed dominating a constraint-heavy run. On 64k distinct first
  arguments that is 167 MB against 68 MB now, with the core benchmark within
  noise on time and 0.1% up on allocation.
* Document what the hash-consing and memo tables cost. They never evict, so
  retained memory grows with the number of *distinct* nodes, edges and symbols
  ever constructed -- and not at all with the work done over values that
  already exist, which measures flat. The README now says so, with figures, and
  says plainly that a long-lived process building unboundedly many unrelated
  automata will grow until it runs out of memory. The previous wording called
  the tables "deliberately small".
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
