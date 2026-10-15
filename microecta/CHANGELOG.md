# Changelog

## 0.2.0.0 - Unreleased

This is a major bump rather than 0.1.1.0 because the public API changed; see
the entries marked breaking below. Existing code that only builds ECTAs,
reduces them, or enumerates them needs no migration.

* Widen the `containers` bound to `<0.9`, so GHC 9.14 builds against the 0.8
  it ships instead of rebuilding 0.7 beside its own boot library.
* Key the edge joins on the symbol itself rather than on its hash.
  `clusterByHash` and `hashJoin` took an `Int` projection and documented the
  precondition that it be injective, and `intersect` and
  `withoutRedundantEdges` passed them `hash . edgeSymbol`. A lawful `Hashable`
  instance for a user alphabet may collide, and then `intersect {A} {B}`
  returned `[B]` and `withoutRedundantEdges {A, B}` dropped an edge. Both
  helpers now take a key projection of any `Hashable` key type and key the
  table by the key, so the precondition is gone.
* Fuse the expandable-variable scan into one pass over the UVar slots. The
  scan now collects candidates in an `IntSet`, resolves only suspended
  constraint targets through union-find, and writes path compression back
  once, replacing the full `refreshReferencedUVars` sweep after every
  expansion while preserving `ExpansionOrder`. On 65,536 constrained terms,
  median CPU time fell from 0.478s to 0.218s and allocation from 4.44 GB to
  2.25 GB; the existing enumeration benchmark improved by 8.6%. Differential
  evaluation matched the old implementation over 10,000 generated automata
  and one million deliberately stale union-find states.
* Fix `unfoldBounded` looping forever on a negative bound. Only `0` was
  matched, so a negative count decremented without end. Zero or less now
  unfolds nothing, which is what the bound already meant.
* `reduceEqConstraints` makes one pass over the equivalence classes of an
  edge, as in the ECTA paper. One pass is not always a fixpoint: the
  intersection for one class can narrow a node that an earlier class has
  already read, as the fixture open since 2021-06-29 shows. Iterate the
  reduction to get a fixpoint, as `fixUnbounded (withoutRedundantEdges .
  reducePartially)` does; at that fixpoint one pass at each edge changes
  nothing. An earlier change on this unreleased version repeated the pass at
  each edge, and that made the term search of the ECTA paper about 100 times
  slower, because each new pass reads new nodes and misses the memo tables.
* Fix `nodeRepresents` accepting a term in which every path of an equality
  class is missing. The class compared the missing subterms, and `Nothing`
  equals `Nothing`. Enumeration and reduction require every path of a class,
  so for `p(x, y)` with `x.0 = y.0` over `x, y` in `{a, f(a)}`, `getAllTerms`
  gave only `p(f(a), f(a))` while `nodeRepresents` also accepted `p(a, a)`.
  A class is now satisfied only when every path exists and all its subterms
  are equal.
* Fix `intersect` and `withoutRedundantEdges` on a symbol that has edges of
  two arities. The edge intersection zipped the two child lists, which drops
  the extra children of the longer one. So `intersect` of `f(a | b)` and
  `f(a | b, a | b)` accepted `f(a)` and `f(b)`, which the second operand
  rejects, and `withoutRedundantEdges` read `f(a)` as implied by `f(a, b)` and
  removed it. Edges with different numbers of children now have an empty
  intersection, and `intersectEdge` returns `Nothing` for them.
* Fix enumeration of an edge whose equality class names a child that the edge
  does not have. `mkEdge` kept the constraint, and enumeration checks the
  highest child index only for constraints that an ancestor passes down, not
  for the edge's own classes. So for `p(a | b)` with `0 = 1`, `getAllTerms`
  gave `p(a)` and `p(b)`, while `nodeRepresents` rejected both and
  `reducePartially` gave `EmptyNode`. `mkEdge` now gives the empty edge when a
  path starts at a missing child or has a negative index, as it does for a
  contradiction. `Data.ECTA.Internal.Paths` exports the check as `fitsArity`.
* Fix `createMu id`, a binder whose body is its own variable. It accepts no
  term, but `createMu` kept it as a `Mu` whose unfolding is the node itself,
  so `nodeRepresents`, `termsMatching`, `union`, and `nodeEdges` did not
  return on it, and `getAllTerms` listed the recursion marker `Mu` as one of
  its terms. `createMu` now gives `EmptyNode` for it, also when it appears
  only after an unused inner binder is dropped, as in
  `createMu (\r -> createMu (\_ -> r))`. `createMuDontCleanup` still builds
  the node.
* Share the unfolding of each recursive node. `unfoldOuterRec` substituted
  the binder into the body on every call, so every operation that reads the
  edges of a `Mu` rebuilt the same interned nodes. The unfolding is now
  memoized per recursive node.
* Substitute into a recursive node in time that does not grow exponentially
  with its nested binders. `createMu` applies its body more than once, and
  substitution into a binder calls `createMu`, so substitution under nested
  binders applied each inner binder again for each application of the outer
  one, and it rebuilt closed subgraphs too. Substitution now returns a node
  without free variables unchanged, and keeps the result for each binder and
  the bindings of its free variables. The `substFree` Haddock now says that
  its identity postcondition holds for binders that `createMu` made.
* Choose the interning placeholder of a `Mu` above every placeholder of an
  enclosing binder that its body captures. `createMu` named the body's own
  variable `RecUnint d`, where `d` is the body's nesting depth, so a body that
  captured an enclosing binder's placeholder at the same level got an
  interning shape that aliased it. A body that captures no enclosing
  placeholder keeps its old shape, so its interning key does not change.
* Hash the intersection environment once, and narrow the paths of an
  equality class in one traversal. Every memo lookup of the intersection
  hashed its whole recursive environment; the environment now carries its
  hash. The equality reduction restricted and edited the children of an edge
  once per path, each time from the root; it now builds one trie of the
  required paths and applies the edits of a class in one traversal. The
  results are the same.
* Fix `maxIndegree` returning `minBound :: Int` for a node with no normal
  nodes to count, such as `EmptyNode` -- the identity of the `Max` monoid
  leaking out as if it were an answer. It returns 0.
* Fix `withoutRedundantEdges` raising "compare: unexpected RecDepth" on a
  recursive node whose body has two edges of one symbol, such as
  `createMu (\t -> Node [a, pair(t, t), pair(t, a)])`. It rebuilt the body of
  a `Mu` under a placeholder variable and intersected the open alternatives,
  and intersection cannot compare or resolve a placeholder. So the README's
  `fixUnbounded (withoutRedundantEdges . reducePartially)` failed on such
  inputs. Now only a node without free recursive variables is changed. A
  closed `Mu` compares the alternatives of its unfolding, where every child is
  closed, and keeps the body alternatives whose unfolding remains. A node that
  refers to an enclosing binder keeps all of its alternatives.
* Fix `reducePartially` not returning when an equality class reaches into a
  recursive node whose body has constraints too, such as `g(y, y)` with
  `0.0 = 1.0` over `y = b | h(x, y)` inside `x`. Reading or editing a path
  through such a `Mu` unfolds it, the unfolding carries the constrained edges
  of the body, and the descent into the edited child reduces those edges,
  which unfold the `Mu` again. `termsMatching` and the README's
  `fixUnbounded (withoutRedundantEdges . reducePartially)` inherited this.
  Reduction now leaves a class unreduced when one of its paths meets a `Mu`
  with constraints. Reduction only narrows, and enumeration and
  `nodeRepresents` still check every class, so the language does not change.
  A `Mu` without constraints still unfolds as before.
* Fix `crush` folding a shared `Mu` once for each path to it. The visited set
  held only ordinary nodes, so a recursive node reachable from two places was
  folded twice, with its body. `nodeCount`, `edgeCount`, `maxIndegree`, and
  `refold` were not affected, but a fold that counts or collects `Mu` nodes
  was. Recursive and ordinary nodes draw identities from one counter, so one
  visited set now covers both.
* Fix enumeration of an automaton whose root is a `Mu` -- what `createMu`
  returns, and the idiomatic way to write a recursive automaton.
  `getAllTerms` returned `[]`, claiming the language was empty, and
  `getAllTruncatedTerms` raised "UVar has not been enumerated". The root UVar
  holds an unconstrained `Mu`, which is where enumeration stops, so it is never
  expanded; both functions now truncate it exactly as they already truncated a
  `Mu` nested under an edge. `getAllTerms` yields the marker term `Mu` and
  `getAllTruncatedTerms` yields `TruncatedRecursion`. Their documentation now states
  that they truncate at recursion, and points at `unfoldBounded`.
* Breaking: partial and truncated enumeration uses `PartialSymbol symbol`
  rather than inventing symbols such as `v0`, `<v0>`, and `Mu` in the caller's
  alphabet. `getAllTruncatedTerms` and `termFragToTruncatedTerm` distinguish
  concrete symbols from `UVarHole`; `expandPartialTermFrag` additionally marks
  an unconstrained recursive node with `TruncatedRecursion`. These fixed constructors
  keep partiality outside the caller's alphabet. These APIs no longer require
  `IsString`.
* `expandPartialTermFrag` reports a recursive node that still carries suspended
  constraints as a `UVarHole` rather than as `TruncatedRecursion`. Such a node
  is still pending expansion, and an oracle that parks its checks on holes
  would have read it as final and settled a check that had not been decided.
  `TruncatedRecursion` now means what enumeration means by it: a recursive node
  with no constraints left, which is where enumeration stops.
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
  caller say which of the currently expandable UVars to expand next. It takes
  the truncated-recursion symbol as its first argument, as `getAllTermsWith`
  does, rather than requiring `IsString`, so an ordinary datatype alphabet can
  prune; `enumPruneWith` matches it. `getAllTermsPrune` and `enumPrune` keep
  `IsString` and pass `"Mu"`. This
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
* Breaking: drop `pathHeadUnsafe`, `pathTailUnsafe`, and
  `completedSubsumptionOrdering` from `Data.ECTA.Paths`.
  `completedSubsumptionOrdering` remains in `Data.ECTA.Internal.Paths`; the
  two unsafe path accessors had `toPathTrie` as their only caller and are gone.
  The safe `subsumptionOrderedEclasses` remains public, while its partial
  counterpart is internal.
* `memo2` keys one table by the argument pair instead of nesting two unary
  tables. The nested form allocated a fresh hash table for every distinct first
  argument -- about a kilobyte each before storing an entry -- which a heap
  profile showed dominating a constraint-heavy run. On 64k distinct first
  arguments that is 167 MB against 68 MB now, with the core benchmark within
  noise on time and 0.1% up on allocation.
* Make building ECTAs safe from any thread. The hash-consing and memoization
  tables are now immutable maps in `IORef`s, read without blocking and updated
  atomically; racing inserts converge on one interned `Id`. A probe that raced
  16 runs out of 20 before now reports no disagreement in 25. Recursive-node
  shapes are computed before entering the cache and stored in `UninternedMu`,
  so hashing and equality do not rebuild nodes during an update.

  Together these take the core benchmark from 0.77s and 4,765 MB to 0.30s and
  2,161 MB, at about 1.5x the retained memory in the unbounded-growth case,
  which the README quantifies. The stored shape accounts for the smaller part
  of that (0.69s and 4,317 MB with it alone); the rest is the immutable map
  being a faster cache than the mutable one it replaced, not a cost of being
  safe.
  Breaking: `UninternedMu` takes the shape as a new first argument, and
  `Cache`'s `content` field is an `IORef` of an immutable map.
* Breaking: replace the Spectacular-derived `nodeRepresentsTemplate` and
  `edgeRepresentsTemplate` predicates with an explicit `Template` type,
  `matchesTemplate` for concrete terms, and `termsMatching` for restricting an
  ECTA language. Wildcard symbols, exact arity, and prefix matching are now
  separate constructors; `<v>` is no longer reserved, and equality constraints
  are retained while the language is restricted.
* Sharpen the concurrency warning with what actually happens. Building one
  structurally identical node from several threads produced two identities in
  three runs out of eight, silently -- no exception. That is the first,
  eight-run probe; the entry above reports the later 20-run one against the
  synchronized tables. Both READMEs now say so, and name the likeliest cause: a
  parallel test runner, which `tasty` is by default and `hspec` is under
  `parallel`.
* Add tests for `Application.TermSearch.*`, which had none: the type encoding,
  the canonical and prefixed type variables, `filterType` keeping exactly the
  terms of the requested type, and `reduceFully` reaching a fixpoint.
* Document the measured limits in the README. Enumerating an unfolded
  recursive automaton is practical to about six unfoldings, and equality
  constraints whose paths nest cost about 4.7x per level, which makes about ten
  the wall. Constraint *count* is not a problem -- a thousand independent
  depth-two classes take 0.04s -- and intersection, reduction and the
  generator's counting all measured flat over the ranges tried.
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
  studied. Ported from jkoppel/ecta 059cafa by Jimmy Koppel.
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
