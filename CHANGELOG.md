# Changelog

## Unreleased

* Relax package lower bounds to less precise minor-version floors while keeping
  the existing upper bounds.
* Add indexed applicative generators represented by ECTA terms, conditioned
  joins backed by ECTA equality constraints, and an optional public QuickCheck
  adapter with an explicit opaque `fromGen` boundary.
* Count and unrank uniform transparent generator languages without
  materializing applicative or joined Cartesian products.
* Expose deterministic rank replay and exact coverage counts, sample weighted
  transparent generators compositionally, and support direct three-way joins
  with two ECTA equality constraints.
* Add partition-preserving grouped generators (`Grouped`, built with `groupBy`
  from any transparent generator) so repeated joins compose compact ECTA
  supports and exact rank indices without enumerating prior layers.
* Generalize keyed operation application to any arity: a `Sig` is written
  like a function type over keys (`leftKey --> rightKey --> resultKey`), and
  the single `apply` joins the operation family with one argument family per
  signature component in one ECTA edge holding one equality constraint per
  argument.
* Condition flat generators with reified key equalities: `match` takes an
  `On` value such as `authenticatedUser :==: fileOwner`, conjoinable with
  `:&&:`, replacing the positional `matchOn`. The three-way `matchOn3` is
  gone; star-shaped conditioning belongs to the keyed layer (`apply`).
* Add qualified do-notation in `Data.ECTA.Gen.Do`, re-exported by the
  QuickCheck adapter: QuickCheck-style blocks for flat generators and for
  grouped operation application at any arity, with curated compile-time errors
  for monadic shapes.

## 0.1.0.0 - 2026-06-09

* Initial release of microecta
* Extract the small ECTA core and term-search compatibility layer into a
  Cabal-only package.
* Add ECTA pruning
* Add sparse path tries, a dependency-light benchmark harness, and baked
  compile-time RTS caps so optimized builds stay inside the 512M target.
* Document the main API, pruning callbacks, module map, dependency surface,
  and benchmark baseline.
