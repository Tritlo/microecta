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
  like a many-sorted operation signature (`leftKey :* rightKey :-> resultKey`),
  and
  the single `apply` joins the operation family with one argument family per
  signature component in one ECTA edge holding one equality constraint per
  argument.
* Condition flat generators with reified key equalities: `match` takes an
  `On` value such as `authenticatedUser :==: fileOwner`, conjoinable with
  `:&&:`, replacing the positional `matchOn`. The three-way `matchOn3` is
  gone; star-shaped conditioning belongs to the keyed layer (`apply`).
* Add `frequencies`, the per-group weighted choice among grouped generators,
  so alternated layers such as depth-bounded languages stay grouped.
* Compile transparent uniform sampling: every outcome index now retains a
  symbolic decode plan (choices, mixed-radix products, maps) that lowering
  normalizes — maps pushed into leaves, nested choices spliced flat, small
  leaves tabulated — and compiles to one flat decoder, on machine `Int`
  arithmetic whenever the cardinality fits and `Integer` otherwise. Rank
  order, masses, supports, and inspection are unchanged; non-uniform and
  opaque generators keep the previous sampling path.
* Add `mapWithKey` for grouped generators, and `forAll` and `sized` to the
  QuickCheck adapter: `forAll` shrinks by walking ranks toward zero, so every
  shrink stays inside the generated language and the failing rank replays the
  counterexample deterministically; `sized` maps QuickCheck's size parameter
  to a generator, building each size once.
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
