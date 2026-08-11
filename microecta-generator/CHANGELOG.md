# Changelog

## 0.1.0.0 - Unreleased

* Add indexed applicative generators represented by ECTA terms, conditioned
  joins backed by ECTA equality constraints, and QuickCheck integration with
  an explicit opaque `fromGen` boundary.
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
  arithmetic whenever the cardinality fits and `Integer` otherwise, with
  strict argument binding at every compiled application. Rank order, masses,
  supports, and inspection are unchanged; non-uniform and opaque generators
  keep the previous sampling path. The typed-expression benchmark moves from
  0.56x-1.39x of a handwritten QuickCheck generator to 1.31x-2.12x at depths
  one through four.
* Add `mapWithKey` for grouped generators, and `forAll` and `sized` to the
  QuickCheck adapter: `forAll` shrinks to the smallest failing member by
  first searching every structurally smaller member in size order
  (`smallerMembers`, capped), then shrinking components through
  `shrinkRank` - every shrink stays inside the generated language, the
  counterexample is globally size-minimal whenever the search reaches one,
  and the failing rank replays it deterministically; `sized` maps
  QuickCheck's size parameter to a generator, building each size once.
* Add qualified do-notation in `Data.ECTA.Gen.Do`, re-exported by the
  QuickCheck adapter: QuickCheck-style blocks for flat generators and for
  grouped operation application at any arity, with curated compile-time errors
  for monadic shapes.
* Add `mu`, which builds a generator from its own language. A recursive
  generator stands for the whole unbounded language: size classes counted by
  FEAT-style convolution instead of a cardinality, size-major ranks, and a
  `Mu` node for a support. `upToSize` bounds it to an ordinary finite
  generator, and `toGen` and `forAll` do that from QuickCheck's size
  parameter, drawing uniformly from the members of at most that size.
  Bounding preserves ranks, so a counterexample replays under any bound.
  Finite generators keep their mixed-radix ranks and compiled decoder
  unchanged. Recursion must be guarded by `<*>`, `frequency` alternatives
  around a recursive occurrence must carry equal weights, and inspection
  that needs one term per member (`groupBy`, `match`, `pmf`, `countBy`)
  reports an error on a recursive language.
