# microlta-generator

`microlta-generator` is the Liquid Tree Automata adapter for the ranked engine
in `microecta-generator`. Building the language is pure. `compile` is the one
imperative boundary: it asks Liquid Fixpoint/Z3 which guarded witnesses are
valid and which pool refinements imply one another, then returns a pure
`Compiled` value.

```haskell
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE QualifiedDo #-}

import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.Guard (refines)
import Data.LTA.Refinement (true, (.==.), (.>=.))

choices = LTA.pool
  [ LTA.refined 0 "non-negative" (value .>=. 0)
  , LTA.refined 1 "one"          (value .==. 1)
  ]

liquidPairs =
  LTA.node "pair" true (\left right -> left `refines` right) $ LTA.do
    left  <- choices
    right <- choices
    LTA.pure (left, right)
```

The do-block only describes independent children. The root symbol, refinement,
and guard live at `node`, where they belong. A value-dependent child choice is
rejected at compile time; express that relationship with the liquid guard.
The guard function receives symbolic constructor arguments in the same order
as the child generators below it. For guards over nested terms,
`descendant left [1]` selects the second child below `left`. Raw `Guard`
constructors and `argument` remain available for unusual programmatic guards.

After the one solver phase, QuickCheck and replay are pure:

```haskell
Right compiled <- LTA.compile solver liquidPairs

quickCheck $ LTA.forAll compiled (uncurry (>=))
replayed = LTA.select failingRank compiled
```

The pool need not be part of a long-lived specification. It can be sampled and
frozen only for one generation run:

```haskell
compiled <- LTA.compileSampled solver $ do
  lefts  <- LTA.samplePool 32 nativeRefinedInt
  rights <- LTA.samplePool 8  nativeRefinedInt
  pure $
    LTA.node "pair" true (\left right -> left `refines` right) $ LTA.do
      left  <- lefts
      right <- rights
      LTA.pure (left, right)
```

Here the two pools are sampled independently. Sample once and use the same
`LTAGen` at both child positions when they should share a universe. The pools
remain fixed inside `compiled`; changing them for each individual test would
make ranks, replay, and shrinking unstable and would also invoke Z3 per test.
Independent pool sizes multiply: the example presents 32 x 8 candidate pairs
to the current finite compiler before its guards reject any of them. Larger
languages will eventually need symbolic or incremental compilation rather than
enumerating that Cartesian product.

For replay across process runs, fix each pool with a seed, just as in
`microecta-generator`:

```haskell
lefts  = LTA.freeze 20260902 32 nativeRefinedInt
rights = LTA.freeze 20260903 8  nativeRefinedInt
```

The same seed, size, and native generator produce the same pool ranks. Reuse a
single frozen value at several child positions when they should range over one
shared universe; use distinct seeds for independent pools.

## Refinement shrinking and pools

A refined pool contributes potential local replacements. Compilation asks Z3
whether the current refinement implies each candidate refinement. Strict
implication is a shrink; logically equivalent entries shrink toward the earlier
pool rank to keep the graph acyclic.

The refinement is a trusted annotation on the Haskell value. The generic
library cannot prove that an arbitrary `a` satisfies a Liquid Fixpoint
predicate without an explicit encoding for `a`; a typed frontend could supply
that check later.

Those local replacements are lifted through `node` products. The complete LTA
guard is then decisive: a replacement that makes the whole tree invalid is
never handed to QuickCheck. The compiler follows its shrink edges through that
invalid intermediate and reconnects any valid descendants.

For the example, the raw product is:

```text
(0,0)  accepted
(0,1)  rejected: non-negative does not entail exactly-one
(1,0)  accepted
(1,1)  accepted
```

`(1,1)` therefore shrinks first to `(1,0)` and can reach `(0,0)` without ever
emitting `(0,1)`. `samplePool n native` does the same thing for a finite pool
drawn once from a native QuickCheck generator. Repeated draws remain repeated
ranks, retaining empirical weight, while implication supplies semantic shrink
edges.

`compiledSupport` returns the LTA containing only accepted witnesses. Its
automaton is a specialization of `Data.Tree.FTA`; `Data.Tree.Gen` and
`Data.Tree.Gen.QuickCheck` provide the shared sampling and shrinking machinery.
Weights influence sampling but do not duplicate replay ranks.

The current spike discovers every implication relation inside a pool, which is
quadratic in the number of distinct pool refinements. That is useful for small
semantic universes. A production version should let a native value shrinker
propose a sparse candidate graph for large sampled pools, with Z3 validating
only those edges.

Enter the repository's `nix-shell` to place Z3 on `PATH`, then run the complete
example:

```sh
cabal run liquid-pairs
```
