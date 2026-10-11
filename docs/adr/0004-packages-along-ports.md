# 4. Packages along the ports

## Context

All the code shipped as `microcfta` and `microcfta-generator`. The global
intern tables, the Z3 adapter, the liquid layer, and the ranked layer sat
next to code that does not need them. So a test of one part built all of it,
the core tests needed Z3, and a Lean model of one part had no small premise
to assume for the rest.

## Decision

Seven packages, cut along module boundaries that already existed, one cut at
a time:

| Package | Holds |
| --- | --- |
| `cfta-base` | Terms, paths, the index and rank arithmetic, the tree searches, the union-find. |
| `cfta-intern` | The global intern tables and memo tables. |
| `cfta` | The interned engine, `Symbol`, `Constraint`, equality, and `Refinement.Expression`. |
| `cfta-liquid` | The liquid tree automata: `Data.CFTA.Refinement` and its modules. |
| `cfta-z3` | The Z3 adapter of the `Entailment` port. |
| `cfta-rank` | The ranked layer: plans, decoders, sizes, samplers, shrinking. |
| `cfta-generator` | The generators, and the QuickCheck backend of the ranked layer. |

Each package has a test suite for its contract. Only `cfta-z3` and the
generator's refinement tests need Z3. The packages are no longer micro, so
they drop the prefix; the modules stay `Data.CFTA.*`.

## Why

GHC optimizes a call across a package boundary as it optimizes a call across
a module boundary: the same interface files, the same unfoldings. So the cuts
keep the speed. Measured in instructions against the commit before the split,
every standard cell and probe of the renamed packages moves by at most 0.05%,
except `lta-do 20` (-1.2%; it moves about 1.1% between equal builds), the
`sorted` probe (-0.4%), and the recursion probes of under a million
instructions (up to 0.15%). Every sample checksum is equal.

## Discussion points

- A constraint type parameter on `Node` and `Edge` would make the engine
  generic over theories, but it adds a dictionary to the inner loops and a
  two-type key to every cache. Rejected.
- `type Formula = Fixpoint.Expr` still puts liquid-fixpoint into `cfta`, and
  the generator catches the adapter's `TimeLimitReached`. A spike will test a
  formula type of the core's own, so that liquid-fixpoint sits only behind
  the `Entailment` port.
- `Refinement.Expression` stays in `cfta`: it builds the formulas that a
  `Symbol` holds, and it imports only `Symbol`.
- The QuickCheck backend of the ranked layer stays in the generator, so that
  `cfta-rank` needs no QuickCheck.
- Seven packages mean more release work than two. `scripts/release.sh` gives
  the publish order.
