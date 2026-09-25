# 1. One counting core: linear integer arithmetic, with other value types reduced to it

## Context

A generator promises an exact count and a decoder from rank to value. A
symbolic leaf, such as `integers` or `every`, has no pool: the conditions and
contracts on it select its values. So its theory must count and rank the
solutions of a formula, not only decide it. SMT solvers decide. They do not
count. A contract relates several children, so their values are counted
together, and a count does not factor by theory as satisfiability combines by
theory (Nelson-Oppen).

## Decision

One engine counts every symbolic value: the lattice counter for linear
integer arithmetic, `Data.CFTA.Refinement.Lattice`. It sums the variables out
with Faulhaber polynomials, as in Pugh, "Counting solutions to Presburger
formulas" (PLDI 1994). Every other value type reduces to bounded integers
through `Literal`: an integral type stands for itself, and `Bool`, `Char`, and
an enumeration stand for their positions. Deciding a guard is a separate job
behind `Entailment`, with Z3 by default. Counting never calls the solver.

## Why

One target keeps a contract across types countable: a `Bool` child and an
`Integer` child meet in one formula. The reductions keep the count, add no
dependency, and leave the engine unchanged. Mature prior art takes the same
route: MCBAT counts bounded arrays through uninterpreted functions and linear
integer arithmetic, and ABC counts strings with automata and their lengths with
integers.

## Consequences

- A new value type needs only a `Literal` instance.
- Arithmetic on reduced values is exact. Bit-vector wraparound is not modelled.
- Real numbers do not fit. They have no count and no rank.
- A contract reads a `Bool` child as an integer, so it compares the child with
  `literal True`.
- A formula with many disjunctions makes the inclusion-exclusion sum large. A
  BDD or d-DNNF counter is the second backend if a language needs one. It
  goes where `compile` counts the integer points of a formula.

## Discussion points

- One counting plugin for each theory: rejected. A contract couples the
  variables of several theories, and the count of a coupled formula does not
  factor.
- Barvinok's algorithm, through LattE or the barvinok library: polynomial for
  a fixed dimension, but it brings C, GMP, and NTL. Pugh's summation is enough
  for the dimensions that generators make.
- Typed terms, as in SBV, with `Formula` as a term of type `Bool`: this makes
  Booleans usable directly in connectives, but it changes the stored formula
  type. Deferred until a language needs it.
- Other solvers: deciding is already an interface. liquid-fixpoint also
  speaks CVC4, CVC5, and MathSAT. A native Presburger decider, such as the
  Omega test, could decide linear integer guards without Z3.
