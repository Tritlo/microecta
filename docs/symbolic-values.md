# Symbolic values

A refinement generator draws a value from a pool, or from a symbolic leaf. A
pool lists its values, and `compile` decides the guards on them with the
solver, once for each group of equal refinements. A symbolic leaf lists none: its conditions and the contracts on it select the
values, and `compile` counts them without enumeration. Two leaves are
symbolic:

- `integers` draws every `Integer`. Its conditions must bound it.
- `every` draws every value of a type whose values integers stand for, such as
  `Word8`, `Char`, `Bool`, or an enumeration.

This page explains how to use them, what `compile` can count, and how the
counting works. [ADR 1](adr/0001-one-counting-core.md) records why one
counter serves every type.

## A first example

[`TypedValues.hs`](../microcfta-generator/examples/TypedValues.hs) draws a
color, a brightness byte, and a flag, and relates two of them with a contract:

```haskell
data Color = Red | Green | Blue
    deriving (Bounded, Enum, Eq, Show)
    deriving (Literal) via (Enumerated Color)

pixels :: LTAGen.LTAGen (Color, Word8, Bool)
pixels = LTAGen.guarded "pixel" (\_ brightness dimmed -> brightness .> 0 .|| dimmed .== literal True) $ LTAGen.do
    color <- LTAGen.every `LTAGen.satisfying` (./= literal Red)
    brightness <- LTAGen.every
    dimmed <- LTAGen.every
    LTAGen.pure (color, brightness, dimmed)
```

`compile pixels` has 1,022 members: two colors, times 255 brightnesses with
either flag and one zero brightness with the flag. The Haskell types choose
the leaves. `every` for `Color` has three values, for `Word8` 256, and for
`Bool` two. CI runs this example.

## Types

A type works with `every` when it has a `Literal` instance. The instance says
which integer stands for each value (`toLiteral`), which value an integer
stands for (`fromLiteral`), and the least and the greatest value, if the type
has them (`literalRange`).

| Type | Integer of a value | Values of `every` |
| --- | --- | --- |
| `Integer` | itself | unbounded: add conditions that bound it |
| `Natural` | itself | from zero: add an upper bound |
| `Int`, `Int8` to `Int64`, `Word`, `Word8` to `Word64` | itself | the whole range of the type |
| `Bool`, `Char`, `Ordering`, `()` | its position, `fromEnum` | every value |
| an enumeration that derives `Literal` via `Enumerated` | its position, `fromEnum` | every value |

To add an enumeration, derive its instance with `DerivingVia`, as `Color`
does above. To add another type, write the three methods. For example, a
percentage that stands for an integer from 0 to 100:

```haskell
newtype Percent = Percent Int
    deriving (Eq, Show)

instance Literal Percent where
    toLiteral (Percent value) = toInteger value
    fromLiteral = Percent . fromInteger
    literalRange = (Just (Percent 0), Just (Percent 100))
```

`elements` also takes a `Literal` type. It lists its values, and each value
has the exact refinement `\v -> v .== literal x`.

## Conditions and contracts

A condition or a contract reads a value as its integer, so compare it with a
`literal`: `(./= literal Red)`, or `\c -> literal 'a' .<= c .&& c .<= literal 'z'`.
A `Bool` is 0 or 1, so a contract writes `dimmed .== literal True`. Arithmetic
on these integers is exact: `x + y` on two `Word8` values does not wrap around.

On a symbolic leaf, `satisfying` narrows the values. It does not test the leaf
with the solver. A contract of `guarded` keeps the tuples of values that it
admits. The contract can also name a child from `elements`, whose refinement
fixes one integer. With `ensuring`, a constructor's result is a term of its
integer children, and a parent's contract reads that term. The
[generator README](../microcfta-generator/README.md#results-and-bounded-recursion)
shows sorted lists, where every element stays symbolic up to the end of the
list.

Ranks follow the lexicographic order of the symbolic leaves, from left to
right. Rank 0 of `pixels` is `(Green, 0, True)`. A shrink goes to an earlier
rank, so it makes the first leaves smaller first.

## What compile can count

`compile` counts the integer points of one formula for each group of
children: the conditions of the symbolic leaves, the parts of the guards that
read them, and the exact values of the other children that those parts name.
The formula must meet three rules:

1. Each atom is linear: sums, differences, and constant factors of integers.
2. Each symbolic value is bounded above and below.
3. When the counter sums a value out, each bound has the coefficient one or
   minus one on that value, after division by the common divisor. The counter
   sums the values out from the last leaf to the first. So `2 * x .<= y`
   breaks this rule when `x` comes after `y`, and `2 * x .<= 10` never does.

A formula that breaks a rule gives `UncountableIntegers`, and `explain` names
the rule. A guard form other than a contract or a condition, an equality, and a
guard that reads below the root of a child with open values give
`IntegerLeafRead`.

## How the counter works

`Data.CFTA.Refinement.Lattice` counts in three steps:

1. It reads the formula as a signed sum of conjunctions. A negation is one
   minus the formula, and a disjunction follows inclusion and exclusion. Each
   conjunction is a polyhedron.
2. It sums the variables out, from the last to the first. For each choice of
   the largest lower bound and the smallest upper bound of a variable, the
   variable ranges over one interval, and the Faulhaber formulas give the sum
   of a polynomial over that interval. Each step keeps the number of
   completions as a sum of polynomials over polyhedral pieces. This is Pugh's
   method from "Counting solutions to Presburger formulas" (PLDI 1994).
3. To decode a rank, it chooses each variable in turn by a binary search over
   the counts of completions.

The cost grows with the number of symbolic values that one formula joins, and
with the number of bounds on each value. The bounded-reads contract joins two
values that range to a million, and compiles in about 1.5 ms. Sorted lists of
eight elements join eight values, and compile in about 25 ms.
A formula with many disjunctions gives many signed conjunctions.

## Deciding and counting

A theory does two jobs in this library, and different parts do them:

- Deciding: a guard over pools, a condition on a pool, the pruning of an
  imported automaton, and similarity need a yes or a no. The engine asks an
  `Entailment`, which `withZ3` gives. `compileWith` takes any `Entailment`.
  liquid-fixpoint can also drive CVC4, CVC5, and MathSAT.
- Counting: a symbolic leaf needs the number of solutions and the solution at
  each rank. Solvers do not give these. The lattice counter gives them, and it
  never calls the solver.

Every symbolic type reduces to integers, so one counter serves all of them, and
a contract can relate values of different types in one formula. The ADR lists
what does not fit: real numbers have no count and no rank, bit-vector
wraparound is not modelled, and a `Bool` child is an integer in a contract.
