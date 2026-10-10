# 2. A generator's sizes count pays, as in FEAT

## Context

A size bound (`upToSize`), the size classes of `countAtSize` and `pmfAtSize`,
and the order of shrinking all read the size of a member. The size was the
number of source choices: `pure` and every atom cost one, and `<*>` added its
sides. So `pure f <*> x` was one larger than `f <$> x`, `pure id <*> v` was not
`v`, a built tree counted its leaves while an imported term counted its nodes,
and a product with `pure` guarded a recursion that `fmap` did not.

## Decision

Sizes follow FEAT (Duregård, Jansson, and Wang, "Feat: Functional Enumeration
of Algebraic Types", Haskell Symposium 2012, §2 "Guarded recursion and
costs"). `pure` costs zero, `<*>` adds the sizes of its sides, `fmap` and the
choices keep sizes, and `pay` adds one to every member. An atom (`elements`,
`fromIndexed`, `every`, `atomic`, a group of `groupOn`) costs one, a
constructor (`node`, `leaf`, `guarded`, `measured`) pays one, and an imported
term costs its number of nodes. A recursion must reach its occurrence through
a pay, or through a product whose other side has no member of size zero, and
through a product or a constructor, which adds a term node.
`Data.CFTA.Gen` and `Data.CFTA.Ranked` export `pay`.

## Why

The `Functor` and `Applicative` laws then hold for sizes, so the members and
the distribution at each size do not depend on how a generator is written.
Built and imported terms of one datatype have the same sizes. FEAT shows that
this cost model guards recursion and keeps every size class finite.

## Consequences

- Identity, homomorphism, interchange, and `fmap f x = pure f <*> x` hold rank
  by rank. Composition holds for the members, counts, and distribution of each
  size. For a finite language it also holds rank by rank, because mixed-radix
  ranks are associative. For a recursive language, the ranks inside a size
  class can differ: a product orders its splits by the size of its left side,
  so `(u <*> v) <*> w` and `u <*> (v <*> w)` order the same members
  differently. The reference spec checks all five laws.
- A built tree is one larger for each constructor, and `pure` inside a product
  is one smaller, so size bounds and the samples of bounded generators change.
- `recur (\t -> oneof [pure Leaf, Node <$> t <*> t])` is unguarded. A `node` or
  a `pay` around the recursive alternative guards it.
- `recur (\t -> oneof [leaf, pay t])` is unguarded too, although FEAT accepts
  it. A pay adds no term node, so the members of such a recursion can share
  one term, as they do under a constructor that removes their choice
  wrappers, and that term would have infinitely many ranks.
  `oneof [leaf, node "s" t]` is guarded.
- Two imports keep a size that is not their number of nodes. A symbolic
  acyclic import is one atom per term, of size one. A compact acyclic import
  counts the shared subterm of a group of equal children once.

## Discussion points

- Atoms cost one, although in FEAT only `pay` costs. A free atom would make
  every `recur (\t -> oneof [elements xs, f <$> t <*> t])` unguarded, and FEAT
  pays for each constructor, nullary ones too, through `consts`. So an atom is
  a constructor that pays once.
- FEAT starts a pay with an empty part of size zero to make a recursive
  enumeration productive. Here that zero count would multiply the count of the
  full size in a product, and reading that count inside its own definition
  does not terminate. A pay and a product start their counts at their minimum
  size instead, which the knot knows before it counts.
