{-# LANGUAGE DerivingStrategies #-}

{- | Indexes, ranks, and counts of terms, automata, and languages.

Each value is an 'Int' or an 'Integer'. An index or a rank is zero-based. A
count, such as an arity or a cardinality, starts at zero too. Each kind of
index or count has its own newtype, so the compiler rejects a value of one
kind in the place of another kind.
-}
module Data.CFTA.Index (
    ChildIndex (..),
    TransitionIndex (..),
    Arity (..),
    childIndexes,
    ArgumentIndex (..),
    Depth (..),
    VarIndex (..),
    Rank (..),
    Cardinality (..),
    everyRank,
    hasRank,
    pairRank,
    splitRank,
    RankOffset (..),
    nextOffset,
    offsetRank,
    rebaseRank,
    Size (..),
    ClassRank (..),
    classMemberRank,
    Weight (..),
    countWeight,
) where

import Data.Hashable (Hashable)

{- | The zero-based index of a child in the children of a transition or a term.

A 'Data.CFTA.Path.Path' is a list of child indexes.
-}
newtype ChildIndex = ChildIndex Int
    deriving newtype (Eq, Ord, Show, Hashable, Num, Enum)

{- | The zero-based index of a transition among the transitions of a state or
node.

In an interned automaton, a transition is an 'Data.CFTA.Interned.Edge'.
-}
newtype TransitionIndex = TransitionIndex Int
    deriving newtype (Eq, Ord, Show, Hashable, Num, Enum)

{- | The number of children of a symbol, a transition, or a term node.

The child indexes of a node with arity @n@ are @0 .. n - 1@.
-}
newtype Arity = Arity Int
    deriving newtype (Eq, Ord, Show, Num, Enum)

-- | The child indexes of a node with the given arity, from @0@ to @arity - 1@.
childIndexes :: Arity -> [ChildIndex]
childIndexes (Arity arity) = map ChildIndex [0 .. arity - 1]

{- | The zero-based index of an argument of a guard, a contract, or an n-way
join.

The arguments of a guard or a contract are the children of a transition, in
order. The arguments of an n-way join come after its operation.
-}
newtype ArgumentIndex = ArgumentIndex Int
    deriving newtype (Eq, Ord, Show, Hashable, Num, Enum)

{- | The depth of a node in a term, or a bound on that depth.

A leaf has depth 0. The tree automata literature counts a leaf as height 1.
-}
newtype Depth = Depth Int
    deriving newtype (Eq, Ord, Show, Num, Enum)

{- | The index of a variable in the variable list of one problem.

A problem is a symbolic counting problem or a lattice query. Each problem
numbers its variables from zero. An index of one problem has no meaning in
another problem.
-}
newtype VarIndex = VarIndex Int
    deriving newtype (Eq, Ord, Show, Num, Enum)

{- | The zero-based rank of a term or a value in the enumeration order of a
language.

The ranks of one language are stable. The same language gives the same ranks
in every process.
-}
newtype Rank = Rank Integer
    deriving newtype (Eq, Ord, Show, Hashable, Num, Enum)

{- | The number of members of a language, or of a part of a language.

The ranks of a language with cardinality @n@ are @0 .. n - 1@.
-}
newtype Cardinality = Cardinality Integer
    deriving newtype (Eq, Ord, Show, Num, Enum, Real)

-- | The ranks of a language with the given cardinality, from @0@ to @cardinality - 1@.
everyRank :: Cardinality -> [Rank]
everyRank (Cardinality cardinality) = map Rank [0 .. cardinality - 1]
{-# INLINE everyRank #-}

-- | Whether a language with the given cardinality has the rank.
hasRank :: Cardinality -> Rank -> Bool
hasRank (Cardinality cardinality) (Rank rank) = rank >= 0 && rank < cardinality
{-# INLINE hasRank #-}

{- | The rank of a pair in a product language, from the ranks of its two parts.

The rank of the first part is more significant. The radix is the cardinality
of the second part.
-}
pairRank :: Cardinality -> Rank -> Rank -> Rank
pairRank (Cardinality radix) (Rank first) (Rank second) = Rank (first * radix + second)
{-# INLINE pairRank #-}

-- | The ranks of the two parts of a pair in a product language. This is the inverse of 'pairRank'.
splitRank :: Cardinality -> Rank -> (Rank, Rank)
splitRank (Cardinality radix) (Rank rank) = case rank `quotRem` radix of
    (first, second) -> (Rank first, Rank second)
{-# INLINE splitRank #-}

{- | The first rank of a group of members in a larger language.

A group is an alternative of a choice, a size class, or a group of a join.
The groups of a language follow each other in rank order.
-}
newtype RankOffset = RankOffset Integer
    deriving newtype (Eq, Ord, Show, Num, Enum)

-- | The offset of the next group, after a group with the given offset and cardinality.
nextOffset :: RankOffset -> Cardinality -> RankOffset
nextOffset (RankOffset offset) (Cardinality cardinality) = RankOffset (offset + cardinality)
{-# INLINE nextOffset #-}

-- | The rank of a member in the larger language, from its rank in its group.
offsetRank :: RankOffset -> Rank -> Rank
offsetRank (RankOffset offset) (Rank rank) = Rank (offset + rank)
{-# INLINE offsetRank #-}

-- | The rank of a member in its group, from its rank in the larger language. This is the inverse of 'offsetRank'.
rebaseRank :: RankOffset -> Rank -> Rank
rebaseRank (RankOffset offset) (Rank rank) = Rank (rank - offset)
{-# INLINE rebaseRank #-}

{- | The size of a term, or the size of the members of one size class.

The size of a generated member is its number of pays, as in FEAT: a constant
has size zero, an atom has size one, and a constructor adds one. The size of
an accepted term of an automaton is its number of nodes.
-}
newtype Size = Size Integer
    deriving newtype (Eq, Ord, Show, Num, Enum)

{- | The zero-based rank of a member inside its size class.

The members of a size class with @n@ members have the class ranks
@0 .. n - 1@.
-}
newtype ClassRank = ClassRank Integer
    deriving newtype (Eq, Ord, Show, Num, Enum)

-- | The rank of a member, from the first rank of its size class and its rank in the class.
classMemberRank :: RankOffset -> ClassRank -> Rank
classMemberRank (RankOffset offset) (ClassRank classRank) = Rank (offset + classRank)
{-# INLINE classMemberRank #-}

{- | The relative frequency weight of an alternative or a value.

A sampler selects an alternative in proportion to its weight. A weight does
not change a rank or a cardinality.
-}
newtype Weight = Weight Integer
    deriving newtype (Eq, Ord, Show, Num, Enum, Real)

-- | The weight of a group with the given number of members, when each member weighs one.
countWeight :: Cardinality -> Weight
countWeight (Cardinality count) = Weight count
{-# INLINE countWeight #-}
