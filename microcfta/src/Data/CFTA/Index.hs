{-# LANGUAGE DerivingStrategies #-}

{- | Indexes and counts of terms and automata.

Each value is an 'Int'. An index is zero-based. A count, such as an arity,
starts at zero too. Each kind of index or count has its own newtype, so the
compiler rejects a value of one kind in the place of another kind.
-}
module Data.CFTA.Index (
    ChildIndex (..),
    TransitionIndex (..),
    Arity (..),
    childIndexes,
    Depth (..),
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

{- | The depth of a node in a term, or a bound on that depth.

A leaf has depth 0. The tree automata literature counts a leaf as height 1.
-}
newtype Depth = Depth Int
    deriving newtype (Eq, Ord, Show, Num, Enum)
