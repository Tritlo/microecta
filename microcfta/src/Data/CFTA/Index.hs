{-# LANGUAGE DerivingStrategies #-}

{- | Indexes and depths of terms and automata.

Each value is an 'Int'. An index is zero-based, and a leaf has depth 0. Each
kind of value has its own newtype, so the compiler rejects a value of one kind
in the place of another kind.
-}
module Data.CFTA.Index (
    ChildIndex (..),
    TransitionIndex (..),
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

{- | The depth of a node in a term, or a bound on that depth.

A leaf has depth 0. The tree automata literature counts a leaf as height 1.
-}
newtype Depth = Depth Int
    deriving newtype (Eq, Ord, Show, Num, Enum)
