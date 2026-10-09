{-# LANGUAGE DerivingStrategies #-}

{- | Index types for automata and terms.

Each index is a zero-based 'Int'. Each kind of index has its own newtype, so
the compiler rejects an index of one kind in the place of another kind.
-}
module Data.CFTA.Index (
    ChildIndex (..),
) where

import Data.Hashable (Hashable)

{- | The zero-based index of a child in the children of a transition or a term.

A 'Data.CFTA.Path.Path' is a list of child indexes.
-}
newtype ChildIndex = ChildIndex Int
    deriving newtype (Eq, Ord, Show, Hashable, Num, Enum)
