{-# LANGUAGE DerivingStrategies #-}

{- | The symbols of a generator's support graph.

The equality engine builds its support over the user's symbols and over
private labels of its own: the applicative spine, choices, source indexes,
joins, keys, and recursive families. 'Label' keeps the two apart in one
symbol type, so a support cannot collide with a user symbol and the engine
reserves no names.
-}
module Data.CFTA.Gen.Label (
    Label (..),
    ChoiceIndex (..),
    ComponentIndex (..),
    GroupIndex (..),
    KeyIndex (..),
    surface,
) where

import Data.Hashable (Hashable)
import qualified Data.Tree as Tree
import GHC.Generics (Generic)

import Data.CFTA.Index (ArgumentIndex, Rank)
import Data.CFTA.Ranked.Internal.Size (ChoiceIndex (..))

-- | A user symbol, or one private label of the generator engine.
data Label symbol
    = -- | A user symbol: a constructor closed with @node@, or one read from an imported automaton.
      Label symbol
    | -- | The nullary applicative identity, @pure@.
      Pure
    | -- | One applicative step: the function language and the argument language.
      Apply
    | -- | One alternative of a choice, by position.
      Choice !ChoiceIndex
    | -- | One member of a finite source, by rank.
      Index !Rank
    | -- | A two-way join: the two keyed sides under one equality constraint.
      Join
    | -- | An n-way join: the keyed operation and its keyed arguments.
      JoinN
    | -- | The operation of an n-way join, with one key per argument position.
      CenterKeyed
    | -- | The left side of a two-way join, with its key.
      LeftKeyed
    | -- | The right side of a two-way join, with its key.
      RightKeyed
    | -- | One argument of an n-way join, with its key.
      ArgKeyed
    | -- | One key-labelled alternative of a recursive family.
      Family
    | -- | A recursive family restricted to one key.
      AtKey
    | -- | The key of one family member, by its index among the keys of the family.
      Key !KeyIndex
    | -- | The key of one matched group of a two-way join, by its index.
      Group !GroupIndex
    | -- | The key of one argument position of one joined component.
      ArgKey !ComponentIndex !ArgumentIndex
    | -- | A placeholder leaf that a theory fills with a value when it compiles.
      Placeholder
    deriving (Eq, Ord, Show, Generic)

instance (Hashable symbol) => Hashable (Label symbol)

{- | The zero-based index of a component of an n-way join.

A component is one operation signature of an application, or one accepted
key pair of a relation. The argument keys of a component carry its index, so
the keys of two components differ.
-}
newtype ComponentIndex = ComponentIndex Int
    deriving newtype (Eq, Ord, Show, Hashable, Num, Enum)

{- | The zero-based index of a matched group of a two-way join.

A matched group holds the outcomes of one left key and one right key that
the join accepts. The groups follow each other in rank order.
-}
newtype GroupIndex = GroupIndex Int
    deriving newtype (Eq, Ord, Show, Hashable, Num, Enum)

-- | The zero-based index of a key among the keys of a recursive family, in ascending key order.
newtype KeyIndex = KeyIndex Int
    deriving newtype (Eq, Ord, Show, Hashable, Num, Enum)

{- | The user's term under a labelled term.

Every 'Label' node is kept, and every private node is flattened into its
parent's children. A term whose root is private surfaces as a forest, and a
private leaf surfaces as nothing.
-}
surface :: Tree.Tree (Label symbol) -> [Tree.Tree symbol]
surface (Tree.Node (Label symbol) children) = [Tree.Node symbol $ concatMap surface children]
surface (Tree.Node _ children) = concatMap surface children
