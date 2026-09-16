-- | Ordinary first-order trees shared by the tree-automata APIs.
module Data.Tree.Term (Term, pattern Term) where

import Data.Tree (Tree (Node))

{- | A concrete term represented by the standard containers rose tree.

The label and child list are lazy. The type uses the standard 'Tree' instances,
including its 'Read' and 'Show' representation. Import the constructor pattern
with @import Data.Tree.Term (Term, pattern Term)@ and @PatternSynonyms@.
-}
type Term = Tree

-- | Construct or match a term without adding a wrapper or forcing its fields.
pattern Term :: symbol -> [Term symbol] -> Term symbol
pattern Term symbol children = Node symbol children

{-# COMPLETE Term #-}
