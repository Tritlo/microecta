-- | Ordinary first-order trees shared by the tree-automata APIs.
module Data.Tree.Term (Term (..)) where

import Data.Hashable (Hashable (..))

{- | A concrete first-order term over an arbitrary symbol alphabet.

'fmap' changes the alphabet without changing the tree's shape.
-}
data Term symbol = Term !symbol ![Term symbol]
    deriving (Eq, Ord, Read, Show)

instance Functor Term where
    fmap f (Term symbol children) = Term (f symbol) (map (fmap f) children)

instance (Hashable symbol) => Hashable (Term symbol) where
    hashWithSalt salt (Term symbol children) =
        salt `hashWithSalt` symbol `hashWithSalt` children
