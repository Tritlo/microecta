{-# LANGUAGE DeriveGeneric #-}

{- | Terms, refinements, and the scalar names of a liquid tree automaton.

This module carries the vocabulary that both the constraint language and the
automaton structure use. It depends on neither of them.
-}
module Data.LTA.Types (
    Refinement,
    eraseRefinements,
    termAt,
    State (..),
    LiquidSymbol (..),
) where

import Control.Monad (foldM, guard)
import Data.Hashable (Hashable)
import Data.Maybe (listToMaybe)
import qualified Data.Tree as Tree
import GHC.Generics (Generic)

import Data.ECTA.Paths (Path, unPath)
import Data.ECTA.Term (Symbol)
import qualified Language.Fixpoint.Types as Fixpoint

-- | A logical refinement understood by Liquid Fixpoint.
type Refinement = Fixpoint.Expr

-- | Remove refinements to recover the underlying MicroECTA term.
eraseRefinements :: Tree.Tree LiquidSymbol -> Tree.Tree Symbol
eraseRefinements = fmap $ \(LiquidSymbol symbol _) -> symbol

-- | Read the subterm at one position. An absent position gives 'Nothing'.
termAt :: Path -> Tree.Tree LiquidSymbol -> Maybe (Tree.Tree LiquidSymbol)
termAt target term = foldM descend term (unPath target)
  where
    descend node index = do
        guard (index >= 0)
        listToMaybe $ drop index $ Tree.subForest node

-- | An integer identity for one LTA state.
newtype State = State {unState :: Int}
    deriving (Eq, Ord, Show)

-- | The label carried by one LTA transition or annotated term node.
data LiquidSymbol = LiquidSymbol !Symbol !Refinement
    deriving (Eq, Ord, Show, Generic)

instance Hashable LiquidSymbol
