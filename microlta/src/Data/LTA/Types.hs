{-# LANGUAGE DeriveGeneric #-}

{- | Terms, refinements, and the scalar names of a liquid tree automaton.

This module carries the vocabulary that both the constraint language and the
automaton structure use. It depends on neither of them.
-}
module Data.LTA.Types (
    Refinement,
    eraseRefinements,
    State (..),
    LiquidSymbol (..),
) where

import Data.Hashable (Hashable)
import qualified Data.Tree as Tree
import GHC.Generics (Generic)

import Data.CFTA.Symbol (Symbol)
import qualified Language.Fixpoint.Types as Fixpoint

-- | A logical refinement understood by Liquid Fixpoint.
type Refinement = Fixpoint.Expr

-- | Remove refinements to recover the underlying MicroECTA term.
eraseRefinements :: Tree.Tree LiquidSymbol -> Tree.Tree Symbol
eraseRefinements = fmap $ \(LiquidSymbol symbol _) -> symbol

{- | Read the subterm at one position. An absent position gives 'Nothing'.
| An integer identity for one LTA state.
-}
newtype State = State {unState :: Int}
    deriving (Eq, Ord, Show)

-- | The label carried by one LTA transition or annotated term node.
data LiquidSymbol = LiquidSymbol !Symbol !Refinement
    deriving (Eq, Ord, Show, Generic)

instance Hashable LiquidSymbol
