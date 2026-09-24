{- | Terms, refinements, and the symbols of a liquid tree automaton.

This module carries the vocabulary that both the constraint language and the
automaton structure use. It depends on neither of them.
-}
module Data.CFTA.Refinement.Types (
    Formula,
    eraseRefinements,
    LiquidSymbol (LiquidSymbol),
) where

import Data.Hashable (Hashable (..))
import qualified Data.Tree as Tree
import System.IO.Unsafe (unsafePerformIO)

import Data.CFTA.Interned.Cache (Cache, Id, freshCacheWith, intern, newIdSupply)
import Data.CFTA.Symbol (Symbol)
import qualified Language.Fixpoint.Types as Fixpoint

-- | A logical refinement understood by Liquid Fixpoint.
type Formula = Fixpoint.Expr

-- | Remove refinements to recover the underlying term.
eraseRefinements :: Tree.Tree LiquidSymbol -> Tree.Tree Symbol
eraseRefinements = fmap $ \(LiquidSymbol symbol _) -> symbol

{- | The label carried by one LTA transition or annotated term node.

A label is interned. Equal labels share one identity, so equality compares
identities and hashing reads a hash that was computed once. Ordering compares
the symbol and then the refinement, so it does not depend on the order in
which labels were built.
-}
data LiquidSymbol = InternedLiquidSymbol !Id !Int !Symbol !Formula

{-# COMPLETE LiquidSymbol #-}

-- | Build or match a label from its symbol and its refinement.
pattern LiquidSymbol :: Symbol -> Formula -> LiquidSymbol
pattern LiquidSymbol symbol refinement <- InternedLiquidSymbol _ _ symbol refinement
  where
    LiquidSymbol symbol refinement = intern labels identify (symbol, refinement)

-- | Attach an identity and the structural hash to a new label.
identify :: Id -> (Symbol, Formula) -> LiquidSymbol
identify identity key@(symbol, refinement) = InternedLiquidSymbol identity (hash key) symbol refinement

-- | The process-global table of labels.
labels :: Cache (Symbol, Formula) LiquidSymbol
labels = unsafePerformIO $ freshCacheWith =<< newIdSupply
{-# NOINLINE labels #-}

instance Eq LiquidSymbol where
    InternedLiquidSymbol left _ _ _ == InternedLiquidSymbol right _ _ _ = left == right

instance Ord LiquidSymbol where
    compare (InternedLiquidSymbol left _ leftSymbol leftRefinement) (InternedLiquidSymbol right _ rightSymbol rightRefinement)
        | left == right = EQ
        | otherwise = compare (leftSymbol, leftRefinement) (rightSymbol, rightRefinement)

instance Hashable LiquidSymbol where
    hashWithSalt salt (InternedLiquidSymbol _ structural _ _) = hashWithSalt salt structural

instance Show LiquidSymbol where
    showsPrec precedence (LiquidSymbol symbol refinement) =
        showParen (precedence > 10) $
            showString "LiquidSymbol " . showsPrec 11 symbol . showChar ' ' . showsPrec 11 refinement
