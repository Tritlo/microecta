{-# LANGUAGE DeriveGeneric #-}

{- | Terms, refinements, and the scalar names of a liquid tree automaton.

This module carries the vocabulary that both the constraint language and the
automaton structure use. It depends on neither of them.
-}
module Data.LTA.Types (
    Refinement,
    LiquidTerm (..),
    eraseRefinements,
    termAt,
    State (..),
    LiquidSymbol (..),
) where

import Data.Hashable (Hashable)
import GHC.Generics (Generic)

import Data.ECTA.Paths (Path, unPath)
import Data.ECTA.Term (Symbol, Term (Term))
import qualified Language.Fixpoint.Types as Fixpoint

-- | A logical refinement understood by Liquid Fixpoint.
type Refinement = Fixpoint.Expr

-- | A concrete first-order term annotated with one refinement at every node.
data LiquidTerm = LiquidTerm
    { liquidSymbol :: !Symbol
    , liquidRefinement :: !Refinement
    , liquidChildren :: ![LiquidTerm]
    }
    deriving (Eq, Show)

-- | Remove refinements to recover the underlying MicroECTA term.
eraseRefinements :: LiquidTerm -> Term Symbol
eraseRefinements LiquidTerm{liquidSymbol, liquidChildren} =
    Term liquidSymbol (map eraseRefinements liquidChildren)

-- | Read the subterm at one position. An absent position gives 'Nothing'.
termAt :: Path -> LiquidTerm -> Maybe LiquidTerm
termAt target = go (unPath target)
  where
    go [] term = Just term
    go (index : rest) LiquidTerm{liquidChildren}
        | index < 0 = Nothing
        | otherwise = case drop index liquidChildren of
            child : _ -> go rest child
            [] -> Nothing

-- | An integer identity for one LTA state.
newtype State = State {unState :: Int}
    deriving (Eq, Ord, Show)

-- | The ranked alphabet label carried by one LTA transition.
data LiquidSymbol = LiquidSymbol !Symbol !Refinement
    deriving (Eq, Ord, Show, Generic)

instance Hashable LiquidSymbol
