{-# LANGUAGE DerivingStrategies #-}

{- | Interned symbols for automaton alphabets.

A 'Symbol' is a text and a refinement: a Liquid Fixpoint formula about the
value of the term node that the symbol labels. An ordinary symbol has the
refinement 'Fixpoint.PTrue'. A liquid tree automaton labels a transition with
a refined symbol, such as an integer constructor whose value is three.

Symbols are interned. Equal symbols share one identity, so equality compares
identities and hashing reads a hash that was computed once. Ordering compares
the texts and then the refinements, so it does not depend on the order in which
the process interned the symbols. Construct and match an ordinary symbol with
the 'Symbol' pattern or a string literal, and a refined one with 'RefinedSymbol'.
-}
module Data.CFTA.Symbol (
    Symbol (Symbol, RefinedSymbol),
    Formula,
    symbolText,
    symbolRefinement,
    unrefined,
    eraseRefinements,
    liquidOrder,
) where

import Data.Hashable (Hashable (..))
import Data.String (IsString (..))
import Data.Text (Text)
import qualified Data.Tree as Tree
import qualified Language.Fixpoint.Types as Fixpoint
import System.IO.Unsafe (unsafePerformIO)
import Text.Read (Read (..))

import Data.CFTA.Interned.Cache (Cache, freshCacheWith, intern, newIdSupply)

-- | A logical refinement understood by Liquid Fixpoint.
type Formula = Fixpoint.Expr

{- | The identity of an interned symbol.

The interning cache gives each new symbol a fresh identity. Equal symbols have
one identity, so equality compares identities.
-}
newtype SymbolId = SymbolId Int
    deriving newtype (Eq)

{- | An interned text and refinement, with the ordinary symbol of the text:
the symbol itself when it is ordinary. The ordinary symbol is found once, when
it is first read, so that reading it again allocates nothing.
-}
data Symbol = InternedSymbol !SymbolId !Int !Text !Formula Symbol

{- | An ordinary symbol of a text. As a pattern, it matches every symbol and
gives its text; the refinement is not part of the match.
-}
pattern Symbol :: Text -> Symbol
pattern Symbol text <- InternedSymbol _ _ text _ _
  where
    Symbol text = internSymbol text Fixpoint.PTrue

{-# COMPLETE Symbol #-}

{- | A refined symbol: an ordinary symbol and a refinement. As a pattern, it
matches every symbol and gives the ordinary symbol of its text and its
refinement. Building one uses only the text of the given symbol, so a
refinement that the given symbol has is replaced, not conjoined.
-}
pattern RefinedSymbol :: Symbol -> Formula -> Symbol
pattern RefinedSymbol symbol refinement <- (refinedView -> (symbol, refinement))
  where
    RefinedSymbol symbol refinement = internSymbol (symbolText symbol) refinement

{-# COMPLETE RefinedSymbol #-}

-- | The ordinary symbol and the refinement of a symbol.
refinedView :: Symbol -> (Symbol, Formula)
refinedView symbol = (unrefined symbol, symbolRefinement symbol)

-- | The text of a symbol.
symbolText :: Symbol -> Text
symbolText (InternedSymbol _ _ text _ _) = text

-- | The refinement of a symbol; 'Fixpoint.PTrue' for an ordinary symbol.
symbolRefinement :: Symbol -> Formula
symbolRefinement (InternedSymbol _ _ _ refinement _) = refinement

-- | The ordinary symbol of the same text.
unrefined :: Symbol -> Symbol
unrefined (InternedSymbol _ _ _ _ ordinary) = ordinary

-- | Remove the refinements of a term.
eraseRefinements :: Tree.Tree Symbol -> Tree.Tree Symbol
eraseRefinements = fmap unrefined

-- | Order constructors of equal arity by symbol text and refinement, not by interning order.
liquidOrder :: Symbol -> (Text, Formula)
liquidOrder (RefinedSymbol (Symbol name) refinement) = (name, refinement)
{-# INLINE liquidOrder #-}

-- | Intern one text and refinement.
internSymbol :: Text -> Formula -> Symbol
internSymbol text refinement = intern symbols identify (text, refinement)
  where
    identify identity key = symbol
      where
        symbol = InternedSymbol (SymbolId identity) (hash key) text refinement ordinary
        ordinary
            | refinement == Fixpoint.PTrue = symbol
            | otherwise = Symbol text

-- | The process-global table of symbols.
symbols :: Cache (Text, Formula) Symbol
symbols = unsafePerformIO $ freshCacheWith =<< newIdSupply
{-# NOINLINE symbols #-}

instance Eq Symbol where
    InternedSymbol left _ _ _ _ == InternedSymbol right _ _ _ _ = left == right

-- | Text order, then refinement order. Equal identities skip the comparison.
instance Ord Symbol where
    compare (InternedSymbol left _ leftText leftRefinement _) (InternedSymbol right _ rightText rightRefinement _)
        | left == right = EQ
        | otherwise = compare leftText rightText <> compare leftRefinement rightRefinement

instance Hashable Symbol where
    hashWithSalt salt (InternedSymbol _ structural _ _ _) = hashWithSalt salt structural

-- | An ordinary symbol shows as its text; a refined one also shows its refinement.
instance Show Symbol where
    showsPrec precedence symbol@(InternedSymbol _ _ text refinement _)
        | refinement == Fixpoint.PTrue = showsPrec precedence text
        | otherwise =
            showParen (precedence > 10) $
                showString "RefinedSymbol " . showsPrec 11 (unrefined symbol) . showChar ' ' . showsPrec 11 refinement

instance IsString Symbol where
    fromString = Symbol . fromString

instance Read Symbol where
    readPrec = Symbol <$> readPrec
