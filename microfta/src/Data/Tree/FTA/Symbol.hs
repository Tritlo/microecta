{- | Interned symbols for automaton alphabets.

A 'Symbol' is interned text: equality, ordering, and hashing use the interned
identity, so comparing two symbols costs the same whatever their length.
Construct and match symbols with the 'Symbol' pattern or a string literal.
-}
module Data.Tree.FTA.Symbol (Symbol (.., Symbol)) where

import Data.Hashable (Hashable (..))
import qualified Data.Interned as Interned
import Data.Interned.Text (InternedText, internedTextId)
import Data.String (IsString (..))
import Data.Text (Text)
import Text.Read (Read (..))

-- | Interned term or edge symbol.
newtype Symbol = Symbol' InternedText
    deriving (Eq, Ord)

-- | Build or match a symbol from text.
pattern Symbol :: Text -> Symbol
pattern Symbol t <- Symbol' (Interned.unintern -> t)
  where
    Symbol t = Symbol' (Interned.intern t)

{-# COMPLETE Symbol #-}

instance Show Symbol where
    show (Symbol it) = show it

instance Hashable Symbol where
    hashWithSalt s (Symbol' t) = s `hashWithSalt` internedTextId t

instance IsString Symbol where
    fromString = Symbol . fromString

instance Read Symbol where
    readPrec = Symbol <$> readPrec
