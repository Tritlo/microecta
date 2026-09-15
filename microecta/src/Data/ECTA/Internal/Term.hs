{- | Symbols and concrete terms accepted by ECTAs.

Terms are ordinary first-order trees. They are the concrete values produced by
the enumeration API in "Data.ECTA".
The exports of this internal module are not covered by the PVP contract of
the package.
-}
module Data.ECTA.Internal.Term (
    Symbol (.., Symbol),
    Term (..),
) where

import Data.Hashable (Hashable (..))
import qualified Data.Interned as OrigInterned
import Data.String (IsString (..))
import Data.Text (Text)
import Text.Read (Read (..))

import Data.Interned.Text (InternedText, internedTextId)

import Data.Text.Extended.Pretty
import Data.Tree.Term (Term (..))

---------------------------------------------------------------
-------------------------- Symbols ----------------------------
---------------------------------------------------------------

-- | Interned term or edge symbol.
data Symbol = Symbol' {-# UNPACK #-} !InternedText
    deriving (Eq, Ord)

-- | Build or match a symbol from text.
pattern Symbol :: Text -> Symbol
pattern Symbol t <- Symbol' (OrigInterned.unintern -> t)
  where
    Symbol t = Symbol' (OrigInterned.intern t)

{-# COMPLETE Symbol #-}

instance Pretty Symbol where
    pretty (Symbol t) = t

instance Show Symbol where
    show (Symbol it) = show it

instance Hashable Symbol where
    hashWithSalt s (Symbol' t) = s `hashWithSalt` (internedTextId t)

instance IsString Symbol where
    fromString = Symbol . fromString

instance Read Symbol where
    readPrec = Symbol <$> readPrec
