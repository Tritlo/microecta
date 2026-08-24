{-# LANGUAGE OverloadedStrings #-}

{- | Symbols and concrete terms accepted by ECTAs.

Terms are ordinary first-order trees. They are the concrete values produced by
the enumeration API in "Data.ECTA".
-}
module Data.ECTA.Internal.Term (
    Symbol (.., Symbol),
    Term (..),
) where

import Data.Hashable (Hashable (..))
import qualified Data.Interned as OrigInterned
import Data.Maybe (maybeToList)
import Data.String (IsString (..))
import Data.Text (Text)
import qualified Data.Text as Text
import Text.Read (Read (..))

import Data.Interned.Text (InternedText, internedTextId)

import Data.ECTA.Paths
import Data.Text.Extended.Pretty
import Utility.List (adjustAt, atMay)

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

---------------------------------------------------------------
---------------------------- Terms ----------------------------
---------------------------------------------------------------

-- | Concrete first-order term over an arbitrary symbol alphabet.
data Term symbol = Term !symbol ![Term symbol]
    deriving (Eq, Ord, Read, Show)

instance (Hashable symbol) => Hashable (Term symbol) where
    hashWithSalt salt (Term symbol children) =
        salt `hashWithSalt` symbol `hashWithSalt` children

instance (Pretty symbol) => Pretty (Term symbol) where
    pretty (Term s []) = pretty s
    pretty (Term s ts) = pretty s <> "(" <> (Text.intercalate ", " $ map pretty ts) <> ")"

---------------------
------ Term ops
---------------------

instance Pathable (Term symbol) (Term symbol) where
    type Emptyable (Term symbol) = Maybe (Term symbol)

    getPath EmptyPath t = Just t
    getPath (ConsPath p ps) (Term _ ts) = case atMay p ts of
        Nothing -> Nothing
        Just t -> getPath ps t

    getAllAtPath p t = maybeToList $ getPath p t

    modifyAtPath f EmptyPath t = f t
    modifyAtPath f (ConsPath p ps) (Term s ts) = Term s (adjustAt p (modifyAtPath f ps) ts)
