{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Minimal pretty-printing class that produces strict 'Text'.
module Data.Text.Extended.Pretty (
    Pretty (..),
) where

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Tree as Tree

----------------------------------------------------------------------

-- | Convert a value to human-readable strict 'Text'.
class Pretty a where
    -- | Render a value.
    pretty :: a -> Text

instance {-# OVERLAPPABLE #-} (Show a) => Pretty a where
    pretty = Text.pack . show

instance (Pretty symbol) => Pretty (Tree.Tree symbol) where
    pretty (Tree.Node s []) = pretty s
    pretty (Tree.Node s ts) = pretty s <> "(" <> Text.intercalate ", " (map pretty ts) <> ")"
