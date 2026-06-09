{-# LANGUAGE UndecidableInstances #-}

-- | Minimal pretty-printing class that produces strict 'Text'.
module Data.Text.Extended.Pretty (
    Pretty (..),
) where

import Data.Text (Text)
import qualified Data.Text as Text

----------------------------------------------------------------------

-- | Convert a value to human-readable strict 'Text'.
class Pretty a where
    -- | Render a value.
    pretty :: a -> Text

instance {-# OVERLAPPABLE #-} (Show a) => Pretty a where
    pretty = Text.pack . show
