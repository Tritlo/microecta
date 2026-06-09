{- | Small type language used by the compatibility term-search helpers.

The original @ecta@ package carried a much larger term-search application. In
@microecta@, this module is just the lightweight type skeleton that downstream
projects use before translating types to ECTA nodes with
'Application.TermSearch.Dataset.typeToFta'.
-}
module Application.TermSearch.Type (
    TypeSkeleton (..),
) where

import Data.Data (Data)
import Data.Hashable (Hashable)
import Data.Text (Text)
import GHC.Generics (Generic)

-- | Minimal first-order type syntax.
data TypeSkeleton
    = -- | Type variable.
      TVar Text
    | -- | Function type.
      TFun TypeSkeleton TypeSkeleton
    | -- | Type constructor applied to zero or more arguments.
      TCons Text [TypeSkeleton]
    deriving (Eq, Ord, Show, Read, Data, Generic)

instance Hashable TypeSkeleton
