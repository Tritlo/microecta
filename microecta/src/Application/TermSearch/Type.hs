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
import Data.Hashable (Hashable (..))
import Data.Text (Text)

-- | Minimal first-order type syntax.
data TypeSkeleton
    = -- | Type variable.
      TVar Text
    | -- | Function type.
      TFun TypeSkeleton TypeSkeleton
    | -- | Type constructor applied to zero or more arguments.
      TCons Text [TypeSkeleton]
    deriving (Eq, Ord, Show, Read, Data)

instance Hashable TypeSkeleton where
    hashWithSalt salt (TVar name) =
        salt `hashWithSalt` (0 :: Int) `hashWithSalt` name
    hashWithSalt salt (TFun fromType toType) =
        salt `hashWithSalt` (1 :: Int) `hashWithSalt` fromType `hashWithSalt` toType
    hashWithSalt salt (TCons name args) =
        salt `hashWithSalt` (2 :: Int) `hashWithSalt` name `hashWithSalt` args
