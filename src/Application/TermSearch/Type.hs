module Application.TermSearch.Type (
    TypeSkeleton (..),
    Argument,
) where

import Data.Data (Data)
import Data.Hashable (Hashable)
import Data.Text (Text)
import GHC.Generics (Generic)

import Data.ECTA
import Data.ECTA.Term

data TypeSkeleton
    = TVar Text
    | TFun TypeSkeleton TypeSkeleton
    | TCons Text [TypeSkeleton]
    deriving (Eq, Ord, Show, Read, Data, Generic)

instance Hashable TypeSkeleton

type Argument = (Symbol, Node)
