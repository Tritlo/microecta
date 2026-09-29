module Main (main) where

import Test.Hspec (hspec)

import qualified Data.CFTA.Equality.ConstraintSpec
import qualified Data.CFTA.Internal.UnionFindSpec

main :: IO ()
main =
    hspec $ do
        Data.CFTA.Internal.UnionFindSpec.spec
        Data.CFTA.Equality.ConstraintSpec.spec
