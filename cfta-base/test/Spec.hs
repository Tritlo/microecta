module Main (main) where

import Test.Hspec (hspec)

import qualified Data.CFTA.IndexSpec
import qualified Data.CFTA.Internal.TreeSpec
import qualified Data.CFTA.Internal.UnionFindSpec
import qualified Data.CFTA.TermSpec

main :: IO ()
main = hspec $ do
    Data.CFTA.IndexSpec.spec
    Data.CFTA.TermSpec.spec
    Data.CFTA.Internal.TreeSpec.spec
    Data.CFTA.Internal.UnionFindSpec.spec
