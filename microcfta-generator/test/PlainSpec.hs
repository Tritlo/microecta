module Main (main) where

import qualified Data.CFTA.GenSpec
import qualified Data.CFTA.RankedSpec
import Test.Hspec (hspec)

main :: IO ()
main = hspec $ do
    Data.CFTA.GenSpec.spec
    Data.CFTA.RankedSpec.spec
