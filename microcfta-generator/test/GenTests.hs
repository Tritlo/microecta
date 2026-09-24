module Main (main) where

import Test.Hspec (hspec)

import qualified Data.CFTA.GenSpec
import qualified Data.CFTA.RankedSpec

main :: IO ()
main =
    hspec $ do
        Data.CFTA.RankedSpec.spec
        Data.CFTA.GenSpec.spec
