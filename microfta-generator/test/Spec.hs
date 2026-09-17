module Main (main) where

import qualified Data.RankedSpec
import qualified Data.Tree.FTA.GenSpec
import Test.Hspec (hspec)

main :: IO ()
main = hspec $ do
    Data.Tree.FTA.GenSpec.spec
    Data.RankedSpec.spec
