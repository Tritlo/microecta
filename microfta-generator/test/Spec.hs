module Main (main) where

import qualified Data.Tree.FTA.GenSpec
import qualified Data.Tree.GenSpec
import Test.Hspec (hspec)

main :: IO ()
main = hspec $ do
    Data.Tree.FTA.GenSpec.spec
    Data.Tree.GenSpec.spec
