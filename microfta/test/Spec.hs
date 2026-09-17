module Main (main) where

import qualified Data.Tree.FTASpec
import Test.Hspec (hspec)

main :: IO ()
main = hspec Data.Tree.FTASpec.spec
