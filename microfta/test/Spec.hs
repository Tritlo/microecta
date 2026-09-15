module Main (main) where

import qualified Data.Tree.FTASyntaxSpec
import Test.Hspec (hspec)

main :: IO ()
main = hspec Data.Tree.FTASyntaxSpec.spec
