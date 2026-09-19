module Main (main) where

import qualified Data.CFTASpec
import Test.Hspec (hspec)

main :: IO ()
main = hspec Data.CFTASpec.spec
