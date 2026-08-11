module Main (main) where

import Test.Hspec (hspec)

import qualified Data.ECTA.GenSpec
import qualified Data.ECTA.RecursiveGenSpec
import qualified Data.ECTA.TypedExpressionGenSpec

main :: IO ()
main =
    hspec $ do
        Data.ECTA.GenSpec.spec
        Data.ECTA.RecursiveGenSpec.spec
        Data.ECTA.TypedExpressionGenSpec.spec
