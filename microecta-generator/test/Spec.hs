module Main (main) where

import Test.Hspec (hspec)

import qualified Data.ECTA.GenSpec
import qualified Data.ECTA.IFCExpressionGenSpec
import qualified Data.ECTA.RecursiveGenSpec
import qualified Data.ECTA.TypedExpressionGenSpec
import qualified Data.Tree.FTA.GenSpec

main :: IO ()
main =
    hspec $ do
        Data.ECTA.GenSpec.spec
        Data.ECTA.IFCExpressionGenSpec.spec
        Data.ECTA.RecursiveGenSpec.spec
        Data.ECTA.TypedExpressionGenSpec.spec
        Data.Tree.FTA.GenSpec.spec
