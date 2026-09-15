module Main (main) where

import Test.Hspec (hspec)

import qualified Data.ECTA.DatatypeGenSpec
import qualified Data.ECTA.GenSpec
import qualified Data.ECTA.IFCExpressionGenSpec
import qualified Data.ECTA.RankDecodingSpec
import qualified Data.ECTA.RecursiveGenSpec
import qualified Data.ECTA.TypedExpressionGenSpec

main :: IO ()
main =
    hspec $ do
        Data.ECTA.DatatypeGenSpec.spec
        Data.ECTA.GenSpec.spec
        Data.ECTA.IFCExpressionGenSpec.spec
        Data.ECTA.RankDecodingSpec.spec
        Data.ECTA.RecursiveGenSpec.spec
        Data.ECTA.TypedExpressionGenSpec.spec
