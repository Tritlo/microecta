module Main (main) where

import Test.Hspec (hspec)

import qualified Data.CFTA.Gen.Equality.DatatypeGenSpec
import qualified Data.CFTA.Gen.Equality.GenSpec
import qualified Data.CFTA.Gen.Equality.IFCExpressionGenSpec
import qualified Data.CFTA.Gen.Equality.RankDecodingSpec
import qualified Data.CFTA.Gen.Equality.RecursiveGenSpec
import qualified Data.CFTA.Gen.Equality.TypedExpressionGenSpec
import qualified Data.CFTA.GenSpec
import qualified Data.CFTA.RankedSpec

main :: IO ()
main =
    hspec $ do
        Data.CFTA.RankedSpec.spec
        Data.CFTA.GenSpec.spec
        Data.CFTA.Gen.Equality.DatatypeGenSpec.spec
        Data.CFTA.Gen.Equality.GenSpec.spec
        Data.CFTA.Gen.Equality.IFCExpressionGenSpec.spec
        Data.CFTA.Gen.Equality.RankDecodingSpec.spec
        Data.CFTA.Gen.Equality.RecursiveGenSpec.spec
        Data.CFTA.Gen.Equality.TypedExpressionGenSpec.spec
