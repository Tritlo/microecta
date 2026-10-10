module Main (main) where

import Test.Hspec (hspec)

import qualified Data.CFTA.Gen.Equality.DatatypeGenSpec
import qualified Data.CFTA.Gen.Equality.GenSpec
import qualified Data.CFTA.Gen.Equality.RankDecodingSpec
import qualified Data.CFTA.Gen.Equality.SimpleSpec
import qualified Data.CFTA.Gen.ReferenceSpec
import qualified Data.CFTA.GenSpec
import qualified Data.CFTA.RankedSpec

main :: IO ()
main =
    hspec $ do
        Data.CFTA.RankedSpec.spec
        Data.CFTA.GenSpec.spec
        Data.CFTA.Gen.Equality.DatatypeGenSpec.spec
        Data.CFTA.Gen.Equality.GenSpec.spec
        Data.CFTA.Gen.Equality.RankDecodingSpec.spec
        Data.CFTA.Gen.Equality.SimpleSpec.spec
        Data.CFTA.Gen.ReferenceSpec.spec
