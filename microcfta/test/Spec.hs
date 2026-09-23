module Main (main) where

import Test.Hspec (hspec)

import qualified Data.CFTA.Equality.ConstraintSpec
import qualified Data.CFTA.Equality.FTASpec
import qualified Data.CFTA.EqualitySpec
import qualified Data.CFTA.Internal.UnionFindSpec
import qualified Data.CFTA.TermSearchSpec
import qualified Data.CFTASpec

main :: IO ()
main =
    hspec $ do
        Data.CFTASpec.spec
        Data.CFTA.Internal.UnionFindSpec.spec
        Data.CFTA.Equality.ConstraintSpec.spec
        Data.CFTA.Equality.FTASpec.spec
        Data.CFTA.EqualitySpec.spec
        Data.CFTA.TermSearchSpec.spec
