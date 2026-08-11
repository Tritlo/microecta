module Main (main) where

import Test.Hspec (hspec)

import qualified Data.ECTA.GenSpec
import qualified Data.ECTA.TypedExpressionGenSpec
import qualified Data.Persistent.UnionFindSpec
import qualified ECTASpec
import qualified PathsSpec
import qualified Utility.HashJoinSpec

main :: IO ()
main =
    hspec $ do
        Data.ECTA.GenSpec.spec
        Data.ECTA.TypedExpressionGenSpec.spec
        Data.Persistent.UnionFindSpec.spec
        ECTASpec.spec
        PathsSpec.spec
        Utility.HashJoinSpec.spec
