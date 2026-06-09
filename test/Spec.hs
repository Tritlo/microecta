module Main (main) where

import Test.Hspec (hspec)

import qualified Data.Persistent.UnionFindSpec
import qualified ECTASpec
import qualified PathsSpec
import qualified Utility.HashJoinSpec

main :: IO ()
main =
    hspec $ do
        Data.Persistent.UnionFindSpec.spec
        ECTASpec.spec
        PathsSpec.spec
        Utility.HashJoinSpec.spec
