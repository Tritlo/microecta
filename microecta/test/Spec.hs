module Main (main) where

import Test.Hspec (hspec)

import qualified Application.TermSearchSpec
import qualified Data.Persistent.UnionFindSpec
import qualified Data.Tree.FTASyntaxSpec
import qualified ECTASpec
import qualified PathsSpec
import qualified Utility.HashJoinSpec

main :: IO ()
main =
    hspec $ do
        Application.TermSearchSpec.spec
        Data.Persistent.UnionFindSpec.spec
        Data.Tree.FTASyntaxSpec.spec
        ECTASpec.spec
        PathsSpec.spec
        Utility.HashJoinSpec.spec
