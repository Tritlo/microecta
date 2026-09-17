module Main (main) where

import Test.Hspec (hspec)

import qualified Application.TermSearchSpec
import qualified Data.ECTA.FTASpec
import qualified Data.Persistent.UnionFindSpec
import qualified ECTASpec
import qualified PathsSpec

main :: IO ()
main =
    hspec $ do
        Application.TermSearchSpec.spec
        Data.Persistent.UnionFindSpec.spec
        Data.ECTA.FTASpec.spec
        ECTASpec.spec
        PathsSpec.spec
