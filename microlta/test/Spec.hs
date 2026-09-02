module Main (main) where

import Test.Hspec (hspec)

import qualified Data.LTA.GuardSpec
import qualified Data.LTA.RecognitionSpec
import qualified Data.LTA.RecursiveSpec
import qualified Data.LTA.SemanticsSpec
import qualified Data.LTA.SubstitutionSpec
import qualified Data.LTA.SyntaxSpec

main :: IO ()
main =
    hspec $ do
        Data.LTA.GuardSpec.spec
        Data.LTA.RecognitionSpec.spec
        Data.LTA.SubstitutionSpec.spec
        Data.LTA.RecursiveSpec.spec
        Data.LTA.SemanticsSpec.spec
        Data.LTA.SyntaxSpec.spec
