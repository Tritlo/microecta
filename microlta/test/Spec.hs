module Main (main) where

import System.Directory (findExecutable)
import System.Exit (die)
import Test.Hspec (hspec)

import qualified Data.LTA.GuardSpec
import qualified Data.LTA.MinimizeSpec
import qualified Data.LTA.PruneSpec
import qualified Data.LTA.RecognitionSpec
import qualified Data.LTA.RecursiveSpec
import qualified Data.LTA.RefinementRelationSpec
import qualified Data.LTA.SubstitutionSpec
import qualified Data.LTA.SyntaxSpec

main :: IO ()
main = do
    z3 <- findExecutable "z3"
    case z3 of
        Nothing -> die "The test suite needs the z3 executable on PATH; enter nix-shell or install Z3."
        Just _ -> pure ()
    hspec $ do
        Data.LTA.GuardSpec.spec
        Data.LTA.RecognitionSpec.spec
        Data.LTA.SubstitutionSpec.spec
        Data.LTA.RecursiveSpec.spec
        Data.LTA.RefinementRelationSpec.spec
        Data.LTA.PruneSpec.spec
        Data.LTA.MinimizeSpec.spec
        Data.LTA.SyntaxSpec.spec
