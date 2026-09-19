module Main (main) where

import System.Directory (findExecutable)
import System.Exit (die)
import Test.Hspec (hspec)

import qualified Data.CFTA.Equality.ConstraintsSpec
import qualified Data.CFTA.Equality.FTASpec
import qualified Data.CFTA.EqualitySpec
import qualified Data.CFTA.Example.TermSearchSpec
import qualified Data.CFTA.Internal.UnionFindSpec
import qualified Data.CFTA.Refinement.GuardSpec
import qualified Data.CFTA.Refinement.MinimizeSpec
import qualified Data.CFTA.Refinement.PruneSpec
import qualified Data.CFTA.Refinement.RecognitionSpec
import qualified Data.CFTA.Refinement.RecursiveSpec
import qualified Data.CFTA.Refinement.RefinementRelationSpec
import qualified Data.CFTA.Refinement.SubstitutionSpec
import qualified Data.CFTA.Refinement.SyntaxSpec
import qualified Data.CFTASpec

main :: IO ()
main = do
    z3 <- findExecutable "z3"
    case z3 of
        Nothing -> die "The test suite needs the z3 executable on PATH; enter nix-shell or install Z3."
        Just _ -> pure ()
    hspec $ do
        Data.CFTASpec.spec
        Data.CFTA.Internal.UnionFindSpec.spec
        Data.CFTA.Equality.ConstraintsSpec.spec
        Data.CFTA.Equality.FTASpec.spec
        Data.CFTA.EqualitySpec.spec
        Data.CFTA.Example.TermSearchSpec.spec
        Data.CFTA.Refinement.GuardSpec.spec
        Data.CFTA.Refinement.RecognitionSpec.spec
        Data.CFTA.Refinement.SubstitutionSpec.spec
        Data.CFTA.Refinement.RecursiveSpec.spec
        Data.CFTA.Refinement.RefinementRelationSpec.spec
        Data.CFTA.Refinement.PruneSpec.spec
        Data.CFTA.Refinement.MinimizeSpec.spec
        Data.CFTA.Refinement.SyntaxSpec.spec
