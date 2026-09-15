module Main (main) where

import System.Directory (findExecutable)
import System.Exit (die)
import Test.Hspec (hspec)

import qualified Data.LTA.BoundedGeneratorSpec
import qualified Data.LTA.DependentApplicationSpec
import qualified Data.LTA.OpaquePoolSpec
import qualified Data.LTA.PreconditionTypedExpressionSpec
import qualified Data.LTA.QuickCheckSyntaxSpec
import qualified Data.LTA.RecursiveGeneratorSpec
import qualified Data.LTA.SafeBufferSpec
import qualified Data.LTA.SimilarityMinimizationSpec
import qualified Data.LTA.SizedVectorSpec
import qualified Data.LTA.StateMachineTraceSpec
import qualified Data.LTA.SubsumptionTypedExpressionSpec

main :: IO ()
main = do
    z3 <- findExecutable "z3"
    case z3 of
        Nothing -> die "The test suite needs the z3 executable on PATH; enter nix-shell or install Z3."
        Just _ -> pure ()
    hspec $ do
        Data.LTA.QuickCheckSyntaxSpec.spec
        Data.LTA.OpaquePoolSpec.spec
        Data.LTA.RecursiveGeneratorSpec.spec
        Data.LTA.BoundedGeneratorSpec.spec
        Data.LTA.SafeBufferSpec.spec
        Data.LTA.PreconditionTypedExpressionSpec.spec
        Data.LTA.SubsumptionTypedExpressionSpec.spec
        Data.LTA.SimilarityMinimizationSpec.spec
        Data.LTA.SizedVectorSpec.spec
        Data.LTA.StateMachineTraceSpec.spec
        Data.LTA.DependentApplicationSpec.spec
