module Main (main) where

import Test.Hspec (hspec)

import qualified Data.LTA.DependentApplicationSpec
import qualified Data.LTA.PreconditionTypedExpressionSpec
import qualified Data.LTA.QuickCheckSyntaxSpec
import qualified Data.LTA.RecursiveGeneratorSpec
import qualified Data.LTA.SimilarityMinimizationSpec
import qualified Data.LTA.SubsumptionTypedExpressionSpec

main :: IO ()
main =
    hspec $ do
        Data.LTA.QuickCheckSyntaxSpec.spec
        Data.LTA.RecursiveGeneratorSpec.spec
        Data.LTA.PreconditionTypedExpressionSpec.spec
        Data.LTA.SubsumptionTypedExpressionSpec.spec
        Data.LTA.SimilarityMinimizationSpec.spec
        Data.LTA.DependentApplicationSpec.spec
