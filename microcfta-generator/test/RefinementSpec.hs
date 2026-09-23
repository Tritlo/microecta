module Main (main) where

import System.Directory (findExecutable)
import System.Exit (die)
import Test.Hspec (hspec)

import qualified Data.CFTA.Gen.Refinement.BoundedGeneratorSpec
import qualified Data.CFTA.Gen.Refinement.CompileSpec
import qualified Data.CFTA.Gen.Refinement.RecursiveGeneratorSpec

main :: IO ()
main = do
    z3 <- findExecutable "z3"
    case z3 of
        Nothing -> die "The test suite needs the z3 executable on PATH; enter nix-shell or install Z3."
        Just _ -> pure ()
    hspec $ do
        Data.CFTA.Gen.Refinement.CompileSpec.spec
        Data.CFTA.Gen.Refinement.RecursiveGeneratorSpec.spec
        Data.CFTA.Gen.Refinement.BoundedGeneratorSpec.spec
