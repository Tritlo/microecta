{- | The specs that decide guards with Z3: pruning, minimization,
substitution, the refinement relation, and the guard checks.
-}
module Main (main) where

import System.Directory (findExecutable)
import System.Exit (die)
import Test.Hspec (hspec)

import qualified Data.CFTA.Refinement.GuardSpec
import qualified Data.CFTA.Refinement.MinimizeSpec
import qualified Data.CFTA.Refinement.PruneSpec
import qualified Data.CFTA.Refinement.RefinementRelationSpec
import qualified Data.CFTA.Refinement.SubstitutionSpec

main :: IO ()
main = do
    z3 <- findExecutable "z3"
    case z3 of
        Nothing -> die "The test suite needs the z3 executable on PATH; enter nix-shell or install Z3."
        Just _ -> pure ()
    hspec $ do
        Data.CFTA.Refinement.GuardSpec.spec
        Data.CFTA.Refinement.SubstitutionSpec.spec
        Data.CFTA.Refinement.RefinementRelationSpec.spec
        Data.CFTA.Refinement.PruneSpec.spec
        Data.CFTA.Refinement.MinimizeSpec.spec
