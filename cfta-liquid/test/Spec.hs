{- | The specs of the liquid tree automata: guards, recognition, pruning,
minimization, substitution, the refinement relation, and the lattice
entailment. They decide guards without Z3.
-}
module Main (main) where

import Test.Hspec (hspec)

import qualified Data.CFTA.Refinement.GuardSpec
import qualified Data.CFTA.Refinement.MinimizeSpec
import qualified Data.CFTA.Refinement.PruneSpec
import qualified Data.CFTA.Refinement.RecognitionSpec
import qualified Data.CFTA.Refinement.RecursiveSpec
import qualified Data.CFTA.Refinement.RefinementRelationSpec
import qualified Data.CFTA.Refinement.SimpleSpec
import qualified Data.CFTA.Refinement.SubstitutionSpec
import qualified Data.CFTA.Refinement.SyntaxSpec

main :: IO ()
main =
    hspec $ do
        Data.CFTA.Refinement.GuardSpec.spec
        Data.CFTA.Refinement.RecognitionSpec.spec
        Data.CFTA.Refinement.SubstitutionSpec.spec
        Data.CFTA.Refinement.RecursiveSpec.spec
        Data.CFTA.Refinement.RefinementRelationSpec.spec
        Data.CFTA.Refinement.PruneSpec.spec
        Data.CFTA.Refinement.MinimizeSpec.spec
        Data.CFTA.Refinement.SyntaxSpec.spec
        Data.CFTA.Refinement.SimpleSpec.spec
