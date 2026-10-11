module Main (main) where

import Test.Hspec (hspec)

import qualified Data.CFTA.Equality.ConstraintSpec
import qualified Data.CFTA.Equality.FTASpec
import qualified Data.CFTA.EqualitySpec
import qualified Data.CFTA.Refinement.GuardSpec
import qualified Data.CFTA.Refinement.MinimizeSpec
import qualified Data.CFTA.Refinement.PruneSpec
import qualified Data.CFTA.Refinement.RecognitionSpec
import qualified Data.CFTA.Refinement.RecursiveSpec
import qualified Data.CFTA.Refinement.RefinementRelationSpec
import qualified Data.CFTA.Refinement.SimpleSpec
import qualified Data.CFTA.Refinement.SubstitutionSpec
import qualified Data.CFTA.Refinement.SyntaxSpec
import qualified Data.CFTA.SimpleSpec
import qualified Data.CFTA.SymbolSpec
import qualified Data.CFTA.TermSearchSpec
import qualified Data.CFTASpec

main :: IO ()
main =
    hspec $ do
        Data.CFTASpec.spec
        Data.CFTA.Equality.ConstraintSpec.spec
        Data.CFTA.Equality.FTASpec.spec
        Data.CFTA.EqualitySpec.spec
        Data.CFTA.TermSearchSpec.spec
        Data.CFTA.Refinement.GuardSpec.spec
        Data.CFTA.Refinement.RecognitionSpec.spec
        Data.CFTA.Refinement.SubstitutionSpec.spec
        Data.CFTA.Refinement.RecursiveSpec.spec
        Data.CFTA.Refinement.RefinementRelationSpec.spec
        Data.CFTA.Refinement.PruneSpec.spec
        Data.CFTA.Refinement.MinimizeSpec.spec
        Data.CFTA.Refinement.SyntaxSpec.spec
        Data.CFTA.SymbolSpec.spec
        Data.CFTA.SimpleSpec.spec
        Data.CFTA.Refinement.SimpleSpec.spec
