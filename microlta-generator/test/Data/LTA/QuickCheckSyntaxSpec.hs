module Data.LTA.QuickCheckSyntaxSpec (spec) where

import Test.Hspec (Spec, describe, it, shouldBe)

import Data.LTA (Guard (Entails, Satisfies), path, semanticConstraint)
import Data.LTA.Guard (argument, buildGuard, isSubtypeOf, refines, requires)
import Data.LTA.TypedExpressionLanguage (nonNegative)

spec :: Spec
spec =
    describe "QuickCheck-facing LTA syntax" $ do
        it "turns named lambda arguments into paths without magic indices" $
            buildGuard (\actual expected -> actual `isSubtypeOf` expected)
                `shouldBe` semanticConstraint (Entails (path [0]) (path [1]))

        it "keeps explicit positions as a programmatic escape hatch" $
            argument 0 `refines` argument 1
                `shouldBe` buildGuard (\actual expected -> actual `isSubtypeOf` expected)

        it "states ordinary preconditions in the vocabulary of a property writer" $
            buildGuard (\candidate -> candidate `requires` nonNegative)
                `shouldBe` semanticConstraint (Satisfies (path [0]) nonNegative)
