module Data.LTA.GuardSpec (spec) where

import Test.Hspec (Spec, describe, it, shouldBe)

import Data.LTA (Entailment (Entailment), Guard (Satisfies), LiquidTerm (LiquidTerm), Verdict (..), evaluateGuard, path)
import Data.LTA.Guard (buildGuard, requires)
import Data.LTA.Refinement (true, (.>=.))
import qualified Language.Fixpoint.Types as Fixpoint

-- | A small decidable implication table keeps syntax tests independent of Z3.
tableEntailment :: Entailment
tableEntailment = Entailment $ \antecedent consequent ->
    pure $
        if antecedent == consequent || consequent == true
            then Yes
            else No

value :: Fixpoint.Expr
value = Fixpoint.EVar $ Fixpoint.symbol ("v" :: String)

spec :: Spec
spec =
    describe "LTA guard syntax" $ do
        it "states a literal precondition without a phantom predicate child" $ do
            let nonNegative = value .>=. (0 :: Int)
                guard = buildGuard $ \denominator -> denominator `requires` nonNegative
                term = LiquidTerm "divide" true [LiquidTerm "n" nonNegative []]
            guard `shouldBe` Satisfies (path [0]) nonNegative
            evaluateGuard tableEntailment guard term >>= (`shouldBe` Yes)

        it "rejects a child whose refinement does not establish the requirement" $ do
            let nonNegative = value .>=. (0 :: Int)
                guard = buildGuard $ \denominator -> denominator `requires` nonNegative
                term = LiquidTerm "divide" true [LiquidTerm "n" true []]
            evaluateGuard tableEntailment guard term >>= (`shouldBe` No)
