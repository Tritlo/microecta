module Data.LTA.SyntaxSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import Data.LTA (Entailment (Entailment), LiquidTerm (LiquidTerm), State (State), Verdict (..), accepts)
import Data.LTA.Guard (requires, unconstrained)
import Data.LTA.Refinement (true, (.>=.))
import qualified Data.LTA.Syntax as Syntax
import qualified Language.Fixpoint.Types as Fixpoint

value :: Fixpoint.Expr
value = Fixpoint.EVar $ Fixpoint.symbol ("v" :: String)

tableEntailment :: Entailment
tableEntailment = Entailment $ \antecedent consequent ->
    pure $ if antecedent == consequent || consequent == true then Yes else No

spec :: Spec
spec =
    describe "handwritten LTA syntax" $ do
        it "extends the FTA row shape with refinements and named guards" $ do
            let nonNegative = value .>=. (0 :: Int)
            case Syntax.automaton
                (State 0)
                [ Syntax.row
                    (State 0)
                    [ Syntax.transition
                        "sqrt"
                        true
                        [State 1]
                        (\argument -> argument `requires` nonNegative)
                    ]
                , Syntax.row
                    (State 1)
                    [Syntax.transition "zero" nonNegative [] unconstrained]
                ] of
                Left err -> expectationFailure $ show err
                Right automaton ->
                    accepts
                        tableEntailment
                        automaton
                        (LiquidTerm "sqrt" true [LiquidTerm "zero" nonNegative []])
                        >>= (`shouldBe` Yes)
