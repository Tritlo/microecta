module Data.LTA.SubstitutionSpec (spec) where

import Test.Hspec (Spec, describe, it, shouldBe)

import Data.LTA (
    Entailment (Entailment),
    LiquidConstraint,
    LiquidTerm (LiquidTerm),
    Verdict (..),
    evaluateConstraint,
 )
import Data.LTA.Guard (buildGuard, isSubtypeOf, withActualFor, withActualsFor)
import Data.LTA.Refinement (true, (.==.))
import qualified Language.Fixpoint.Types as Fixpoint

equalityEntailment :: Entailment
equalityEntailment = Entailment $ \antecedent consequent ->
    pure $ if antecedent == consequent then Yes else No

variable :: String -> Fixpoint.Expr
variable = Fixpoint.EVar . Fixpoint.symbol

dependentGuard :: LiquidConstraint
dependentGuard =
    buildGuard $ \resultType functionOutput actual formal ->
        withActualFor actual formal $
            functionOutput `isSubtypeOf` resultType

spec :: Spec
spec =
    describe "dependent LTA guards" $ do
        it "substitutes the actual argument for the formal in the result type" $ do
            let expected = variable "v" .==. variable "x"
                dependent = variable "v" .==. variable "n"
                term =
                    LiquidTerm
                        "app"
                        true
                        [ LiquidTerm "result" expected []
                        , LiquidTerm "output" dependent []
                        , LiquidTerm "x" true []
                        , LiquidTerm "n" true []
                        ]
            evaluateConstraint equalityEntailment dependentGuard term >>= (`shouldBe` Yes)

        it "keeps different actual arguments distinct" $ do
            let expected = variable "v" .==. variable "y"
                dependent = variable "v" .==. variable "n"
                term =
                    LiquidTerm
                        "app"
                        true
                        [ LiquidTerm "result" expected []
                        , LiquidTerm "output" dependent []
                        , LiquidTerm "x" true []
                        , LiquidTerm "n" true []
                        ]
            evaluateConstraint equalityEntailment dependentGuard term >>= (`shouldBe` No)

        it "substitutes several actual arguments in one dependent result" $ do
            let expected = variable "v" .==. Fixpoint.EBin Fixpoint.Plus (variable "x") (variable "y")
                dependent = variable "v" .==. Fixpoint.EBin Fixpoint.Plus (variable "n") (variable "m")
                guard =
                    buildGuard $ \resultType functionOutput firstActual firstFormal secondActual secondFormal ->
                        withActualsFor
                            [(firstActual, firstFormal), (secondActual, secondFormal)]
                            (functionOutput `isSubtypeOf` resultType)
                term =
                    LiquidTerm
                        "binary-app"
                        true
                        [ LiquidTerm "result" expected []
                        , LiquidTerm "output" dependent []
                        , LiquidTerm "x" true []
                        , LiquidTerm "n" true []
                        , LiquidTerm "y" true []
                        , LiquidTerm "m" true []
                        ]
            evaluateConstraint equalityEntailment guard term >>= (`shouldBe` Yes)
