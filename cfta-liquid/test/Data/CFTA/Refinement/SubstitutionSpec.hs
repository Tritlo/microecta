{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.SubstitutionSpec (spec) where

import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Refinement (
    Constraint,
    Entailment (Entailment),
    Guard (Satisfies, Substitute),
    Substitution (Substitution),
    Symbol (RefinedSymbol),
    Verdict (..),
    evaluateConstraint,
    evaluateGuard,
    path,
 )
import Data.CFTA.Refinement.Expression (false, true, variable, (.==))
import Data.CFTA.Refinement.Guard (buildGuard, isSubtypeOf, withActualFor, withActualsFor)
import Data.CFTA.Symbol (valueName)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

equalityEntailment :: Entailment
equalityEntailment = Entailment $ \antecedent consequent ->
    pure $ if antecedent == consequent then Yes else No

dependentGuard :: Constraint
dependentGuard =
    buildGuard $ \resultType functionOutput actual formal ->
        withActualFor actual formal $
            functionOutput `isSubtypeOf` resultType

spec :: Spec
spec =
    describe "dependent LTA guards" $ do
        it "substitutes the actual argument for the formal in the result type" $ do
            let expected = variable valueName .== variable "x"
                dependent = variable valueName .== variable "n"
                term =
                    Term.Node
                        ( RefinedSymbol
                            "app"
                            true
                        )
                        [ Term.Node (RefinedSymbol "result" expected) []
                        , Term.Node (RefinedSymbol "output" dependent) []
                        , Term.Node (RefinedSymbol "x" true) []
                        , Term.Node (RefinedSymbol "n" true) []
                        ]
            evaluateConstraint equalityEntailment dependentGuard term >>= (`shouldBe` Yes)

        it "keeps different actual arguments distinct" $ do
            let expected = variable valueName .== variable "y"
                dependent = variable valueName .== variable "n"
                term =
                    Term.Node
                        ( RefinedSymbol
                            "app"
                            true
                        )
                        [ Term.Node (RefinedSymbol "result" expected) []
                        , Term.Node (RefinedSymbol "output" dependent) []
                        , Term.Node (RefinedSymbol "x" true) []
                        , Term.Node (RefinedSymbol "n" true) []
                        ]
            evaluateConstraint equalityEntailment dependentGuard term >>= (`shouldBe` No)

        it "substitutes several actual arguments in one dependent result" $ do
            let expected = variable valueName .== variable "x" + variable "y"
                dependent = variable valueName .== variable "n" + variable "m"
                guard =
                    buildGuard $ \resultType functionOutput firstActual firstFormal secondActual secondFormal ->
                        withActualsFor
                            [(firstActual, firstFormal), (secondActual, secondFormal)]
                            (functionOutput `isSubtypeOf` resultType)
                term =
                    Term.Node
                        ( RefinedSymbol
                            "binary-app"
                            true
                        )
                        [ Term.Node (RefinedSymbol "result" expected) []
                        , Term.Node (RefinedSymbol "output" dependent) []
                        , Term.Node (RefinedSymbol "x" true) []
                        , Term.Node (RefinedSymbol "n" true) []
                        , Term.Node (RefinedSymbol "y" true) []
                        , Term.Node (RefinedSymbol "m" true) []
                        ]
            evaluateConstraint equalityEntailment guard term >>= (`shouldBe` Yes)

        it "reports unsupported fresh declarations to a simple entailment callback" $ do
            let solver = Entailment $ \_ _ -> pure Yes
                guard =
                    Substitute
                        [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
                        (Satisfies (path []) false)
            evaluateGuard solver guard collidingActuals >>= (`shouldBe` Unknown)

-- | Two different applications whose result refinements identify their values.
collidingActuals :: Term Symbol
collidingActuals =
    Term.Node
        ( RefinedSymbol
            "pair"
            true
        )
        [ Term.Node (RefinedSymbol "app" (variable valueName .== 0)) [Term.Node (RefinedSymbol "zero" true) []]
        , Term.Node (RefinedSymbol "app" (variable valueName .== 1)) [Term.Node (RefinedSymbol "one" true) []]
        , Term.Node (RefinedSymbol "x" true) []
        , Term.Node (RefinedSymbol "y" true) []
        ]
