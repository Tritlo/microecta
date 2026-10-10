{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.SubstitutionSpec (spec) where

import qualified Data.Tree as Tree
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
import Data.CFTA.Refinement.Expression (false, fromExpr, toExpr, true, variable, (.<), (.==))
import Data.CFTA.Refinement.Guard (buildGuard, isSubtypeOf, withActualFor, withActualsFor)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3, withZ3Assuming)
import Data.CFTA.Symbol (valueName)
import qualified Language.Fixpoint.Types as Fixpoint

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
                    Tree.Node
                        ( RefinedSymbol
                            "app"
                            true
                        )
                        [ Tree.Node (RefinedSymbol "result" expected) []
                        , Tree.Node (RefinedSymbol "output" dependent) []
                        , Tree.Node (RefinedSymbol "x" true) []
                        , Tree.Node (RefinedSymbol "n" true) []
                        ]
            evaluateConstraint equalityEntailment dependentGuard term >>= (`shouldBe` Yes)

        it "keeps different actual arguments distinct" $ do
            let expected = variable valueName .== variable "y"
                dependent = variable valueName .== variable "n"
                term =
                    Tree.Node
                        ( RefinedSymbol
                            "app"
                            true
                        )
                        [ Tree.Node (RefinedSymbol "result" expected) []
                        , Tree.Node (RefinedSymbol "output" dependent) []
                        , Tree.Node (RefinedSymbol "x" true) []
                        , Tree.Node (RefinedSymbol "n" true) []
                        ]
            evaluateConstraint equalityEntailment dependentGuard term >>= (`shouldBe` No)

        it "substitutes several actual arguments in one dependent result" $ do
            let expected = variable valueName .== toExpr (Fixpoint.EBin Fixpoint.Plus (fromExpr $ variable "x") (fromExpr $ variable "y"))
                dependent = variable valueName .== toExpr (Fixpoint.EBin Fixpoint.Plus (fromExpr $ variable "n") (fromExpr $ variable "m"))
                guard =
                    buildGuard $ \resultType functionOutput firstActual firstFormal secondActual secondFormal ->
                        withActualsFor
                            [(firstActual, firstFormal), (secondActual, secondFormal)]
                            (functionOutput `isSubtypeOf` resultType)
                term =
                    Tree.Node
                        ( RefinedSymbol
                            "binary-app"
                            true
                        )
                        [ Tree.Node (RefinedSymbol "result" expected) []
                        , Tree.Node (RefinedSymbol "output" dependent) []
                        , Tree.Node (RefinedSymbol "x" true) []
                        , Tree.Node (RefinedSymbol "n" true) []
                        , Tree.Node (RefinedSymbol "y" true) []
                        , Tree.Node (RefinedSymbol "m" true) []
                        ]
            evaluateConstraint equalityEntailment guard term >>= (`shouldBe` Yes)

        it "keeps distinct actual values with the same constructor separate" $
            withZ3 declarations $ \solver -> do
                let guard requirement =
                        Substitute
                            [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
                            (Satisfies (path []) requirement)
                evaluateGuard solver (guard false) collidingActuals >>= (`shouldBe` No)
                evaluateGuard solver (guard $ variable "x" .< variable "y") collidingActuals
                    >>= (`shouldBe` Yes)

        it "reports unsupported fresh declarations to a simple entailment callback" $ do
            let solver = Entailment $ \_ _ -> pure Yes
                guard =
                    Substitute
                        [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
                        (Satisfies (path []) false)
            evaluateGuard solver guard collidingActuals >>= (`shouldBe` Unknown)

        it "uses one actual value when several formals refer to the same position" $
            withZ3 declarations $ \solver -> do
                let guard =
                        Substitute
                            [Substitution (path [0]) (path [2]), Substitution (path [0]) (path [3])]
                            (Satisfies (path []) $ variable "x" .== variable "y")
                evaluateGuard solver guard collidingActuals >>= (`shouldBe` Yes)

        it "preserves ambient identity for repeated occurrences of one named leaf" $
            withZ3Assuming declarations [variable "x" .== 7] $ \solver -> do
                let guard requirement =
                        Substitute
                            [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
                            (Satisfies (path []) requirement)
                    term =
                        Tree.Node
                            ( RefinedSymbol
                                "pair"
                                true
                            )
                            [ Tree.Node (RefinedSymbol "x" true) []
                            , Tree.Node (RefinedSymbol "x" true) []
                            , Tree.Node (RefinedSymbol "y" true) []
                            , Tree.Node (RefinedSymbol "z" true) []
                            ]
                evaluateGuard solver (guard $ variable "y" .== 7) term >>= (`shouldBe` Yes)
                evaluateGuard solver (guard $ variable "y" .== variable "z") term >>= (`shouldBe` Yes)

        it "applies a swap simultaneously instead of rewriting its replacements" $
            withZ3 declarations $ \solver -> do
                let guard =
                        Substitute
                            [Substitution (path [0]) (path [1]), Substitution (path [1]) (path [0])]
                            (Satisfies (path []) $ variable "x" .== variable "y")
                    term = Tree.Node (RefinedSymbol "pair" true) [Tree.Node (RefinedSymbol "x" true) [], Tree.Node (RefinedSymbol "y" true) []]
                evaluateGuard solver guard term >>= (`shouldBe` No)

        it "does not swap the value assumptions of actual arguments" $
            withZ3 declarations $ \solver -> do
                let guard =
                        Substitute
                            [Substitution (path [0]) (path [1]), Substitution (path [1]) (path [0])]
                            (Satisfies (path []) $ variable "x" .< variable "y")
                    term =
                        Tree.Node
                            ( RefinedSymbol
                                "pair"
                                true
                            )
                            [ Tree.Node (RefinedSymbol "x" (variable valueName .== 0)) []
                            , Tree.Node (RefinedSymbol "y" (variable valueName .== 1)) []
                            ]
                evaluateGuard solver guard term >>= (`shouldBe` No)

        it "composes nested scopes from the inner scope to the outer scope" $
            withZ3 declarations $ \solver -> do
                let guard =
                        Substitute [Substitution (path [0]) (path [1])]
                            $ Substitute [Substitution (path [1]) (path [2])]
                            $ Satisfies (path [])
                            $ variable "y" .== variable "z"
                    term =
                        Tree.Node
                            ( RefinedSymbol
                                "triple"
                                true
                            )
                            [Tree.Node (RefinedSymbol "z" true) [], Tree.Node (RefinedSymbol "x" true) [], Tree.Node (RefinedSymbol "y" true) []]
                evaluateGuard solver guard term >>= (`shouldBe` Yes)

        it "keeps actual refinements in their ambient environment under nested scopes" $
            withZ3Assuming declarations [variable "z" .== 0] $ \solver -> do
                let guard requirement =
                        Substitute [Substitution (path [0]) (path [1])]
                            $ Substitute [Substitution (path [2]) (path [3])]
                            $ Satisfies (path []) requirement
                    term =
                        Tree.Node
                            ( RefinedSymbol
                                "quadruple"
                                true
                            )
                            [ Tree.Node (RefinedSymbol "x" (variable valueName .== variable "z")) []
                            , Tree.Node (RefinedSymbol "y" true) []
                            , Tree.Node (RefinedSymbol "w" (variable valueName .== 1)) []
                            , Tree.Node (RefinedSymbol "z" true) []
                            ]
                evaluateGuard solver (guard $ variable "y" .== variable "w") term >>= (`shouldBe` No)
                evaluateGuard solver (guard $ variable "y" .< variable "w") term >>= (`shouldBe` Yes)

        it "renames quantified binders instead of capturing the actual variable" $
            withZ3 declarations $ \solver -> do
                let requirement =
                        Fixpoint.PAll [(Fixpoint.symbol ("x" :: String), Fixpoint.FInt)] $
                            variable "y" .== variable "x"
                    guard =
                        Substitute [Substitution (path [0]) (path [1])] $
                            Satisfies (path []) requirement
                    term = Tree.Node (RefinedSymbol "pair" true) [Tree.Node (RefinedSymbol "x" true) [], Tree.Node (RefinedSymbol "y" true) []]
                evaluateGuard solver guard term >>= (`shouldBe` No)

-- | Sorts for actual variables and constructor result values in these checks.
declarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
declarations = [(Fixpoint.symbol name, Fixpoint.FInt) | name <- [valueName, "app", "w", "x", "y", "z"] :: [String]]

-- | Two different applications whose result refinements identify their values.
collidingActuals :: Tree.Tree Symbol
collidingActuals =
    Tree.Node
        ( RefinedSymbol
            "pair"
            true
        )
        [ Tree.Node (RefinedSymbol "app" (variable valueName .== 0)) [Tree.Node (RefinedSymbol "zero" true) []]
        , Tree.Node (RefinedSymbol "app" (variable valueName .== 1)) [Tree.Node (RefinedSymbol "one" true) []]
        , Tree.Node (RefinedSymbol "x" true) []
        , Tree.Node (RefinedSymbol "y" true) []
        ]
