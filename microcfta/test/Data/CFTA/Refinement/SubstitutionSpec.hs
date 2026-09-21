{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.SubstitutionSpec (spec) where

import qualified Data.Tree as Tree
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Refinement (
    Entailment (Entailment),
    Guard (Satisfies, Substitute),
    LiquidConstraint,
    LiquidSymbol (LiquidSymbol),
    Substitution (Substitution),
    Verdict (..),
    evaluateConstraint,
    evaluateGuard,
    path,
 )
import Data.CFTA.Refinement.Expression (false, true, variable, (.<.), (.==.))
import Data.CFTA.Refinement.Guard (buildGuard, isSubtypeOf, withActualFor, withActualsFor)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3, withZ3Assuming)
import qualified Language.Fixpoint.Types as Fixpoint

equalityEntailment :: Entailment
equalityEntailment = Entailment $ \antecedent consequent ->
    pure $ if antecedent == consequent then Yes else No

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
                    Tree.Node
                        ( LiquidSymbol
                            "app"
                            true
                        )
                        [ Tree.Node (LiquidSymbol "result" expected) []
                        , Tree.Node (LiquidSymbol "output" dependent) []
                        , Tree.Node (LiquidSymbol "x" true) []
                        , Tree.Node (LiquidSymbol "n" true) []
                        ]
            evaluateConstraint equalityEntailment dependentGuard term >>= (`shouldBe` Yes)

        it "keeps different actual arguments distinct" $ do
            let expected = variable "v" .==. variable "y"
                dependent = variable "v" .==. variable "n"
                term =
                    Tree.Node
                        ( LiquidSymbol
                            "app"
                            true
                        )
                        [ Tree.Node (LiquidSymbol "result" expected) []
                        , Tree.Node (LiquidSymbol "output" dependent) []
                        , Tree.Node (LiquidSymbol "x" true) []
                        , Tree.Node (LiquidSymbol "n" true) []
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
                    Tree.Node
                        ( LiquidSymbol
                            "binary-app"
                            true
                        )
                        [ Tree.Node (LiquidSymbol "result" expected) []
                        , Tree.Node (LiquidSymbol "output" dependent) []
                        , Tree.Node (LiquidSymbol "x" true) []
                        , Tree.Node (LiquidSymbol "n" true) []
                        , Tree.Node (LiquidSymbol "y" true) []
                        , Tree.Node (LiquidSymbol "m" true) []
                        ]
            evaluateConstraint equalityEntailment guard term >>= (`shouldBe` Yes)

        it "keeps distinct actual values with the same constructor separate" $
            withZ3 declarations $ \solver -> do
                let guard requirement =
                        Substitute
                            [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
                            (Satisfies (path []) requirement)
                evaluateGuard solver (guard false) collidingActuals >>= (`shouldBe` No)
                evaluateGuard solver (guard $ variable "x" .<. variable "y") collidingActuals
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
                            (Satisfies (path []) $ variable "x" .==. variable "y")
                evaluateGuard solver guard collidingActuals >>= (`shouldBe` Yes)

        it "preserves ambient identity for repeated occurrences of one named leaf" $
            withZ3Assuming declarations [variable "x" .==. (7 :: Int)] $ \solver -> do
                let guard requirement =
                        Substitute
                            [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
                            (Satisfies (path []) requirement)
                    term =
                        Tree.Node
                            ( LiquidSymbol
                                "pair"
                                true
                            )
                            [ Tree.Node (LiquidSymbol "x" true) []
                            , Tree.Node (LiquidSymbol "x" true) []
                            , Tree.Node (LiquidSymbol "y" true) []
                            , Tree.Node (LiquidSymbol "z" true) []
                            ]
                evaluateGuard solver (guard $ variable "y" .==. (7 :: Int)) term >>= (`shouldBe` Yes)
                evaluateGuard solver (guard $ variable "y" .==. variable "z") term >>= (`shouldBe` Yes)

        it "applies a swap simultaneously instead of rewriting its replacements" $
            withZ3 declarations $ \solver -> do
                let guard =
                        Substitute
                            [Substitution (path [0]) (path [1]), Substitution (path [1]) (path [0])]
                            (Satisfies (path []) $ variable "x" .==. variable "y")
                    term = Tree.Node (LiquidSymbol "pair" true) [Tree.Node (LiquidSymbol "x" true) [], Tree.Node (LiquidSymbol "y" true) []]
                evaluateGuard solver guard term >>= (`shouldBe` No)

        it "does not swap the value assumptions of actual arguments" $
            withZ3 declarations $ \solver -> do
                let guard =
                        Substitute
                            [Substitution (path [0]) (path [1]), Substitution (path [1]) (path [0])]
                            (Satisfies (path []) $ variable "x" .<. variable "y")
                    term =
                        Tree.Node
                            ( LiquidSymbol
                                "pair"
                                true
                            )
                            [ Tree.Node (LiquidSymbol "x" (variable "v" .==. (0 :: Int))) []
                            , Tree.Node (LiquidSymbol "y" (variable "v" .==. (1 :: Int))) []
                            ]
                evaluateGuard solver guard term >>= (`shouldBe` No)

        it "composes nested scopes from the inner scope to the outer scope" $
            withZ3 declarations $ \solver -> do
                let guard =
                        Substitute [Substitution (path [0]) (path [1])]
                            $ Substitute [Substitution (path [1]) (path [2])]
                            $ Satisfies (path [])
                            $ variable "y" .==. variable "z"
                    term =
                        Tree.Node
                            ( LiquidSymbol
                                "triple"
                                true
                            )
                            [Tree.Node (LiquidSymbol "z" true) [], Tree.Node (LiquidSymbol "x" true) [], Tree.Node (LiquidSymbol "y" true) []]
                evaluateGuard solver guard term >>= (`shouldBe` Yes)

        it "keeps actual refinements in their ambient environment under nested scopes" $
            withZ3Assuming declarations [variable "z" .==. (0 :: Int)] $ \solver -> do
                let guard requirement =
                        Substitute [Substitution (path [0]) (path [1])]
                            $ Substitute [Substitution (path [2]) (path [3])]
                            $ Satisfies (path []) requirement
                    term =
                        Tree.Node
                            ( LiquidSymbol
                                "quadruple"
                                true
                            )
                            [ Tree.Node (LiquidSymbol "x" (variable "v" .==. variable "z")) []
                            , Tree.Node (LiquidSymbol "y" true) []
                            , Tree.Node (LiquidSymbol "w" (variable "v" .==. (1 :: Int))) []
                            , Tree.Node (LiquidSymbol "z" true) []
                            ]
                evaluateGuard solver (guard $ variable "y" .==. variable "w") term >>= (`shouldBe` No)
                evaluateGuard solver (guard $ variable "y" .<. variable "w") term >>= (`shouldBe` Yes)

        it "renames quantified binders instead of capturing the actual variable" $
            withZ3 declarations $ \solver -> do
                let requirement =
                        Fixpoint.PAll [(Fixpoint.symbol ("x" :: String), Fixpoint.FInt)] $
                            variable "y" .==. variable "x"
                    guard =
                        Substitute [Substitution (path [0]) (path [1])] $
                            Satisfies (path []) requirement
                    term = Tree.Node (LiquidSymbol "pair" true) [Tree.Node (LiquidSymbol "x" true) [], Tree.Node (LiquidSymbol "y" true) []]
                evaluateGuard solver guard term >>= (`shouldBe` No)

-- | Sorts for actual variables and constructor result values in these checks.
declarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
declarations = [(Fixpoint.symbol name, Fixpoint.FInt) | name <- ["v", "app", "w", "x", "y", "z"] :: [String]]

-- | Two different applications whose result refinements identify their values.
collidingActuals :: Tree.Tree LiquidSymbol
collidingActuals =
    Tree.Node
        ( LiquidSymbol
            "pair"
            true
        )
        [ Tree.Node (LiquidSymbol "app" (variable "v" .==. (0 :: Int))) [Tree.Node (LiquidSymbol "zero" true) []]
        , Tree.Node (LiquidSymbol "app" (variable "v" .==. (1 :: Int))) [Tree.Node (LiquidSymbol "one" true) []]
        , Tree.Node (LiquidSymbol "x" true) []
        , Tree.Node (LiquidSymbol "y" true) []
        ]
