{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.SubstitutionSpec (spec) where

import Data.String (fromString)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Formula (Name)
import Data.CFTA.Refinement (
    Guard (Satisfies, Substitute),
    Substitution (Substitution),
    Symbol (RefinedSymbol),
    Verdict (..),
    evaluateGuard,
    path,
 )
import Data.CFTA.Refinement.Expression (false, true, variable, (.<), (.==))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3, withZ3Assuming)
import Data.CFTA.Symbol (valueName)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec =
    describe "dependent LTA guards" $ do
        it "keeps distinct actual values with the same constructor separate" $
            withZ3 declarations $ \solver -> do
                let guard requirement =
                        Substitute
                            [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
                            (Satisfies (path []) requirement)
                evaluateGuard solver (guard false) collidingActuals >>= (`shouldBe` No)
                evaluateGuard solver (guard $ variable "x" .< variable "y") collidingActuals
                    >>= (`shouldBe` Yes)

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
                        Term.Node
                            ( RefinedSymbol
                                "pair"
                                true
                            )
                            [ Term.Node (RefinedSymbol "x" true) []
                            , Term.Node (RefinedSymbol "x" true) []
                            , Term.Node (RefinedSymbol "y" true) []
                            , Term.Node (RefinedSymbol "z" true) []
                            ]
                evaluateGuard solver (guard $ variable "y" .== 7) term >>= (`shouldBe` Yes)
                evaluateGuard solver (guard $ variable "y" .== variable "z") term >>= (`shouldBe` Yes)

        it "applies a swap simultaneously instead of rewriting its replacements" $
            withZ3 declarations $ \solver -> do
                let guard =
                        Substitute
                            [Substitution (path [0]) (path [1]), Substitution (path [1]) (path [0])]
                            (Satisfies (path []) $ variable "x" .== variable "y")
                    term = Term.Node (RefinedSymbol "pair" true) [Term.Node (RefinedSymbol "x" true) [], Term.Node (RefinedSymbol "y" true) []]
                evaluateGuard solver guard term >>= (`shouldBe` No)

        it "does not swap the value assumptions of actual arguments" $
            withZ3 declarations $ \solver -> do
                let guard =
                        Substitute
                            [Substitution (path [0]) (path [1]), Substitution (path [1]) (path [0])]
                            (Satisfies (path []) $ variable "x" .< variable "y")
                    term =
                        Term.Node
                            ( RefinedSymbol
                                "pair"
                                true
                            )
                            [ Term.Node (RefinedSymbol "x" (variable valueName .== 0)) []
                            , Term.Node (RefinedSymbol "y" (variable valueName .== 1)) []
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
                        Term.Node
                            ( RefinedSymbol
                                "triple"
                                true
                            )
                            [Term.Node (RefinedSymbol "z" true) [], Term.Node (RefinedSymbol "x" true) [], Term.Node (RefinedSymbol "y" true) []]
                evaluateGuard solver guard term >>= (`shouldBe` Yes)

        it "keeps actual refinements in their ambient environment under nested scopes" $
            withZ3Assuming declarations [variable "z" .== 0] $ \solver -> do
                let guard requirement =
                        Substitute [Substitution (path [0]) (path [1])]
                            $ Substitute [Substitution (path [2]) (path [3])]
                            $ Satisfies (path []) requirement
                    term =
                        Term.Node
                            ( RefinedSymbol
                                "quadruple"
                                true
                            )
                            [ Term.Node (RefinedSymbol "x" (variable valueName .== variable "z")) []
                            , Term.Node (RefinedSymbol "y" true) []
                            , Term.Node (RefinedSymbol "w" (variable valueName .== 1)) []
                            , Term.Node (RefinedSymbol "z" true) []
                            ]
                evaluateGuard solver (guard $ variable "y" .== variable "w") term >>= (`shouldBe` No)
                evaluateGuard solver (guard $ variable "y" .< variable "w") term >>= (`shouldBe` Yes)

-- | Integer names for actual variables and constructor result values in these checks.
declarations :: [Name]
declarations = [fromString valueName, "app", "w", "x", "y", "z"]

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
