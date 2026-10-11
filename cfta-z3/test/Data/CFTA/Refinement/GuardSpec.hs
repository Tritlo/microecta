{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.GuardSpec (spec) where

import Control.Exception (IOException, try)
import Data.String (fromString)
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Refinement (
    Entailment (entails),
    Guard (Entails, Substitute),
    Substitution (Substitution),
    Symbol (RefinedSymbol),
    Verdict (..),
    entailsWithBindings,
    evaluateGuard,
    path,
 )
import Data.CFTA.Refinement.Expression (false, refinementFormula, true, variable, (.&&), (.==), (.>), (.>=))
import Data.CFTA.Refinement.LiquidFixpoint (TimeLimitReached (..), withZ3, withZ3Timeout)
import Data.CFTA.Symbol (valueName)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec =
    describe "LTA guard syntax" $ do
        it "connects a substituted node symbol to that node's refinement" $ do
            let declarations = [fromString valueName, "model", "previous"]
                guard =
                    Substitute
                        [Substitution (path [0]) (path [1, 0])]
                        (Entails (path [1, 1]) (path []))
                term =
                    Term.Node
                        ( RefinedSymbol
                            "step"
                            (refinementFormula (\v -> v .== 1))
                        )
                        [ Term.Node (RefinedSymbol "previous" (refinementFormula (\v -> v .== 0))) []
                        , Term.Node
                            ( RefinedSymbol
                                "command"
                                true
                            )
                            [ Term.Node (RefinedSymbol "model" true) []
                            , Term.Node (RefinedSymbol "post-state" (refinementFormula (\v -> v .== (variable "model" + 1)))) []
                            ]
                        ]
            withZ3 declarations $ \solver ->
                evaluateGuard solver guard term >>= (`shouldBe` Yes)

        it "answers correctly after the solver rejects a query" $ do
            -- The query binds the fresh name twice, so it declares that name
            -- twice. Z3 rejects the second declaration, and it still answers
            -- the check-sat. The rejection is an exception. The next queries
            -- go to a new solver process, so each one reads its own answer,
            -- not the answer of the query before it.
            let x = variable "x"
                positive = x .> 0
                nonNegative = x .>= 0
                twice = [("fresh", "x"), ("fresh", "x")]
            withZ3 ["x"] $ \solver -> do
                rejection <- try (entailsWithBindings solver twice positive positive) :: IO (Either IOException Verdict)
                either (const True) (const False) rejection `shouldBe` True
                results <- mapM (uncurry $ entails solver) [(positive, nonNegative), (nonNegative, positive), (positive, nonNegative)]
                results `shouldBe` [Yes, No, Yes]

        it "answers correctly after a query is interrupted" $ do
            -- An interrupted query can leave its answer unread in the solver
            -- process. The next query goes to a new process, so it reads its
            -- own answer. The waits cover interruptions before the query is
            -- sent, while Z3 runs, and after it answers.
            let v = variable valueName
            withZ3 [] $ \solver -> do
                answers <-
                    mapM
                        ( \micros -> do
                            _ <- timeout micros (entails solver (v .== 0) (v .>= 0))
                            entails solver (v .== 0) (v .== 1)
                        )
                        [1, 5, 20, 50, 100, 200, 500, 1000, 2000, 5000]
                answers `shouldBe` replicate 10 No

        it "raises TimeLimitReached when a query reaches the time limit" $ do
            -- Z3 did not decide this query about cubes in five minutes, so a
            -- limit of 200 milliseconds stops it. The next query still gets
            -- its own answer.
            let x = variable "x"
                y = variable "y"
                z = variable "z"
                cubes = x .>= 1 .&& y .>= 1 .&& z .>= 1 .&& x * x * x + y * y * y .== z * z * z
            withZ3Timeout 200 [] [] $ \solver -> do
                reached <- try (entails solver cubes false)
                reached `shouldBe` (Left (TimeLimitReached 200) :: Either TimeLimitReached Verdict)
                entails solver (x .>= 1) (x .>= 0) >>= (`shouldBe` Yes)
