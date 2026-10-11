{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.GuardSpec (spec) where

import Control.Exception (IOException, try)
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Refinement (
    Entailment (entails),
    Guard (Entails, Substitute),
    Substitution (Substitution),
    Symbol (RefinedSymbol),
    Verdict (..),
    evaluateGuard,
    path,
 )
import Data.CFTA.Refinement.Expression (false, refinementFormula, toExpr, true, variable, (.&&), (.==), (.>=))
import Data.CFTA.Refinement.LiquidFixpoint (TimeLimitReached (..), withZ3, withZ3Timeout)
import Data.CFTA.Symbol (valueName)
import qualified Data.CFTA.Term as Term
import qualified Language.Fixpoint.Types as Fixpoint

spec :: Spec
spec =
    describe "LTA guard syntax" $ do
        it "connects a substituted node symbol to that node's refinement" $ do
            let model :: Fixpoint.Expr
                model = Fixpoint.EVar $ Fixpoint.symbol ("model" :: String)
                declarations =
                    [ (Fixpoint.symbol name, Fixpoint.FInt)
                    | name <- [valueName, "model", "previous"] :: [String]
                    ]
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
                            , Term.Node (RefinedSymbol "post-state" (refinementFormula (\v -> v .== (toExpr model + 1)))) []
                            ]
                        ]
            withZ3 declarations $ \solver ->
                evaluateGuard solver guard term >>= (`shouldBe` Yes)

        it "answers correctly after the solver rejects a query" $ do
            -- Z3 rejects the assertion that applies the Int constant f, and it
            -- still answers the check-sat. The rejection is an exception. The
            -- next queries go to a new solver process, so each one reads its
            -- own answer, not the answer of the query before it.
            let x = Fixpoint.EVar (Fixpoint.symbol ("x" :: String))
                f = Fixpoint.EVar (Fixpoint.symbol ("f" :: String))
                rejected = Fixpoint.PAtom Fixpoint.Gt (Fixpoint.EApp f x) (Fixpoint.expr (0 :: Int))
                positive = Fixpoint.PAtom Fixpoint.Gt x (Fixpoint.expr (0 :: Int))
                nonNegative = Fixpoint.PAtom Fixpoint.Ge x (Fixpoint.expr (0 :: Int))
            withZ3 [(Fixpoint.symbol ("x" :: String), Fixpoint.FInt), (Fixpoint.symbol ("f" :: String), Fixpoint.FInt)] $ \solver -> do
                rejection <- try (entails solver rejected positive) :: IO (Either IOException Verdict)
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
