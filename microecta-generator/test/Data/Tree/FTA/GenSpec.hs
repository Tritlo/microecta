{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE QualifiedDo #-}

module Data.Tree.FTA.GenSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import qualified Test.QuickCheck as QC

import qualified Data.Tree.FTA as Automaton
import qualified Data.Tree.FTA.Gen.QuickCheck as FTA
import qualified Data.Tree.FTA.UntypedExpressionLanguage as Expressions
import Data.Tree.Term (Term (Term))

atoms :: FTA.FTAGen String Int
atoms =
    case FTA.oneof [FTA.leaf "zero" 0, FTA.leaf "one" 1] of
        Left err -> error $ show err
        Right generator -> generator

pairs :: FTA.FTAGen String (Int, Int)
pairs = FTA.node "pair" $ FTA.do
    left <- atoms
    right <- atoms
    FTA.pure (left, right)

spec :: Spec
spec = do
    describe "ordinary FTA generator syntax" $ do
        it "uses each do binding as one direct constructor child" $ do
            FTA.cardinality pairs `shouldBe` 4
            FTA.generatedTerm pairs 2
                `shouldBe` Right (Term "pair" [Term "one" [], Term "zero" []])

        it "builds exact support carrying the public node labels" $
            case FTA.support pairs of
                Left err -> expectationFailure $ show err
                Right support -> do
                    Automaton.accepts support (Term "pair" [Term "zero" [], Term "one" []])
                        `shouldBe` True
                    Automaton.accepts support (Term "pair" [Term "zero" []])
                        `shouldBe` False

    describe "ordinary FTA integer expressions" $ do
        it "has the exact structural cardinality at every bounded depth" $
            map (FTA.cardinality . Expressions.expressionsAtDepth) [0 .. 4]
                `shouldBe` map Expressions.expressionCount [0 .. 4]

        it "generates executable expressions without type-side conditions" $ do
            let expressions = Expressions.expressionsAtDepth 2
                generated =
                    [ expression
                    | rank <- [0 .. FTA.cardinality expressions - 1]
                    , Right expression <- [FTA.unrank expressions rank]
                    ]
            generated `shouldSatisfy` all ((>= 0) . Expressions.evaluate)

        modifyMaxSuccess (const 500) $
            it "keeps both reference generators in the exact-depth language" $
                QC.conjoin
                    [ QC.forAll (generator 3) $ \expression ->
                        QC.counterexample (show expression) $
                            expressionDepth expression QC.=== 3
                    | generator <-
                        [ Expressions.naiveExpressionGen
                        , Expressions.handwrittenExpressionGen
                        ]
                    ]

-- | Number of constructor layers in an untyped expression.
expressionDepth :: Expressions.Expression -> Int
expressionDepth (Expressions.Literal _) = 0
expressionDepth (Expressions.Add left right) =
    1 + max (expressionDepth left) (expressionDepth right)
expressionDepth (Expressions.Multiply left right) =
    1 + max (expressionDepth left) (expressionDepth right)
