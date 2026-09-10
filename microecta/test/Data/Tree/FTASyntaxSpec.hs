module Data.Tree.FTASyntaxSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import qualified Data.ECTA.FTA.Syntax as ECTA
import Data.ECTA.Paths (EqConstraints (EmptyConstraints), mkEqConstraints, path)
import qualified Data.Tree.FTA as Automaton
import qualified Data.Tree.FTA.Syntax as FTA
import Data.Tree.Term (Term (Term))

data State = Expression | Atom
    deriving (Eq, Ord, Show)

spec :: Spec
spec =
    describe "shared FTA construction syntax" $ do
        it "builds an ordinary recursive FTA without unit annotations" $
            case FTA.automaton
                Expression
                [ FTA.row
                    Expression
                    [ FTA.transition "zero" []
                    , FTA.transition "add" [Expression, Expression]
                    ]
                ] of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    Automaton.accepts automaton (Term "zero" []) `shouldBe` True
                    Automaton.accepts
                        automaton
                        (Term "add" [Term "zero" [], Term "zero" []])
                        `shouldBe` True

        it "uses the same rows for an ECTA equality annotation" $ do
            let equalChildren = mkEqConstraints [[path [0], path [1]]]
            case ECTA.automaton
                Expression
                [ ECTA.row Expression [ECTA.transition "pair" [Atom, Atom] equalChildren]
                , ECTA.row Atom [ECTA.transition "value" [] EmptyConstraints]
                ] of
                Left err -> expectationFailure $ show err
                Right automaton ->
                    map Automaton.transitionGuard (Automaton.transitionsFrom automaton Expression)
                        `shouldBe` [equalChildren]

        it "constructs the ordinary product intersection" $ do
            let left =
                    FTA.automaton
                        Expression
                        [FTA.row Expression [FTA.transition "left" [], FTA.transition "shared" []]]
                right =
                    FTA.automaton
                        Expression
                        [FTA.row Expression [FTA.transition "shared" [], FTA.transition "right" []]]
            case (left, right) of
                (Right leftAutomaton, Right rightAutomaton) ->
                    case Automaton.intersect leftAutomaton rightAutomaton of
                        Left err -> expectationFailure $ show err
                        Right intersection -> do
                            let ordinary = Automaton.stripGuards intersection
                            Automaton.accepts ordinary (Term "shared" []) `shouldBe` True
                            Automaton.accepts ordinary (Term "left" []) `shouldBe` False
                            Automaton.accepts ordinary (Term "right" []) `shouldBe` False
                (Left err, _) -> expectationFailure $ show err
                (_, Left err) -> expectationFailure $ show err
