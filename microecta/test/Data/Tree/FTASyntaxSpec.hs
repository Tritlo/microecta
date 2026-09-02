module Data.Tree.FTASyntaxSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import Data.ECTA.Paths (EqConstraints (EmptyConstraints), mkEqConstraints, path)
import qualified Data.Tree.FTA as FTA
import qualified Data.Tree.FTA.Syntax as Syntax
import Data.Tree.Term (Term (Term))

data State = Expression | Atom
    deriving (Eq, Ord, Show)

spec :: Spec
spec =
    describe "shared FTA construction syntax" $ do
        it "builds an ordinary recursive FTA without unit annotations" $
            case Syntax.automaton
                Expression
                [ Syntax.row
                    Expression
                    [ Syntax.transition "zero" []
                    , Syntax.transition "add" [Expression, Expression]
                    ]
                ] of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    FTA.accepts automaton (Term "zero" []) `shouldBe` True
                    FTA.accepts
                        automaton
                        (Term "add" [Term "zero" [], Term "zero" []])
                        `shouldBe` True

        it "uses the same rows for an ECTA equality annotation" $ do
            let equalChildren = mkEqConstraints [[path [0], path [1]]]
            case Syntax.automaton
                Expression
                [ Syntax.row Expression [Syntax.guarded "pair" [Atom, Atom] equalChildren]
                , Syntax.row Atom [Syntax.guarded "value" [] EmptyConstraints]
                ] of
                Left err -> expectationFailure $ show err
                Right automaton ->
                    map FTA.transitionGuard (FTA.transitionsFrom automaton Expression)
                        `shouldBe` [equalChildren]
