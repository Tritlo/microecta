module Data.ECTA.FTASyntaxSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import qualified Data.ECTA as Core
import qualified Data.ECTA.FTA.Syntax as ECTA
import Data.ECTA.Paths (EqConstraints (EmptyConstraints), mkEqConstraints, path)
import qualified Data.Tree.FTA as Automaton
import qualified Data.Tree.FTA.Interned as Common
import Data.Tree.Term (Term (Term))

data State = Expression | Atom
    deriving (Eq, Ord, Show)

spec :: Spec
spec =
    describe "ECTA transition annotations" $ do
        it "interprets a common equality graph through the public ECTA facade" $ do
            let leaves = Common.Node [Common.Edge "a" [], Common.Edge "b" []]
                graph =
                    Common.Node
                        [Common.mkEdge "pair" [leaves, leaves] (mkEqConstraints [[path [0], path [1]]])]
                ecta = Core.fromInterned graph :: Core.Node String
            Core.toInterned ecta `shouldBe` graph
            Core.nodeRepresents ecta (Term "pair" [Term "a" [], Term "a" []]) `shouldBe` True
            Core.nodeRepresents ecta (Term "pair" [Term "a" [], Term "b" []]) `shouldBe` False

        it "preserves the ECTA display through the common-engine wrapper" $ do
            let edge = Core.Edge "leaf" [] :: Core.Edge String
            show edge `shouldBe` "(Edge \"leaf\" [])"
            show (Core.Node [edge]) `shouldBe` "(Node [(Edge \"leaf\" [])])"
            show (Core.EmptyNode :: Core.Node String) `shouldBe` "EmptyNode"

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
