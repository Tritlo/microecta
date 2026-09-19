module Data.ECTA.FTASpec (spec) where

import Data.Tree (flatten)
import qualified Data.Tree as Tree

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as Automaton
import qualified Data.CFTA.Interned as Common
import qualified Data.ECTA as Core
import Data.ECTA.Paths (EqConstraints (EmptyConstraints), mkEqConstraints, path)

data State = Expression | Atom
    deriving (Eq, Ord, Show)

spec :: Spec
spec =
    describe "ECTA transition annotations" $ do
        it "interprets a common equality graph through the public ECTA facade" $ do
            let leaves = Common.Node [Common.Edge "a" [], Common.Edge "b" []]
                equalChildren = mkEqConstraints [[path [0], path [1]]]
                graph =
                    Common.Node
                        [Common.mkEdge "pair" [leaves, leaves] equalChildren]
                ecta = Core.fromInterned graph :: Core.Node String
            Core.toInterned ecta `shouldBe` graph
            Core.nodeRepresents ecta (Tree.Node "pair" [Tree.Node "a" [], Tree.Node "a" []]) `shouldBe` True
            Core.nodeRepresents ecta (Tree.Node "pair" [Tree.Node "a" [], Tree.Node "b" []]) `shouldBe` False
            case Core.toTree ecta of
                Left err -> expectationFailure $ show err
                Right tree ->
                    [Core.edgeEcs edge | Right edge <- flatten tree]
                        `shouldSatisfy` elem equalChildren

        it "preserves the ECTA display through the common-engine wrapper" $ do
            let edge = Core.Edge "leaf" [] :: Core.Edge String
            show edge `shouldBe` "(Edge \"leaf\" [])"
            show (Core.Node [edge]) `shouldBe` "(Node [(Edge \"leaf\" [])])"
            show (Core.EmptyNode :: Core.Node String) `shouldBe` "EmptyNode"

        it "uses the same rows for an ECTA equality annotation" $ do
            let equalChildren = mkEqConstraints [[path [0], path [1]]]
            case Automaton.mkFTA
                Expression
                [ (Expression, [Automaton.Transition "pair" [Atom, Atom] equalChildren])
                , (Atom, [Automaton.Transition "value" [] EmptyConstraints])
                ] of
                Left err -> expectationFailure $ show err
                Right automaton ->
                    map Automaton.transitionGuard (Automaton.transitionsFrom automaton Expression)
                        `shouldBe` [equalChildren]
