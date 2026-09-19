module Data.LTA.SyntaxSpec (spec) where

import Data.Either (rights)
import Data.Tree (flatten)
import qualified Data.Tree as Tree

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA.Interned as Common
import Data.LTA (AutomatonError (GuardArityMismatch), LiquidSymbol (LiquidSymbol), State (State), Verdict (..), accepts)
import qualified Data.LTA as LTA
import Data.LTA.Guard (isSubtypeOf, requires, unconstrained)
import Data.LTA.Refinement (true, value, (.>=.))
import qualified Data.LTA.Syntax as Syntax
import Data.LTA.TestSupport (tableEntailment)

spec :: Spec
spec =
    describe "handwritten LTA syntax" $ do
        it "reports a named guard with the wrong number of arguments" $ do
            let automaton =
                    Syntax.automaton
                        (State 0)
                        [ Syntax.row
                            (State 0)
                            [Syntax.transition "wrap" true [State 1] (\actual expected -> actual `isSubtypeOf` expected)]
                        , Syntax.row (State 1) [Syntax.transition "leaf" true [] unconstrained]
                        ]
            automaton `shouldBe` Left (GuardArityMismatch "wrap" 1 2)

        it "extends the FTA row shape with refinements and named guards" $ do
            let nonNegative = value .>=. (0 :: Int)
            case Syntax.automaton
                (State 0)
                [ Syntax.row
                    (State 0)
                    [ Syntax.transition
                        "sqrt"
                        true
                        [State 1]
                        (`requires` nonNegative)
                    ]
                , Syntax.row
                    (State 1)
                    [Syntax.transition "zero" nonNegative [] unconstrained]
                ] of
                Left err -> expectationFailure $ show err
                Right automaton ->
                    accepts
                        tableEntailment
                        automaton
                        (Tree.Node (LiquidSymbol "sqrt" true) [Tree.Node (LiquidSymbol "zero" nonNegative) []])
                        >>= (`shouldBe` Yes)

        it "interprets entailments retained by the common interned engine" $ do
            let nonNegative = value .>=. (0 :: Int)
                alternatives =
                    Common.Node
                        [ Common.Edge (LTA.LiquidSymbol "zero" nonNegative) []
                        , Common.Edge (LTA.LiquidSymbol "unknown" true) []
                        ]
                root =
                    Common.Node
                        [ Common.mkEdge
                            (LTA.LiquidSymbol "check" true)
                            [alternatives, alternatives]
                            (LTA.semanticConstraint $ LTA.Entails (LTA.path [0]) (LTA.path [1]))
                        ]
                terms =
                    [ Tree.Node (LiquidSymbol "check" true) [left, right]
                    | left <- [Tree.Node (LiquidSymbol "zero" nonNegative) [], Tree.Node (LiquidSymbol "unknown" true) []]
                    , right <- [Tree.Node (LiquidSymbol "zero" nonNegative) [], Tree.Node (LiquidSymbol "unknown" true) []]
                    ]
            case LTA.fromInterned root of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    let edges = rights $ flatten $ LTA.toTree automaton
                    [(LTA.transitionSymbol edge, LTA.transitionRefinement edge) | edge <- edges]
                        `shouldSatisfy` elem ("zero", nonNegative)
                    map (LTA.constraintAsGuard . LTA.transitionConstraint) edges
                        `shouldSatisfy` elem (LTA.Entails (LTA.path [0]) (LTA.path [1]))
                    mapM (accepts tableEntailment automaton) terms
                        >>= (`shouldBe` [Yes, Yes, No, Yes])
                    LTA.denotationAtMost tableEntailment 1 automaton
                        >>= (`shouldBe` Right (map (terms !!) [0, 1, 3]))

        it "validates recursive guard paths after interned construction" $ do
            let root = Common.Mu $ \self ->
                    Common.Node
                        [ Common.mkEdge
                            (LTA.LiquidSymbol "loop" true)
                            [self]
                            (LTA.semanticConstraint $ LTA.Satisfies (LTA.path [0]) true)
                        ]
            case LTA.fromInterned root of
                Left (LTA.InvalidLiquidAutomaton (LTA.CyclicGuardReference _ target)) ->
                    target `shouldBe` LTA.path [0]
                other -> expectationFailure $ show other

        it "rejects free recursive references in an interned LTA" $
            LTA.fromInterned (Common.Rec $ Common.RecUnint 0)
                `shouldBe` Left (LTA.InvalidInternedGraph Common.OpenNode)
