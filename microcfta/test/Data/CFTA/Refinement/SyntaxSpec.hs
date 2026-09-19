{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.SyntaxSpec (spec) where

import qualified Data.Set as Set
import qualified Data.Tree as Tree

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldMatchList, shouldSatisfy)

import Data.CFTA.Refinement (
    AutomatonError (CyclicGuardReference, GuardArityMismatch, OpenAutomaton),
    Guard (Entails, Satisfies),
    LiquidSymbol (LiquidSymbol),
    Node (Mu, Node, Rec),
    RecNodeId (RecUnint),
    Verdict (..),
    accepts,
    automatonAlphabet,
    constraintAsGuard,
    denotationAtMost,
    mkEdge,
    nodeEdges,
    path,
    semanticConstraint,
    transitionConstraint,
    unconstrainedConstraint,
    validate,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (true, value, (.>=.))
import Data.CFTA.Refinement.Guard (automaton, isSubtypeOf, requires, transition, unconstrained)
import Data.CFTA.Refinement.TestSupport (tableEntailment)

spec :: Spec
spec =
    describe "named guards and validation" $ do
        it "reports a named guard with the wrong number of arguments" $ do
            let leaf = Node [Transition "leaf" true [] unconstrainedConstraint]
            automaton [transition "wrap" true [leaf] (\actual expected -> actual `isSubtypeOf` expected)]
                `shouldBe` Left (GuardArityMismatch "wrap" 1 2)

        it "builds transitions from refinements and named guards" $ do
            let nonNegative = value .>=. (0 :: Int)
                built = do
                    zero <- automaton [transition "zero" nonNegative [] unconstrained]
                    automaton [transition "sqrt" true [zero] (`requires` nonNegative)]
            case built of
                Left err -> expectationFailure $ show err
                Right root ->
                    accepts
                        tableEntailment
                        root
                        (Tree.Node (LiquidSymbol "sqrt" true) [Tree.Node (LiquidSymbol "zero" nonNegative) []])
                        >>= (`shouldBe` Yes)

        it "interprets entailments carried by interned edges" $ do
            let nonNegative = value .>=. (0 :: Int)
                alternatives =
                    Node
                        [ Transition "zero" nonNegative [] unconstrainedConstraint
                        , Transition "unknown" true [] unconstrainedConstraint
                        ]
                root =
                    Node
                        [ mkEdge
                            (LiquidSymbol "check" true)
                            [alternatives, alternatives]
                            (semanticConstraint $ Entails (path [0]) (path [1]))
                        ]
                terms =
                    [ Tree.Node (LiquidSymbol "check" true) [left, right]
                    | left <- [Tree.Node (LiquidSymbol "zero" nonNegative) [], Tree.Node (LiquidSymbol "unknown" true) []]
                    , right <- [Tree.Node (LiquidSymbol "zero" nonNegative) [], Tree.Node (LiquidSymbol "unknown" true) []]
                    ]
            validate root `shouldBe` Right ()
            automatonAlphabet root `shouldSatisfy` Set.member (LiquidSymbol "zero" nonNegative)
            map (constraintAsGuard . transitionConstraint) (nodeEdges root)
                `shouldBe` [Entails (path [0]) (path [1])]
            mapM (accepts tableEntailment root) terms
                >>= (`shouldBe` [Yes, Yes, No, Yes])
            denotationAtMost tableEntailment 1 root
                >>= either (expectationFailure . show) (`shouldMatchList` map (terms !!) [0, 1, 3])

        it "rejects a guard position inside a recursive node" $ do
            let root = Mu $ \self ->
                    Node
                        [ mkEdge
                            (LiquidSymbol "loop" true)
                            [self]
                            (semanticConstraint $ Satisfies (path [0]) true)
                        ]
            case validate root of
                Left (CyclicGuardReference _ target) -> target `shouldBe` path [0]
                other -> expectationFailure $ show other

        it "rejects free recursive references" $
            validate (Rec $ RecUnint 0) `shouldBe` Left OpenAutomaton
