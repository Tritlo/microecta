{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.RecursiveSpec (spec) where

import qualified Data.Tree as Tree
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import Data.CFTA.Refinement (
    Automaton,
    AutomatonError (CyclicGuardReference),
    Entailment (Entailment),
    Guard (Satisfies),
    LiquidSymbol (LiquidSymbol),
    Node (Mu, Node),
    Verdict (Yes),
    accepts,
    path,
    semanticConstraint,
    unconstrainedConstraint,
    validate,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (true)

alwaysEntails :: Entailment
alwaysEntails = Entailment $ \_ _ -> pure Yes

recursiveLists :: Automaton
recursiveLists = Mu $ \list ->
    Node
        [ Transition "nil" true [] unconstrainedConstraint
        , Transition "cons" true [item, list] unconstrainedConstraint
        ]
  where
    item = Node [Transition "item" true [] unconstrainedConstraint]

spec :: Spec
spec =
    describe "recursive LTAs" $ do
        it "accepts cyclic languages when guards do not inspect the cycle" $ do
            let item = Tree.Node (LiquidSymbol "item" true) []
                nil = Tree.Node (LiquidSymbol "nil" true) []
                list = Tree.Node (LiquidSymbol "cons" true) [item, Tree.Node (LiquidSymbol "cons" true) [item, nil]]
            validate recursiveLists `shouldBe` Right ()
            accepts alwaysEntails recursiveLists list >>= (`shouldBe` Yes)

        it "allows a guard to inspect an acyclic sibling of a recursive child" $ do
            let checked = Node [Transition "checked" true [] unconstrainedConstraint]
                automaton = Mu $ \self ->
                    Node [Transition "wrap" true [self, checked] (semanticConstraint $ Satisfies (path [1]) true)]
            validate automaton `shouldBe` Right ()

        it "rejects a guard that points into a recursive node" $ do
            let automaton = Mu $ \self ->
                    Node [Transition "loop" true [self] (semanticConstraint $ Satisfies (path [0]) true)]
            case validate automaton of
                Left (CyclicGuardReference _ target) -> target `shouldBe` path [0]
                other -> expectationFailure $ show other
