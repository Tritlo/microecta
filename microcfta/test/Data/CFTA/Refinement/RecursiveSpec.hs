{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.RecursiveSpec (spec) where

import qualified Data.Tree as Tree
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import Data.CFTA.Refinement (
    Automaton,
    AutomatonError (CyclicGuardReference),
    Entailment (Entailment),
    Guard (Same, Satisfies),
    Node (Mu, Node),
    Symbol (RefinedSymbol),
    Verdict (Yes),
    accepts,
    noConstraint,
    path,
    prune,
    semanticConstraint,
    validate,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (true)

alwaysEntails :: Entailment
alwaysEntails = Entailment $ \_ _ -> pure Yes

recursiveLists :: Automaton
recursiveLists = Mu $ \list ->
    Node
        [ Transition "nil" true [] noConstraint
        , Transition "cons" true [item, list] noConstraint
        ]
  where
    item = Node [Transition "item" true [] noConstraint]

spec :: Spec
spec =
    describe "recursive LTAs" $ do
        it "accepts cyclic languages when guards do not inspect the cycle" $ do
            let item = Tree.Node (RefinedSymbol "item" true) []
                nil = Tree.Node (RefinedSymbol "nil" true) []
                list = Tree.Node (RefinedSymbol "cons" true) [item, Tree.Node (RefinedSymbol "cons" true) [item, nil]]
            validate recursiveLists `shouldBe` Right ()
            accepts alwaysEntails recursiveLists list >>= (`shouldBe` Yes)

        it "allows a guard to inspect an acyclic sibling of a recursive child" $ do
            let checked = Node [Transition "checked" true [] noConstraint]
                automaton = Mu $ \self ->
                    Node [Transition "wrap" true [self, checked] (semanticConstraint $ Satisfies (path [1]) true)]
            validate automaton `shouldBe` Right ()

        it "prunes a guard that reads a position through the recursive reference" $ do
            let leaf = Node [Transition "a" true [] noConstraint]
                automaton = Mu $ \self ->
                    Node
                        [ Transition "g" true [leaf] noConstraint
                        , Transition "f" true [leaf, self] (semanticConstraint $ Satisfies (path [1, 0]) true)
                        ]
                a = Tree.Node (RefinedSymbol "a" true) []
                term = Tree.Node (RefinedSymbol "f" true) [a, Tree.Node (RefinedSymbol "g" true) [a]]
            validate automaton `shouldBe` Right ()
            pruned <- timeout 10000000 $ prune alwaysEntails automaton
            case pruned of
                Just (Right result) -> accepts alwaysEntails result term >>= (`shouldBe` Yes)
                other -> expectationFailure $ show other

        it "prunes an equality that reads a position through the recursive reference" $ do
            let leaf = Node [Transition "a" true [] noConstraint]
                automaton = Mu $ \self ->
                    Node
                        [ Transition "g" true [leaf] noConstraint
                        , Transition "f" true [leaf, self] (semanticConstraint $ Same (path [0]) (path [1, 0]))
                        ]
                a = Tree.Node (RefinedSymbol "a" true) []
                term = Tree.Node (RefinedSymbol "f" true) [a, Tree.Node (RefinedSymbol "g" true) [a]]
            validate automaton `shouldBe` Right ()
            pruned <- timeout 10000000 $ prune alwaysEntails automaton
            case pruned of
                Just (Right result) -> accepts alwaysEntails result term >>= (`shouldBe` Yes)
                other -> expectationFailure $ show other

        it "prunes an equality that reaches the recursive reference through an inner recursive node" $ do
            let leaf = Node [Transition "a" true [] noConstraint]
                automaton = Mu $ \self ->
                    Node
                        [ Transition "g" true [leaf] noConstraint
                        , Transition
                            "f"
                            true
                            [leaf, Mu $ \inner -> Node [Transition "h" true [inner, self] noConstraint, Transition "b" true [] noConstraint]]
                            (semanticConstraint $ Same (path [0]) (path [1, 1, 0]))
                        ]
                a = Tree.Node (RefinedSymbol "a" true) []
                term =
                    Tree.Node
                        (RefinedSymbol "f" true)
                        [a, Tree.Node (RefinedSymbol "h" true) [Tree.Node (RefinedSymbol "b" true) [], Tree.Node (RefinedSymbol "g" true) [a]]]
            validate automaton `shouldBe` Right ()
            pruned <- timeout 10000000 $ prune alwaysEntails automaton
            case pruned of
                Just (Right result) -> accepts alwaysEntails result term >>= (`shouldBe` Yes)
                other -> expectationFailure $ show other

        it "rejects a guard that points into a recursive node" $ do
            let automaton = Mu $ \self ->
                    Node [Transition "loop" true [self] (semanticConstraint $ Satisfies (path [0]) true)]
            case validate automaton of
                Left (CyclicGuardReference _ target) -> target `shouldBe` path [0]
                other -> expectationFailure $ show other
