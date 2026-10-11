{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.RecursiveSpec (spec) where

import System.Timeout (timeout)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import Data.CFTA.Refinement (
    Automaton,
    Entailment (Entailment),
    Guard (Same, Satisfies),
    Node (Mu, Node),
    Symbol (RefinedSymbol),
    Verdict (No, Yes),
    accepts,
    noConstraint,
    path,
    prune,
    semanticConstraint,
    validate,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (true)
import qualified Data.CFTA.Term as Term

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
            let item = Term.Node (RefinedSymbol "item" true) []
                nil = Term.Node (RefinedSymbol "nil" true) []
                list = Term.Node (RefinedSymbol "cons" true) [item, Term.Node (RefinedSymbol "cons" true) [item, nil]]
            validate recursiveLists `shouldBe` Right ()
            accepts alwaysEntails recursiveLists list >>= (`shouldBe` Yes)

        it "allows a guard to inspect an acyclic sibling of a recursive child" $ do
            let checked = Node [Transition "checked" true [] noConstraint]
                automaton = Mu $ \self ->
                    Node [Transition "wrap" true [self, checked] (semanticConstraint $ Satisfies (path [1]) true)]
            validate automaton `shouldBe` Right ()

        it "pruning ends and keeps a term when a guard reads a position through the recursive reference" $ do
            let leaf = Node [Transition "a" true [] noConstraint]
                automaton = Mu $ \self ->
                    Node
                        [ Transition "g" true [leaf] noConstraint
                        , Transition "f" true [leaf, self] (semanticConstraint $ Satisfies (path [1, 0]) true)
                        ]
                a = Term.Node (RefinedSymbol "a" true) []
                term = Term.Node (RefinedSymbol "f" true) [a, Term.Node (RefinedSymbol "g" true) [a]]
            validate automaton `shouldBe` Right ()
            pruned <- timeout 10000000 $ prune alwaysEntails automaton
            case pruned of
                Just (Right result) -> accepts alwaysEntails result term >>= (`shouldBe` Yes)
                other -> expectationFailure $ show other

        it "pruning ends and keeps a term when an equality reads a position through the recursive reference" $ do
            let leaf = Node [Transition "a" true [] noConstraint]
                automaton = Mu $ \self ->
                    Node
                        [ Transition "g" true [leaf] noConstraint
                        , Transition "f" true [leaf, self] (semanticConstraint $ Same (path [0]) (path [1, 0]))
                        ]
                a = Term.Node (RefinedSymbol "a" true) []
                term = Term.Node (RefinedSymbol "f" true) [a, Term.Node (RefinedSymbol "g" true) [a]]
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
                a = Term.Node (RefinedSymbol "a" true) []
                term =
                    Term.Node
                        (RefinedSymbol "f" true)
                        [a, Term.Node (RefinedSymbol "h" true) [Term.Node (RefinedSymbol "b" true) [], Term.Node (RefinedSymbol "g" true) [a]]]
            validate automaton `shouldBe` Right ()
            pruned <- timeout 10000000 $ prune alwaysEntails automaton
            case pruned of
                Just (Right result) -> accepts alwaysEntails result term >>= (`shouldBe` Yes)
                other -> expectationFailure $ show other

        it "decides a deep term in linear time when a node has two transitions with one symbol" $ do
            -- A search with no table tries both "f" transitions again at each
            -- level of a rejected term, so its time is exponential in the depth.
            let a = Transition "a" true [] noConstraint
                f child = Transition "f" true [child] noConstraint
                automaton = Mu $ \q -> Node [a, f q, f (Node [a, f q])]
                label name = RefinedSymbol name true
                deep leaf = iterate (\term -> Term.Node (label "f") [term]) (Term.Node (label leaf) [])
            decided <- timeout 10000000 $ mapM (accepts alwaysEntails automaton . (!! 60) . deep) ["a", "b"]
            decided `shouldBe` Just [Yes, No]
