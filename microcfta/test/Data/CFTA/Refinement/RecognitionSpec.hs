{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.RecognitionSpec (spec) where

import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import Data.CFTA.Refinement (
    Automaton,
    AutomatonError (InconsistentArity),
    Node (EmptyNode, Node),
    Symbol (RefinedSymbol),
    Verdict (..),
    accepts,
    automatonAlphabet,
    denotationAtMost,
    noConstraint,
    union,
    validate,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (refinementFormula, true, (.==))
import Data.CFTA.Refinement.TestSupport (unusedEntailment)

spec :: Spec
spec =
    describe "refinement-labelled LTA recognition" $ do
        it "accepts the transition's declared refinement" $ do
            let zero = refinementFormula (\v -> v .== 0)
                automaton = Node [Transition "zero" zero [] noConstraint]
            accepts unusedEntailment automaton (Tree.Node (RefinedSymbol "zero" zero) [])
                >>= (`shouldBe` Yes)

        it "rejects an invented refinement on the same constructor" $ do
            let zero = refinementFormula (\v -> v .== 0)
                automaton = Node [Transition "zero" zero [] noConstraint]
            accepts unusedEntailment automaton (Tree.Node (RefinedSymbol "zero" true) [])
                >>= (`shouldBe` No)

        it "keeps arity ranked by constructor even across refinements" $ do
            let zero = refinementFormula (\v -> v .== 0)
                one = refinementFormula (\v -> v .== 1)
                child = Node [Transition "child" true [] noConstraint]
                automaton =
                    Node
                        [ Transition "value" zero [] noConstraint
                        , Transition "value" one [child] noConstraint
                        ]
            validate automaton
                `shouldSatisfy` (`elem` [Left (InconsistentArity "value" 0 1), Left (InconsistentArity "value" 1 0)])

        it "takes the union of accepting nodes as the paper's final-state set" $ do
            let automaton =
                    union
                        [ Node [Transition "left" true [] noConstraint]
                        , Node [Transition "right" true [] noConstraint]
                        ]
            Set.size (automatonAlphabet automaton) `shouldBe` 2
            accepts unusedEntailment automaton (Tree.Node (RefinedSymbol "left" true) [])
                >>= (`shouldBe` Yes)
            accepts unusedEntailment automaton (Tree.Node (RefinedSymbol "right" true) [])
                >>= (`shouldBe` Yes)

        it "gives the empty final-state set an empty denotation" $ do
            let automaton = union [] :: Automaton
            automaton `shouldBe` EmptyNode
            automatonAlphabet automaton `shouldBe` Set.empty
            accepts unusedEntailment automaton (Tree.Node (RefinedSymbol "unused" true) [])
                >>= (`shouldBe` No)
            denotationAtMost unusedEntailment 2 automaton >>= (`shouldBe` Right [])
