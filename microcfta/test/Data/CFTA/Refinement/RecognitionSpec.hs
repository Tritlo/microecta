{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.RecognitionSpec (spec) where

import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

import Data.CFTA.Refinement (
    Automaton,
    AutomatonError (InconsistentArity),
    LiquidSymbol (LiquidSymbol),
    Node (EmptyNode, Node),
    Verdict (..),
    accepts,
    automatonAlphabet,
    denotationAtMost,
    unconstrainedConstraint,
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
                automaton = Node [Transition "zero" zero [] unconstrainedConstraint]
            accepts unusedEntailment automaton (Tree.Node (LiquidSymbol "zero" zero) [])
                >>= (`shouldBe` Yes)

        it "rejects an invented refinement on the same constructor" $ do
            let zero = refinementFormula (\v -> v .== 0)
                automaton = Node [Transition "zero" zero [] unconstrainedConstraint]
            accepts unusedEntailment automaton (Tree.Node (LiquidSymbol "zero" true) [])
                >>= (`shouldBe` No)

        it "keeps arity ranked by constructor even across refinements" $ do
            let zero = refinementFormula (\v -> v .== 0)
                one = refinementFormula (\v -> v .== 1)
                child = Node [Transition "child" true [] unconstrainedConstraint]
                automaton =
                    Node
                        [ Transition "value" zero [] unconstrainedConstraint
                        , Transition "value" one [child] unconstrainedConstraint
                        ]
            validate automaton
                `shouldSatisfy` (`elem` [Left (InconsistentArity "value" 0 1), Left (InconsistentArity "value" 1 0)])

        it "takes the union of accepting nodes as the paper's final-state set" $ do
            let automaton =
                    union
                        [ Node [Transition "left" true [] unconstrainedConstraint]
                        , Node [Transition "right" true [] unconstrainedConstraint]
                        ]
            Set.size (automatonAlphabet automaton) `shouldBe` 2
            accepts unusedEntailment automaton (Tree.Node (LiquidSymbol "left" true) [])
                >>= (`shouldBe` Yes)
            accepts unusedEntailment automaton (Tree.Node (LiquidSymbol "right" true) [])
                >>= (`shouldBe` Yes)

        it "gives the empty final-state set an empty denotation" $ do
            let automaton = union [] :: Automaton
            automaton `shouldBe` EmptyNode
            automatonAlphabet automaton `shouldBe` Set.empty
            accepts unusedEntailment automaton (Tree.Node (LiquidSymbol "unused" true) [])
                >>= (`shouldBe` No)
            denotationAtMost unusedEntailment 2 automaton >>= (`shouldBe` Right [])
