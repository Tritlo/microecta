module Data.LTA.RecognitionSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import Data.LTA (
    AutomatonError (DanglingState, InconsistentArity),
    LiquidTerm (LiquidTerm),
    State (State),
    Verdict (..),
    accepts,
    automatonAlphabet,
    denotationAtMost,
    mkAutomaton,
    mkAutomatonWithFinals,
    unconstrainedConstraint,
    pattern Transition,
 )
import Data.LTA.Refinement (true, value, (.==.))
import Data.LTA.TestSupport (unusedEntailment)
import qualified Data.Set as Set

spec :: Spec
spec =
    describe "refinement-labelled LTA recognition" $ do
        it "accepts the transition's declared refinement" $ do
            let zero = value .==. (0 :: Int)
            case mkAutomaton (State 0) [(State 0, [Transition "zero" zero [] unconstrainedConstraint])] of
                Left err -> expectationFailure $ show err
                Right automaton ->
                    accepts unusedEntailment automaton (LiquidTerm "zero" zero [])
                        >>= (`shouldBe` Yes)

        it "rejects an invented refinement on the same constructor" $ do
            let zero = value .==. (0 :: Int)
            case mkAutomaton (State 0) [(State 0, [Transition "zero" zero [] unconstrainedConstraint])] of
                Left err -> expectationFailure $ show err
                Right automaton ->
                    accepts unusedEntailment automaton (LiquidTerm "zero" true [])
                        >>= (`shouldBe` No)

        it "keeps arity ranked by constructor even across refinements" $ do
            let zero = value .==. (0 :: Int)
                one = value .==. (1 :: Int)
            mkAutomaton
                (State 0)
                [
                    ( State 0
                    ,
                        [ Transition "value" zero [] unconstrainedConstraint
                        , Transition "value" one [State 1] unconstrainedConstraint
                        ]
                    )
                , (State 1, [Transition "child" true [] unconstrainedConstraint])
                ]
                `shouldBe` Left (InconsistentArity "value" 0 1)

        it "normalizes the paper's final-state set without changing its union language" $ do
            let rows =
                    [ (State 0, [Transition "left" true [] unconstrainedConstraint])
                    , (State 1, [Transition "right" true [] unconstrainedConstraint])
                    ]
            case mkAutomatonWithFinals [State 0, State 1] rows of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    Set.size (automatonAlphabet automaton) `shouldBe` 2
                    accepts unusedEntailment automaton (LiquidTerm "left" true [])
                        >>= (`shouldBe` Yes)
                    accepts unusedEntailment automaton (LiquidTerm "right" true [])
                        >>= (`shouldBe` Yes)

        it "accepts an empty final-state set with an empty denotation" $
            case mkAutomatonWithFinals [] [(State 0, [Transition "unused" true [] unconstrainedConstraint])] of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    Set.size (automatonAlphabet automaton) `shouldBe` 1
                    accepts unusedEntailment automaton (LiquidTerm "unused" true [])
                        >>= (`shouldBe` No)
                    denotationAtMost unusedEntailment 2 automaton >>= (`shouldBe` Right [])

        it "normalizes an LTA with no states and no final states" $
            case mkAutomatonWithFinals [] [] of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    automatonAlphabet automaton `shouldBe` Set.empty
                    denotationAtMost unusedEntailment 0 automaton >>= (`shouldBe` Right [])

        it "keeps empty finals empty when state identities include both Int bounds" $
            case mkAutomatonWithFinals
                []
                [ (State maxBound, [])
                , (State minBound, [Transition "excluded" true [] unconstrainedConstraint])
                ] of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    accepts unusedEntailment automaton (LiquidTerm "excluded" true []) >>= (`shouldBe` No)
                    denotationAtMost unusedEntailment 0 automaton >>= (`shouldBe` Right [])

        it "does not define a dangling child while normalizing empty finals" $
            mkAutomatonWithFinals [] [(State 0, [Transition "wrap" true [State 1] unconstrainedConstraint])]
                `shouldBe` Left (DanglingState $ State 1)

        it "does not merge an unrelated row when normalizing finals at Int bounds" $
            case mkAutomatonWithFinals
                [State maxBound, State 1]
                [ (State maxBound, [Transition "first" true [] unconstrainedConstraint])
                , (State 1, [Transition "second" true [] unconstrainedConstraint])
                , (State minBound, [Transition "excluded" true [] unconstrainedConstraint])
                ] of
                Left err -> expectationFailure $ show err
                Right automaton ->
                    traverse
                        (accepts unusedEntailment automaton)
                        [LiquidTerm symbol true [] | symbol <- ["first", "second", "excluded"]]
                        >>= (`shouldBe` [Yes, Yes, No])
