module Data.LTA.RecognitionSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import Data.LTA (
    AutomatonError (InconsistentArity),
    Entailment (Entailment),
    LiquidTerm (LiquidTerm),
    State (State),
    Verdict (..),
    accepts,
    automatonAlphabet,
    automatonFinalStates,
    mkAutomaton,
    mkAutomatonWithFinals,
    unconstrainedConstraint,
    pattern Transition,
 )
import Data.LTA.Refinement (true, (.==.))
import qualified Data.Set as Set
import qualified Language.Fixpoint.Types as Fixpoint

unusedEntailment :: Entailment
unusedEntailment = Entailment $ \_ _ -> pure Unknown

value :: Fixpoint.Expr
value = Fixpoint.EVar $ Fixpoint.symbol ("v" :: String)

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
                    Set.size (automatonFinalStates automaton) `shouldBe` 1
                    Set.size (automatonAlphabet automaton) `shouldBe` 2
                    accepts unusedEntailment automaton (LiquidTerm "left" true [])
                        >>= (`shouldBe` Yes)
                    accepts unusedEntailment automaton (LiquidTerm "right" true [])
                        >>= (`shouldBe` Yes)
