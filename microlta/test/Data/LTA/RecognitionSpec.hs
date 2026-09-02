module Data.LTA.RecognitionSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import Data.LTA (
    AutomatonError (InconsistentArity),
    Entailment (Entailment),
    Guard (Top),
    LiquidTerm (LiquidTerm),
    State (State),
    Verdict (..),
    accepts,
    mkAutomaton,
    pattern Transition,
 )
import Data.LTA.Refinement (true, (.==.))
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
            case mkAutomaton (State 0) [(State 0, [Transition "zero" zero [] Top])] of
                Left err -> expectationFailure $ show err
                Right automaton ->
                    accepts unusedEntailment automaton (LiquidTerm "zero" zero [])
                        >>= (`shouldBe` Yes)

        it "rejects an invented refinement on the same constructor" $ do
            let zero = value .==. (0 :: Int)
            case mkAutomaton (State 0) [(State 0, [Transition "zero" zero [] Top])] of
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
                        [ Transition "value" zero [] Top
                        , Transition "value" one [State 1] Top
                        ]
                    )
                , (State 1, [Transition "child" true [] Top])
                ]
                `shouldBe` Left (InconsistentArity "value" 0 1)
