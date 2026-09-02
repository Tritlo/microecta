module Data.LTA.RecursiveSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import Data.LTA (
    Automaton,
    AutomatonError (CyclicGuardReference),
    Entailment (Entailment),
    Guard (Satisfies, Top),
    LiquidTerm (LiquidTerm),
    State (State),
    Verdict (Yes),
    accepts,
    mkAutomaton,
    path,
    pattern Transition,
 )
import Data.LTA.Refinement (true)

alwaysEntails :: Entailment
alwaysEntails = Entailment $ \_ _ -> pure Yes

recursiveLists :: Either AutomatonError Automaton
recursiveLists =
    mkAutomaton
        (State 0)
        [
            ( State 0
            ,
                [ Transition "nil" true [] Top
                , Transition "cons" true [State 1, State 0] Top
                ]
            )
        , (State 1, [Transition "item" true [] Top])
        ]

spec :: Spec
spec =
    describe "recursive LTAs" $ do
        it "accepts cyclic languages when guards do not inspect the cycle" $
            case recursiveLists of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    let item = LiquidTerm "item" true []
                        nil = LiquidTerm "nil" true []
                        list = LiquidTerm "cons" true [item, LiquidTerm "cons" true [item, nil]]
                    accepts alwaysEntails automaton list >>= (`shouldBe` Yes)

        it "allows a guard to inspect an acyclic sibling of a recursive child" $
            case mkAutomaton
                (State 0)
                [ (State 0, [Transition "wrap" true [State 0, State 1] (Satisfies (path [1]) true)])
                , (State 1, [Transition "checked" true [] Top])
                ] of
                Right _ -> pure ()
                Left err -> expectationFailure $ show err

        it "rejects a guard that points into a recursive state" $
            mkAutomaton
                (State 0)
                [ (State 0, [Transition "loop" true [State 0] (Satisfies (path [0]) true)])
                ]
                `shouldBe` Left (CyclicGuardReference (State 0) (path [0]))
