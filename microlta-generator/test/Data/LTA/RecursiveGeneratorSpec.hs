module Data.LTA.RecursiveGeneratorSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import Data.LTA (
    Automaton,
    AutomatonError,
    Entailment (Entailment),
    Guard (Top),
    LiquidTerm (LiquidTerm),
    State (State),
    Verdict (Unknown),
    mkAutomaton,
    pattern Transition,
 )
import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.Refinement (true)

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

unusedEntailment :: Entailment
unusedEntailment = Entailment $ \_ _ -> pure Unknown

compileAtDepth :: Int -> IO (LTA.Compiled LiquidTerm)
compileAtDepth depth =
    case recursiveLists of
        Left err -> expectationFailure (show err) >> fail "unreachable"
        Right automaton ->
            case LTA.fromAutomatonUpToDepth depth automaton of
                Left err -> expectationFailure (show err) >> fail "unreachable"
                Right generator -> do
                    compiled <- LTA.compile unusedEntailment generator
                    case compiled of
                        Left err -> expectationFailure (show err) >> fail "unreachable"
                        Right language -> pure language

spec :: Spec
spec =
    describe "bounded generation from recursive LTAs" $ do
        it "contains only the base transition at depth zero" $ do
            compiled <- compileAtDepth 0
            values compiled `shouldBe` [LiquidTerm "nil" true []]

        it "unfolds every recursive list through the requested depth" $ do
            compiled <- compileAtDepth 2
            let item = LiquidTerm "item" true []
                nil = LiquidTerm "nil" true []
            values compiled
                `shouldBe` [ nil
                           , LiquidTerm "cons" true [item, nil]
                           , LiquidTerm "cons" true [item, LiquidTerm "cons" true [item, nil]]
                           ]

        it "keeps deterministic replay ranks after unfolding" $ do
            compiled <- compileAtDepth 2
            LTA.cardinality compiled `shouldBe` 3
            fmap LTA.generatedValue (LTA.select 2 compiled)
                `shouldBe` Right (last $ values compiled)
  where
    values compiled =
        [ LTA.generatedValue generated
        | rank <- [0 .. LTA.cardinality compiled - 1]
        , Right generated <- [LTA.select rank compiled]
        ]
