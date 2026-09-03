module Data.LTA.RecursiveGeneratorSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import Data.ECTA.Paths (mkEqConstraints)
import Data.LTA (
    Automaton,
    AutomatonError,
    Entailment (Entailment),
    LiquidTerm (LiquidTerm),
    State (State),
    Verdict (Unknown),
    equalityConstraint,
    mkAutomaton,
    path,
    unconstrainedConstraint,
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
                [ Transition "nil" true [] unconstrainedConstraint
                , Transition "cons" true [State 1, State 0] unconstrainedConstraint
                ]
            )
        , (State 1, [Transition "item" true [] unconstrainedConstraint])
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
            let listItem = LiquidTerm "item" true []
                nil = LiquidTerm "nil" true []
            values compiled
                `shouldBe` [ nil
                           , LiquidTerm "cons" true [listItem, nil]
                           , LiquidTerm "cons" true [listItem, LiquidTerm "cons" true [listItem, nil]]
                           ]

        it "keeps deterministic replay ranks after unfolding" $ do
            compiled <- compileAtDepth 2
            LTA.cardinality compiled `shouldBe` 3
            fmap LTA.generatedValue (LTA.select 2 compiled)
                `shouldBe` Right (last $ values compiled)

        it "routes a residual equality through MicroECTA instead of an FTA product" $
            case mkAutomaton
                (State 0)
                [
                    ( State 0
                    ,
                        [ Transition
                            "pair"
                            true
                            [State 1, State 1]
                            (equalityConstraint sameChildren)
                        ]
                    )
                ,
                    ( State 1
                    ,
                        [ Transition "item-a" true [] unconstrainedConstraint
                        , Transition "item-b" true [] unconstrainedConstraint
                        ]
                    )
                ] of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    result <- LTA.compileAutomaton unusedEntailment automaton
                    case result of
                        Left err -> expectationFailure $ show err
                        Right compiled -> do
                            LTA.cardinality compiled `shouldBe` 2
                            map (fmap LTA.generatedValue . (`LTA.select` compiled)) [0, 1]
                                `shouldBe` map Right [pair itemA, pair itemB]
  where
    sameChildren = mkEqConstraints [[path [0], path [1]]]
    itemA = LiquidTerm "item-a" true []
    itemB = LiquidTerm "item-b" true []
    pair item = LiquidTerm "pair" true [item, item]

    values compiled =
        [ LTA.generatedValue generated
        | rank <- [0 .. LTA.cardinality compiled - 1]
        , Right generated <- [LTA.select rank compiled]
        ]
