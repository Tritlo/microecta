{-# LANGUAGE TypeApplications #-}

module Data.LTA.RecursiveGeneratorSpec (spec) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldReturn)

import Data.ECTA.Paths (mkEqConstraints)
import Data.LTA (
    Automaton,
    AutomatonError,
    Entailment (Entailment),
    LiquidTerm (LiquidTerm),
    State (State),
    Symbol,
    Verdict (Unknown, Yes),
    accepts,
    equalityConstraint,
    mkAutomaton,
    path,
    unconstrainedConstraint,
    pattern Transition,
 )
import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.Refinement (true)
import qualified Data.Tree.FTA.Generic as Datatype

-- | Two compact shared subtrees with equal languages and distinct state names.
sharedSubtreeAutomaton :: Int -> Symbol -> Either AutomatonError Automaton
sharedSubtreeAutomaton depth rightLeaf =
    mkAutomaton (State 0) $
        [ (State 0, [transition "pair" [left depth, leftTag], transition "pair" [right depth, rightTag]])
        , (left 0, [transition "atom" []])
        , (right 0, [transition "atom" []])
        , (leftTag, [transition "wrap" [State (2 * depth + 5)]])
        , (rightTag, [transition "wrap" [State (2 * depth + 6)]])
        , (State (2 * depth + 5), [transition "a" []])
        , (State (2 * depth + 6), [transition rightLeaf []])
        ]
            <> [ (state level, [transition "fork" [state (level - 1), state (level - 1)]])
               | state <- [left, right]
               , level <- [1 .. depth]
               ]
  where
    left level = State $ level + 1
    right level = State $ depth + level + 2
    leftTag = State $ 2 * depth + 3
    rightTag = State $ 2 * depth + 4
    transition symbol children = Transition symbol true children unconstrainedConstraint

-- | A large shared tree followed by a smaller term in the same rank space.
largeOrSmallAutomaton :: Int -> Either AutomatonError Automaton
largeOrSmallAutomaton depth =
    mkAutomaton (State 0) $
        [ (State 0, [transition "large" [State $ depth + 1], transition "small" []])
        , (State 1, [transition "atom" []])
        ]
            <> [ (State $ level + 1, [transition "fork" [State level, State level]])
               | level <- [1 .. depth]
               ]
  where
    transition symbol children = Transition symbol true children unconstrainedConstraint

-- | Two independently ranked child choices and one dead root alternative.
variablePairAutomaton :: Either AutomatonError Automaton
variablePairAutomaton =
    mkAutomaton
        (State 0)
        [ (State 0, [transition "missing" [State 3], transition "pair" [State 1, State 1]])
        , (State 1, [transition "wrap" [State 2], transition "atom" []])
        , (State 2, [transition "x" [], transition "y" []])
        , (State 3, [])
        ]
  where
    transition symbol children = Transition symbol true children unconstrainedConstraint

-- | Count the physical nodes of one small test term.
termNodes :: LiquidTerm -> Integer
termNodes (LiquidTerm _ _ children) = 1 + sum (map termNodes children)

unusedEntailment :: Entailment
unusedEntailment = Entailment $ \_ _ -> pure Unknown

-- | Compile the derived list grammar with unconstrained liquid annotations.
compileAtDepth :: Int -> IO (LTA.Compiled [()])
compileAtDepth depth = do
    datatype <- either (fail . show) pure $ Datatype.deriveFTA @[()]
    let annotated = Datatype.annotateDatatype (const (true, unconstrainedConstraint)) datatype
    LTA.compile unusedEntailment (LTA.fromDatatypeUpToDepth depth annotated)
        >>= either (fail . show) pure

spec :: Spec
spec = do
    describe "bounded generation from recursive LTAs" $ do
        it "contains only the base transition at depth zero" $ do
            compiled <- compileAtDepth 0
            values compiled `shouldBe` [[]]

        it "unfolds every recursive list through the requested depth" $ do
            compiled <- compileAtDepth 2
            values compiled `shouldBe` [[], [()], [(), ()]]

        it "keeps deterministic replay ranks after unfolding" $ do
            compiled <- compileAtDepth 2
            LTA.cardinality compiled `shouldBe` 3
            fmap LTA.generatedValue (LTA.unrank compiled 2)
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
                            map (fmap LTA.generatedValue . (LTA.unrank compiled)) [0, 1]
                                `shouldBe` map Right [pair itemA, pair itemB]

    describe "structural automaton shrinking" $ do
        it "shrinks a large rank zero to a later smaller transition" $ do
            automaton <- either (fail . show) pure $ largeOrSmallAutomaton 0
            compiled <- LTA.compileAutomaton unusedEntailment automaton >>= either (fail . show) pure
            LTA.shrinkRank compiled 0 `shouldBe` [1]
            LTA.shrinkRank compiled 1 `shouldBe` []
            LTA.shrinkRank compiled (-1) `shouldBe` []
            LTA.shrinkRank compiled 2 `shouldBe` []

        it "skips dead transitions and preserves sibling decisions in child shrinks" $ do
            automaton <- either (fail . show) pure variablePairAutomaton
            compiled <- LTA.compileAutomaton unusedEntailment automaton >>= either (fail . show) pure
            LTA.cardinality compiled `shouldBe` 9
            LTA.shrinkRank compiled 1 `shouldBe` [8, 7, 2]
            LTA.shrinkRank compiled 4 `shouldBe` [8, 7, 5]
            LTA.shrinkRank compiled 8 `shouldBe` []

        it "emits only accepted terms with strictly fewer tree nodes" $ do
            automaton <- either (fail . show) pure variablePairAutomaton
            compiled <- LTA.compileAutomaton unusedEntailment automaton >>= either (fail . show) pure
            forM_ [0 .. LTA.cardinality compiled - 1] $ \rank -> do
                source <- either (fail . show) pure $ LTA.unrank compiled rank
                forM_ (LTA.shrinkRank compiled rank) $ \candidate -> do
                    target <- either (fail . show) pure $ LTA.unrank compiled candidate
                    let term = LTA.generatedTerm target
                    (termNodes term < termNodes (LTA.generatedTerm source)) `shouldBe` True
                    accepts unusedEntailment automaton term `shouldReturn` Yes

        it "keeps graph shrinks independent of generated and mapped values" $ do
            automaton <- either (fail . show) pure $ largeOrSmallAutomaton 0
            let unavailableValue _ _ _ = error "shrinking forced a generated value" :: ()
            compiled <-
                LTA.compileAutomatonWith unusedEntailment unavailableValue automaton
                    >>= either (fail . show) pure
            LTA.shrinkRank compiled 0 `shouldBe` [1]
            LTA.shrinkRank (LTA.mapCompiled (const False) compiled) 0 `shouldBe` [1]

        it "does not expand huge shared trees with uniform node counts" $ do
            automaton <- either (fail . show) pure $ sharedSubtreeAutomaton 50 "b"
            completed <- timeout 60000000 $ do
                compiled <-
                    LTA.compileAutomatonWith unusedEntailment selectedTag automaton
                        >>= either (fail . show) pure
                evaluate $
                    values compiled == ["a", "b"]
                        && null (LTA.shrinkRank compiled 0)
                        && null (LTA.shrinkRank compiled 1)
            completed `shouldBe` Just True

        it "counts shared selected runs beyond machine-sized node counts" $ do
            automaton <- either (fail . show) pure $ largeOrSmallAutomaton 70
            completed <- timeout 60000000 $ do
                compiled <-
                    LTA.compileAutomatonWith unusedEntailment (\symbol _ _ -> symbol) automaton
                        >>= either (fail . show) pure
                evaluate $
                    values compiled == ["large", "small"]
                        && LTA.shrinkRank compiled 0 == [1]
                        && null (LTA.shrinkRank compiled 1)
            completed `shouldBe` Just True

    describe "finite automaton overlap checks" $ do
        it "counts shared subtrees without expanding their repeated state pairs" $ do
            automaton <- either (fail . show) pure $ sharedSubtreeAutomaton 50 "b"
            result <- LTA.compileAutomatonWith unusedEntailment selectedTag automaton
            case result of
                Left err -> expectationFailure $ show err
                Right compiled -> do
                    LTA.cardinality compiled `shouldBe` 2
                    values compiled `shouldBe` ["a", "b"]

        it "keeps the term ranks of a small shared automaton" $ do
            automaton <- either (fail . show) pure $ sharedSubtreeAutomaton 3 "b"
            complete <- LTA.compile unusedEntailment $ LTA.fromLTA 5 automaton
            counted <- LTA.compileAutomaton unusedEntailment automaton
            fmap LTA.cardinality counted `shouldBe` Right 2
            fmap values counted `shouldBe` fmap values complete

        it "deduplicates overlapping alternatives without expanding their shared subtrees" $ do
            automaton <- either (fail . show) pure $ sharedSubtreeAutomaton 50 "a"
            result <- LTA.compileAutomatonWith unusedEntailment selectedTag automaton
            fmap LTA.cardinality result `shouldBe` Right 1

        it "does not count an alternative with an empty child state" $ do
            automaton <-
                either (fail . show) pure $
                    mkAutomaton
                        (State 0)
                        [
                            ( State 0
                            ,
                                [ Transition "wrap" true [State 1] unconstrainedConstraint
                                , Transition "wrap" true [State 2] unconstrainedConstraint
                                ]
                            )
                        , (State 1, [])
                        , (State 2, [Transition "item-a" true [] unconstrainedConstraint])
                        ]
            result <- LTA.compileAutomaton unusedEntailment automaton
            fmap LTA.cardinality result `shouldBe` Right 1
            fmap values result `shouldBe` Right [LiquidTerm "wrap" true [itemA]]

        it "reports an empty initial state without an overlap" $ do
            automaton <- either (fail . show) pure $ mkAutomaton (State 0) [(State 0, [])]
            result <- LTA.compileAutomaton unusedEntailment automaton
            fmap LTA.cardinality result `shouldBe` Left LTA.EmptyGenerator
  where
    sameChildren = mkEqConstraints [[path [0], path [1]]]
    itemA = LiquidTerm "item-a" true []
    itemB = LiquidTerm "item-b" true []
    pair item = LiquidTerm "pair" true [item, item]

    selectedTag symbol _ children = case (symbol, children) of
        ("pair", [_, tag]) -> tag
        ("wrap", [tag]) -> tag
        _ -> symbol

    values compiled =
        [ LTA.generatedValue generated
        | rank <- [0 .. LTA.cardinality compiled - 1]
        , Right generated <- [LTA.unrank compiled rank]
        ]
