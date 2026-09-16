module Data.LTA.MinimizeSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import qualified Data.Map.Strict as Map

import Data.LTA (
    Automaton,
    AutomatonError,
    Entailment,
    Guard (Satisfies),
    LiquidTerm (LiquidTerm),
    MinimizeError (StaleSimilarity),
    State (State),
    Subtyping (..),
    TransitionId (TransitionId),
    Verdict (No),
    automatonInitial,
    automatonTransitions,
    denotationAtMost,
    minimize,
    mkAutomaton,
    path,
    reduce,
    refinementSubtypingBy,
    semanticConstraint,
    similarity,
    similarityPairs,
    transitionChildren,
    transitionSymbol,
    unconstrainedConstraint,
    pattern Transition,
 )
import Data.LTA.LiquidFixpoint (withZ3)
import Data.LTA.Refinement (value, (.==.), (.>=.))
import Data.LTA.TestSupport (declarations)
import qualified Data.Tree.FTA as FTA
import qualified Language.Fixpoint.Types as Fixpoint

spec :: Spec
spec =
    describe "similarity and minimization" $ do
        it "infers transition similarity and removes the supertype" $
            withZ3 declarations $ \solver ->
                case similarAtoms of
                    Left err -> expectationFailure $ show err
                    Right automaton -> do
                        inferred <- similarity (atomSubtyping solver) automaton
                        case inferred of
                            Left err -> expectationFailure $ show err
                            Right related -> do
                                similarityPairs related
                                    `shouldBe` [(TransitionId (State 0) 1, TransitionId (State 0) 0)]
                                case minimize automaton related of
                                    Left err -> expectationFailure $ show err
                                    Right reduced ->
                                        map
                                            transitionSymbol
                                            (Map.findWithDefault [] (State 0) $ automatonTransitions reduced)
                                            `shouldBe` ["natural"]

        it "rejects a similarity snapshot when transition contents change at the same addresses" $
            withZ3 declarations $ \solver ->
                case similarAtoms of
                    Left err -> expectationFailure $ show err
                    Right original -> do
                        inferred <- similarity (atomSubtyping solver) original
                        case inferred of
                            Left err -> expectationFailure $ show err
                            Right related -> do
                                let changed = FTA.mapGuards (const $ semanticConstraint $ Satisfies (path []) Fixpoint.PTrue) original
                                minimize changed related `shouldBe` Left StaleSimilarity

        it "rejects a similarity snapshot when only the accepting state changes" $
            withZ3 declarations $ \solver ->
                case separatedSimilarAtoms of
                    Left err -> expectationFailure $ show err
                    Right original -> do
                        inferred <- similarity (atomSubtyping solver) original
                        case (inferred, mkAutomaton (State 1) $ Map.toList $ automatonTransitions original) of
                            (Right related, Right changed) -> minimize changed related `shouldBe` Left StaleSimilarity
                            (Left err, _) -> expectationFailure $ show err
                            (_, Left err) -> expectationFailure $ show err

        it "checks snapshots even when the similarity set is empty" $
            case (mkAutomaton (State 0) [(State 0, [])], mkAutomaton (State 1) [(State 1, [])]) of
                (Right original, Right changed) -> do
                    inferred <- similarity (Subtyping $ \_ _ _ -> pure No) original
                    case inferred of
                        Left err -> expectationFailure $ show err
                        Right related -> minimize changed related `shouldBe` Left StaleSimilarity
                (Left err, _) -> expectationFailure $ show err
                (_, Left err) -> expectationFailure $ show err

        it "redirects incoming edges to the retained subtype target" $
            withZ3 declarations $ \solver ->
                case separatedSimilarAtoms of
                    Left err -> expectationFailure $ show err
                    Right automaton -> do
                        reducedResult <- reduce solver (atomSubtyping solver) automaton
                        case reducedResult of
                            Left err -> expectationFailure $ show err
                            Right reduced -> do
                                map
                                    transitionChildren
                                    (Map.findWithDefault [] (State 0) $ automatonTransitions reduced)
                                    `shouldBe` [[State 1], [State 1]]
                                Map.findWithDefault [] (State 2) (automatonTransitions reduced)
                                    `shouldBe` []

        it "keeps unrelated alternatives at a removed transition's target" $
            withZ3 declarations $ \solver ->
                checkMinimization (atomSubtyping solver) sharedSupertypeState $ \reduced -> do
                    map transitionSymbol (Map.findWithDefault [] (State 2) $ automatonTransitions reduced)
                        `shouldBe` ["other"]
                    map transitionChildren (Map.findWithDefault [] (State 0) $ automatonTransitions reduced)
                        `shouldBe` [[State 1], [State 2], [State 1]]
                    denotationAtMost solver 1 reduced >>= (\terms -> fmap length terms `shouldBe` Right 3)

        it "does not strand the paper's final state during minimization" $
            withZ3 declarations $ \solver ->
                case finalStateSupertype of
                    Left err -> expectationFailure $ show err
                    Right automaton -> do
                        inferred <- similarity (atomSubtyping solver) automaton
                        case inferred of
                            Left err -> expectationFailure $ show err
                            Right related ->
                                minimize automaton related
                                    `shouldBe` Right automaton

        it "can remove a final transition when another final derivation remains" $
            withZ3 declarations $ \solver ->
                checkMinimization (atomSubtyping solver) finalStateWithAlternative $ \reduced -> do
                    automatonInitial reduced `shouldBe` State 2
                    denotationAtMost solver 0 reduced
                        >>= (`shouldBe` Right [LiquidTerm "other" Fixpoint.PTrue []])

        it "allows multiple representatives for one target and substitutes repeated states together" $
            withZ3 declarations $ \solver ->
                checkMinimization (twoClassSubtyping solver) multipleRepresentatives $ \reduced -> do
                    map transitionSymbol (Map.findWithDefault [] (State 1) $ automatonTransitions reduced)
                        `shouldBe` ["other"]
                    map transitionChildren (Map.findWithDefault [] (State 0) $ automatonTransitions reduced)
                        `shouldBe` [[State 1, State 1], [State 2, State 2], [State 3, State 3]]
                    denotationAtMost solver 1 reduced >>= (\terms -> fmap length terms `shouldBe` Right 3)

        it "composes substitutions for distinct source states on earlier copies" $
            withZ3 declarations $ \solver ->
                checkMinimization (twoClassSubtyping solver) composedRepresentatives $ \reduced -> do
                    map transitionChildren (Map.findWithDefault [] (State 0) $ automatonTransitions reduced)
                        `shouldBe` [[State 1, State 2], [State 3, State 2], [State 1, State 4], [State 3, State 4]]
                    denotationAtMost solver 1 reduced >>= (\terms -> fmap length terms `shouldBe` Right 4)

        it "keeps a redirected copy when its original supertype transition is removed" $
            withZ3 declarations $ \solver ->
                checkMinimization (twoClassSubtyping solver) copiedSupertype $ \reduced -> do
                    map transitionChildren (Map.findWithDefault [] (State 2) $ automatonTransitions reduced)
                        `shouldBe` [[State 3]]
                    map transitionChildren (Map.findWithDefault [] (State 0) $ automatonTransitions reduced)
                        `shouldBe` [[State 2], [State 4]]
                    denotationAtMost solver 2 reduced >>= (\terms -> fmap length terms `shouldBe` Right 2)

        it "deduplicates equivalent original transitions without removing another alternative" $
            withZ3 declarations $ \solver -> do
                let duplicates =
                        mkAutomaton
                            (State 0)
                            [
                                ( State 0
                                ,
                                    [ Transition "unknown" Fixpoint.PTrue [] unconstrainedConstraint
                                    , Transition "unknown" Fixpoint.PTrue [] unconstrainedConstraint
                                    , Transition "other" Fixpoint.PTrue [] unconstrainedConstraint
                                    ]
                                )
                            ]
                checkMinimization (atomSubtyping solver) duplicates $ \reduced ->
                    map transitionSymbol (Map.findWithDefault [] (State 0) $ automatonTransitions reduced)
                        `shouldBe` ["unknown", "other"]

        it "applies M-Trans transitively over one similarity snapshot" $
            withZ3 declarations $ \solver ->
                case transitiveSimilarAtoms of
                    Left err -> expectationFailure $ show err
                    Right automaton -> do
                        inferred <- similarity (threeAtomSubtyping solver) automaton
                        case inferred of
                            Left err -> expectationFailure $ show err
                            Right related ->
                                case minimize automaton related of
                                    Left err -> expectationFailure $ show err
                                    Right reduced -> do
                                        map
                                            transitionChildren
                                            (Map.findWithDefault [] (State 0) $ automatonTransitions reduced)
                                            `shouldBe` replicate 3 [State 1]
                                        Map.findWithDefault [] (State 2) (automatonTransitions reduced)
                                            `shouldBe` []
                                        Map.findWithDefault [] (State 3) (automatonTransitions reduced)
                                            `shouldBe` []

        it "uses the first inferred representative for overlapping subtypes" $
            withZ3 declarations $ \solver ->
                case overlappingSimilarAtoms of
                    Left err -> expectationFailure $ show err
                    Right automaton -> do
                        inferred <- similarity (overlappingAtomSubtyping solver) automaton
                        case inferred of
                            Left err -> expectationFailure $ show err
                            Right related ->
                                case minimize automaton related of
                                    Left err -> expectationFailure $ show err
                                    Right reduced ->
                                        map
                                            transitionChildren
                                            (Map.findWithDefault [] (State 0) $ automatonTransitions reduced)
                                            `shouldBe` [[State 1], [State 2], [State 1]]

        it "retains a base required by a stricter representative" $
            withZ3 declarations $ \solver ->
                checkRetainedBatch solver (threeAtomSubtyping solver) dependentRepresentative 1

        it "retains a base required by a recursive alternative in the same row" $
            withZ3 declarations $ \solver ->
                checkRetainedBatch solver (threeAtomSubtyping solver) recursiveRepresentative 4

        it "retains a productive base when its subtype has no finite derivation" $
            withZ3 declarations $ \solver ->
                checkRetainedBatch solver (threeAtomSubtyping solver) unproductiveRepresentative 1

        it "retains batches whose combined redirects create a dependency cycle" $
            withZ3 declarations $ \solver ->
                checkRetainedBatch
                    solver
                    (twoClassSubtyping solver)
                    mutuallyDependentRepresentatives
                    1

        it "retains a batch whose copied guard would inspect a cyclic target" $
            withZ3 declarations $ \solver ->
                checkRetainedBatch solver (atomSubtyping solver) cyclicGuardRepresentative 1

-- | Inspect a successful schedule while reporting construction and inference failures.
checkMinimization :: Subtyping -> Either AutomatonError Automaton -> (Automaton -> IO ()) -> IO ()
checkMinimization subtyping constructed check =
    case constructed of
        Left err -> expectationFailure $ show err
        Right original -> do
            inferred <- similarity subtyping original
            case inferred of
                Left err -> expectationFailure $ show err
                Right related -> case minimize original related of
                    Left err -> expectationFailure $ show err
                    Right reduced -> check reduced

-- | Check that minimization retains the finite derivations required by a batch.
checkRetainedBatch :: Entailment -> Subtyping -> Either AutomatonError Automaton -> Int -> IO ()
checkRetainedBatch solver subtyping constructed expected =
    case constructed of
        Left err -> expectationFailure $ show err
        Right original -> do
            before <- denotationAtMost solver 3 original
            fmap length before `shouldBe` Right expected
            inferred <- similarity subtyping original
            case inferred of
                Left err -> expectationFailure $ show err
                Right related -> minimize original related `shouldBe` Right original

-- | Similarity for integer atom transitions; structural nodes are excluded.
atomSubtyping :: Entailment -> Subtyping
atomSubtyping solver = refinementSubtypingBy solver classify
  where
    classify transition
        | transitionSymbol transition `elem` ["unknown", "natural"] = Just ("integer" :: String)
        | otherwise = Nothing

-- | Three comparable integer refinements for the transitive M-Trans fixture.
threeAtomSubtyping :: Entailment -> Subtyping
threeAtomSubtyping solver = refinementSubtypingBy solver classify
  where
    classify transition
        | transitionSymbol transition `elem` ["specific", "natural", "unknown"] =
            Just ("integer" :: String)
        | otherwise = Nothing

-- | Two incomparable exact values that both refine one unknown value.
overlappingAtomSubtyping :: Entailment -> Subtyping
overlappingAtomSubtyping solver = refinementSubtypingBy solver classify
  where
    classify transition
        | transitionSymbol transition `elem` ["exact-zero", "exact-one", "unknown"] =
            Just ("integer" :: String)
        | otherwise = Nothing

-- | Two independent source type classes for state-substitution schedules.
twoClassSubtyping :: Entailment -> Subtyping
twoClassSubtyping solver = refinementSubtypingBy solver classify
  where
    classify transition
        | transitionSymbol transition `elem` ["specific-a", "unknown-a"] = Just False
        | transitionSymbol transition `elem` ["specific-b", "unknown-b"] = Just True
        | otherwise = Nothing

-- | Two refinements sharing one target state, as in an alternative row.
similarAtoms :: Either AutomatonError Automaton
similarAtoms =
    mkAutomaton
        (State 0)
        [
            ( State 0
            ,
                [ Transition "unknown" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "natural" (value .>=. (0 :: Int)) [] unconstrainedConstraint
                ]
            )
        ]

-- | Paper-style representatives with one target state per program transition.
separatedSimilarAtoms :: Either AutomatonError Automaton
separatedSimilarAtoms =
    mkAutomaton
        (State 0)
        [
            ( State 0
            ,
                [ Transition "specific-box" Fixpoint.PTrue [State 1] unconstrainedConstraint
                , Transition "general-box" Fixpoint.PTrue [State 2] unconstrainedConstraint
                ]
            )
        , (State 1, [Transition "natural" (value .>=. (0 :: Int)) [] unconstrainedConstraint])
        , (State 2, [Transition "unknown" Fixpoint.PTrue [] unconstrainedConstraint])
        ]

-- | A supertype transition shares its target with an unrelated alternative.
sharedSupertypeState :: Either AutomatonError Automaton
sharedSupertypeState =
    mkAutomaton
        (State 0)
        [
            ( State 0
            ,
                [ Transition "specific-box" Fixpoint.PTrue [State 1] unconstrainedConstraint
                , Transition "general-box" Fixpoint.PTrue [State 2] unconstrainedConstraint
                ]
            )
        , (State 1, [Transition "natural" (value .>=. (0 :: Int)) [] unconstrainedConstraint])
        ,
            ( State 2
            ,
                [ Transition "unknown" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "other" Fixpoint.PTrue [] unconstrainedConstraint
                ]
            )
        ]

-- | Removing the final supertype transition would leave no accepted derivation.
finalStateSupertype :: Either AutomatonError Automaton
finalStateSupertype =
    mkAutomaton
        (State 2)
        [ (State 1, [Transition "natural" (value .>=. (0 :: Int)) [] unconstrainedConstraint])
        , (State 2, [Transition "unknown" Fixpoint.PTrue [] unconstrainedConstraint])
        ]

-- | A final supertype can be removed while another final alternative remains.
finalStateWithAlternative :: Either AutomatonError Automaton
finalStateWithAlternative =
    mkAutomaton
        (State 2)
        [ (State 1, [Transition "natural" (value .>=. (0 :: Int)) [] unconstrainedConstraint])
        ,
            ( State 2
            ,
                [ Transition "unknown" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "other" Fixpoint.PTrue [] unconstrainedConstraint
                ]
            )
        ]

-- | Two removed transitions share a target but use different representatives.
multipleRepresentatives :: Either AutomatonError Automaton
multipleRepresentatives =
    mkAutomaton
        (State 0)
        [ (State 0, [Transition "pair" Fixpoint.PTrue [State 1, State 1] unconstrainedConstraint])
        ,
            ( State 1
            ,
                [ Transition "unknown-a" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "unknown-b" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "other" Fixpoint.PTrue [] unconstrainedConstraint
                ]
            )
        , (State 2, [Transition "specific-a" (value .==. (0 :: Int)) [] unconstrainedConstraint])
        , (State 3, [Transition "specific-b" (value .==. (1 :: Int)) [] unconstrainedConstraint])
        ]

-- | Independent substitutions can affect each argument of a copied transition.
composedRepresentatives :: Either AutomatonError Automaton
composedRepresentatives =
    mkAutomaton
        (State 0)
        [ (State 0, [Transition "pair" Fixpoint.PTrue [State 1, State 2] unconstrainedConstraint])
        ,
            ( State 1
            ,
                [ Transition "unknown-a" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "other-a" Fixpoint.PTrue [] unconstrainedConstraint
                ]
            )
        ,
            ( State 2
            ,
                [ Transition "unknown-b" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "other-b" Fixpoint.PTrue [] unconstrainedConstraint
                ]
            )
        , (State 3, [Transition "specific-a" (value .==. (0 :: Int)) [] unconstrainedConstraint])
        , (State 4, [Transition "specific-b" (value .==. (1 :: Int)) [] unconstrainedConstraint])
        ]

-- | The first step copies a supertype whose original is removed by the second.
copiedSupertype :: Either AutomatonError Automaton
copiedSupertype =
    mkAutomaton
        (State 0)
        [ (State 0, [Transition "goal" Fixpoint.PTrue [State 2] unconstrainedConstraint])
        , (State 1, [Transition "unknown-a" Fixpoint.PTrue [] unconstrainedConstraint])
        , (State 2, [Transition "unknown-b" Fixpoint.PTrue [State 1] unconstrainedConstraint])
        , (State 3, [Transition "specific-a" (value .==. (0 :: Int)) [] unconstrainedConstraint])
        , (State 4, [Transition "specific-b" (value .==. (1 :: Int)) [] unconstrainedConstraint])
        ]

-- | A representative's other alternative makes its state cyclic.
cyclicGuardRepresentative :: Either AutomatonError Automaton
cyclicGuardRepresentative =
    mkAutomaton
        (State 0)
        [ (State 0, [Transition "goal" Fixpoint.PTrue [State 1] $ semanticConstraint $ Satisfies (path [0]) Fixpoint.PTrue])
        , (State 1, [Transition "unknown" Fixpoint.PTrue [] unconstrainedConstraint])
        ,
            ( State 2
            ,
                [ Transition "natural" (value .>=. (0 :: Int)) [] unconstrainedConstraint
                , Transition "loop" Fixpoint.PTrue [State 2] unconstrainedConstraint
                ]
            )
        ]

-- | Three program states ordered exact-zero <: natural <: unknown.
transitiveSimilarAtoms :: Either AutomatonError Automaton
transitiveSimilarAtoms =
    mkAutomaton
        (State 0)
        [
            ( State 0
            ,
                [ Transition "use-specific" Fixpoint.PTrue [State 1] unconstrainedConstraint
                , Transition "use-natural" Fixpoint.PTrue [State 2] unconstrainedConstraint
                , Transition "use-unknown" Fixpoint.PTrue [State 3] unconstrainedConstraint
                ]
            )
        , (State 1, [Transition "specific" (value .==. (0 :: Int)) [] unconstrainedConstraint])
        , (State 2, [Transition "natural" (value .>=. (0 :: Int)) [] unconstrainedConstraint])
        , (State 3, [Transition "unknown" Fixpoint.PTrue [] unconstrainedConstraint])
        ]

-- | Two incomparable subtypes both related to one supertype.
overlappingSimilarAtoms :: Either AutomatonError Automaton
overlappingSimilarAtoms =
    mkAutomaton
        (State 0)
        [
            ( State 0
            ,
                [ Transition "use-zero" Fixpoint.PTrue [State 1] unconstrainedConstraint
                , Transition "use-one" Fixpoint.PTrue [State 2] unconstrainedConstraint
                , Transition "use-any" Fixpoint.PTrue [State 3] unconstrainedConstraint
                ]
            )
        , (State 1, [Transition "exact-zero" (value .==. (0 :: Int)) [] unconstrainedConstraint])
        , (State 2, [Transition "exact-one" (value .==. (1 :: Int)) [] unconstrainedConstraint])
        , (State 3, [Transition "unknown" Fixpoint.PTrue [] unconstrainedConstraint])
        ]

-- | The stricter transition uses the only base term as its argument.
dependentRepresentative :: Either AutomatonError Automaton
dependentRepresentative =
    mkAutomaton
        (State 2)
        [ (State 0, [Transition "unknown" Fixpoint.PTrue [] unconstrainedConstraint])
        , (State 1, [Transition "specific" (value .==. (0 :: Int)) [State 0] unconstrainedConstraint])
        , (State 2, [Transition "goal" Fixpoint.PTrue [State 1] unconstrainedConstraint])
        ]

-- | A recursive alternative and its only base share one target state.
recursiveRepresentative :: Either AutomatonError Automaton
recursiveRepresentative =
    mkAutomaton
        (State 0)
        [
            ( State 0
            ,
                [ Transition "unknown" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "specific" (value .==. (0 :: Int)) [State 0] unconstrainedConstraint
                ]
            )
        ]

-- | The subtype contains an unproductive cycle before minimization.
unproductiveRepresentative :: Either AutomatonError Automaton
unproductiveRepresentative =
    mkAutomaton
        (State 3)
        [ (State 0, [Transition "unknown" Fixpoint.PTrue [] unconstrainedConstraint])
        , (State 1, [Transition "specific" (value .==. (0 :: Int)) [State 2] unconstrainedConstraint])
        , (State 2, [Transition "loop" Fixpoint.PTrue [State 2] unconstrainedConstraint])
        ,
            ( State 3
            ,
                [ Transition "goal" Fixpoint.PTrue [State 0] unconstrainedConstraint
                , Transition "other-goal" Fixpoint.PTrue [State 1] unconstrainedConstraint
                ]
            )
        ]

-- | Two safe individual redirects form a cycle when applied together.
mutuallyDependentRepresentatives :: Either AutomatonError Automaton
mutuallyDependentRepresentatives =
    mkAutomaton
        (State 4)
        [ (State 0, [Transition "unknown-a" Fixpoint.PTrue [] unconstrainedConstraint])
        , (State 1, [Transition "unknown-b" Fixpoint.PTrue [] unconstrainedConstraint])
        , (State 2, [Transition "specific-a" (value .==. (0 :: Int)) [State 1] unconstrainedConstraint])
        , (State 3, [Transition "specific-b" (value .==. (0 :: Int)) [State 0] unconstrainedConstraint])
        , (State 4, [Transition "goal" Fixpoint.PTrue [State 2, State 3] unconstrainedConstraint])
        ]
