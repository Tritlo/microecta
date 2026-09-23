{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.MinimizeSpec (spec) where

import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldMatchList, shouldSatisfy)

import Data.CFTA.Refinement (
    Automaton,
    Entailment,
    Guard (Satisfies),
    LiquidSymbol (LiquidSymbol),
    MinimizeError (StaleSimilarity),
    Node (Mu, Node),
    Subtyping (..),
    Symbol,
    Transition,
    TransitionId (TransitionId),
    Verdict (No),
    automatonAlphabet,
    denotationAtMost,
    edgeChildren,
    minimize,
    mkEdge,
    nodeEdges,
    nodeMapChildren,
    path,
    reduce,
    refinementSubtypingBy,
    semanticConstraint,
    similarity,
    similarityPairs,
    transitionSymbol,
    unconstrainedConstraint,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (refinementFormula, (.==), (.>=))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Refinement.TestSupport (declarations)
import qualified Language.Fixpoint.Types as Fixpoint

spec :: Spec
spec =
    describe "similarity and minimization" $ do
        it "infers transition similarity and removes the supertype" $
            withZ3 declarations $ \solver -> do
                inferred <- similarity (atomSubtyping solver) similarAtoms
                case inferred of
                    Left err -> expectationFailure $ show err
                    Right related -> do
                        similarityPairs related
                            `shouldBe` [(TransitionId similarAtoms naturalAtom, TransitionId similarAtoms unknownAtom)]
                        minimize similarAtoms related `shouldBe` Right (Node [naturalAtom])

        it "rejects a similarity snapshot when transition contents change at the same addresses" $
            withZ3 declarations $ \solver -> do
                inferred <- similarity (atomSubtyping solver) similarAtoms
                case inferred of
                    Left err -> expectationFailure $ show err
                    Right related -> do
                        let changed =
                                nodeMapChildren
                                    (\edge -> mkEdge (transitionLabel edge) [] (semanticConstraint $ Satisfies (path []) Fixpoint.PTrue))
                                    similarAtoms
                        minimize changed related `shouldBe` Left StaleSimilarity

        it "rejects a similarity snapshot when only the root changes" $
            withZ3 declarations $ \solver -> do
                inferred <- similarity (atomSubtyping solver) separatedSimilarAtoms
                case inferred of
                    Left err -> expectationFailure $ show err
                    Right related -> minimize naturalNode related `shouldBe` Left StaleSimilarity

        it "checks snapshots even when the similarity set is empty" $ do
            inferred <- similarity (Subtyping $ \_ _ _ -> pure No) similarAtoms
            case inferred of
                Left err -> expectationFailure $ show err
                Right related -> do
                    similarityPairs related `shouldBe` []
                    minimize naturalNode related `shouldBe` Left StaleSimilarity

        it "redirects incoming edges to the retained subtype target" $
            withZ3 declarations $ \solver -> do
                reducedResult <- reduce solver (atomSubtyping solver) separatedSimilarAtoms
                case reducedResult of
                    Left err -> expectationFailure $ show err
                    Right reduced -> do
                        map edgeChildren (nodeEdges reduced) `shouldMatchList` [[naturalNode], [naturalNode]]
                        automatonAlphabet reduced `shouldSatisfy` Set.notMember (LiquidSymbol "unknown" Fixpoint.PTrue)

        it "keeps unrelated alternatives at a removed transition's target" $
            withZ3 declarations $ \solver ->
                checkMinimization (atomSubtyping solver) sharedSupertypeState $ \reduced -> do
                    map edgeChildren (nodeEdges reduced)
                        `shouldMatchList` [[naturalNode], [Node [otherAtom]], [naturalNode]]
                    denotationAtMost solver 1 reduced >>= (\terms -> fmap length terms `shouldBe` Right 3)

        it "does not strand the root during minimization" $
            withZ3 declarations $ \solver -> do
                inferred <- similarity (atomSubtyping solver) finalStateSupertype
                case inferred of
                    Left err -> expectationFailure $ show err
                    Right related -> minimize finalStateSupertype related `shouldBe` Right finalStateSupertype

        it "can remove a root transition when another root derivation remains" $
            withZ3 declarations $ \solver ->
                checkMinimization (atomSubtyping solver) finalStateWithAlternative $ \reduced -> do
                    reduced `shouldBe` Node [otherAtom]
                    denotationAtMost solver 0 reduced
                        >>= (`shouldBe` Right [Tree.Node (LiquidSymbol "other" Fixpoint.PTrue) []])

        it "allows multiple representatives for one target and substitutes repeated nodes together" $
            withZ3 declarations $ \solver ->
                checkMinimization (twoClassSubtyping solver) multipleRepresentatives $ \reduced -> do
                    [edgeChildren edge | edge <- nodeEdges reduced, transitionSymbol edge == "pair"]
                        `shouldMatchList` [[Node [otherAtom], Node [otherAtom]], [specificANode, specificANode], [specificBNode, specificBNode]]
                    denotationAtMost solver 1 reduced >>= (\terms -> fmap length terms `shouldBe` Right 5)

        it "composes substitutions for distinct source nodes on earlier copies" $
            withZ3 declarations $ \solver ->
                checkMinimization (twoClassSubtyping solver) composedRepresentatives $ \reduced -> do
                    [edgeChildren edge | edge <- nodeEdges reduced, transitionSymbol edge == "pair"]
                        `shouldMatchList` [ [otherANode, otherBNode]
                                          , [specificANode, otherBNode]
                                          , [otherANode, specificBNode]
                                          , [specificANode, specificBNode]
                                          ]
                    denotationAtMost solver 1 reduced >>= (\terms -> fmap length terms `shouldBe` Right 6)

        it "keeps a redirected copy when its original supertype transition is removed" $
            withZ3 declarations $ \solver ->
                checkMinimization (twoClassSubtyping solver) copiedSupertype $ \reduced -> do
                    [edgeChildren edge | edge <- nodeEdges reduced, transitionSymbol edge == "goal"]
                        `shouldMatchList` [[Node [Transition "unknown-b" Fixpoint.PTrue [specificANode] unconstrainedConstraint]], [specificBNode]]
                    denotationAtMost solver 2 reduced >>= (\terms -> fmap length terms `shouldBe` Right 4)

        it "applies M-Trans transitively over one similarity snapshot" $
            withZ3 declarations $ \solver ->
                checkMinimization (threeAtomSubtyping solver) transitiveSimilarAtoms $ \reduced ->
                    map edgeChildren (nodeEdges reduced) `shouldBe` replicate 3 [Node [specificAtom]]

        it "uses one inferred representative for overlapping subtypes" $
            withZ3 declarations $ \solver ->
                checkMinimization (overlappingAtomSubtyping solver) overlappingSimilarAtoms $ \reduced -> do
                    length (nodeEdges reduced) `shouldBe` 3
                    map edgeChildren (nodeEdges reduced) `shouldSatisfy` notElem [Node [unknownAtom]]
                    denotationAtMost solver 1 reduced >>= (\terms -> fmap length terms `shouldBe` Right 3)

        it "retains a base required by a stricter representative" $
            withZ3 declarations $ \solver ->
                checkRetainedBatch solver (threeAtomSubtyping solver) dependentRepresentative 1

        it "retains a base required by a recursive alternative in the same node" $
            withZ3 declarations $ \solver ->
                checkRetainedBatch solver (threeAtomSubtyping solver) recursiveRepresentative 4

        it "retains a productive base when its subtype has no finite derivation" $
            withZ3 declarations $ \solver ->
                checkRetainedBatch solver (threeAtomSubtyping solver) unproductiveRepresentative 1

        it "retains batches whose combined redirects create a dependency cycle" $
            withZ3 declarations $ \solver ->
                checkRetainedBatch solver (twoClassSubtyping solver) mutuallyDependentRepresentatives 1

        it "retains a batch whose copied guard would inspect a recursive node" $
            withZ3 declarations $ \solver ->
                checkRetainedBatch solver (atomSubtyping solver) cyclicGuardRepresentative 4

-- | Inspect a successful schedule while reporting inference failures.
checkMinimization :: Subtyping -> Automaton -> (Automaton -> IO ()) -> IO ()
checkMinimization subtyping original check = do
    inferred <- similarity subtyping original
    case inferred of
        Left err -> expectationFailure $ show err
        Right related -> case minimize original related of
            Left err -> expectationFailure $ show err
            Right reduced -> check reduced

-- | Check that minimization retains the finite derivations required by a batch.
checkRetainedBatch :: Entailment -> Subtyping -> Automaton -> Int -> IO ()
checkRetainedBatch solver subtyping original expected = do
    before <- denotationAtMost solver 3 original
    fmap length before `shouldBe` Right expected
    inferred <- similarity subtyping original
    case inferred of
        Left err -> expectationFailure $ show err
        Right related -> minimize original related `shouldBe` Right original

-- | The complete label of a transition.
transitionLabel :: Transition -> LiquidSymbol
transitionLabel (Transition symbol refinement _ _) = LiquidSymbol symbol refinement

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

-- | Two independent source type classes for node-substitution schedules.
twoClassSubtyping :: Entailment -> Subtyping
twoClassSubtyping solver = refinementSubtypingBy solver classify
  where
    classify transition
        | transitionSymbol transition `elem` ["specific-a", "unknown-a"] = Just False
        | transitionSymbol transition `elem` ["specific-b", "unknown-b"] = Just True
        | otherwise = Nothing

-- | An unrefined, unconstrained leaf transition.
plain :: Symbol -> Transition
plain symbol = Transition symbol Fixpoint.PTrue [] unconstrainedConstraint

-- | An unrefined constructor with no constraint.
wrap :: Symbol -> [Automaton] -> Transition
wrap symbol children = Transition symbol Fixpoint.PTrue children unconstrainedConstraint

unknownAtom, naturalAtom, otherAtom, specificAtom :: Transition
unknownAtom = plain "unknown"
naturalAtom = Transition "natural" (refinementFormula (\v -> v .>= 0)) [] unconstrainedConstraint
otherAtom = plain "other"
specificAtom = Transition "specific" (refinementFormula (\v -> v .== 0)) [] unconstrainedConstraint

naturalNode, specificANode, specificBNode, otherANode, otherBNode :: Automaton
naturalNode = Node [naturalAtom]
specificANode = Node [Transition "specific-a" (refinementFormula (\v -> v .== 0)) [] unconstrainedConstraint]
specificBNode = Node [Transition "specific-b" (refinementFormula (\v -> v .== 1)) [] unconstrainedConstraint]
otherANode = Node [plain "other-a"]
otherBNode = Node [plain "other-b"]

-- | Two refinements sharing one node, as in an alternative row.
similarAtoms :: Automaton
similarAtoms = Node [unknownAtom, naturalAtom]

-- | Paper-style representatives with one node per program transition.
separatedSimilarAtoms :: Automaton
separatedSimilarAtoms =
    Node
        [ wrap "specific-box" [naturalNode]
        , wrap "general-box" [Node [unknownAtom]]
        ]

-- | A supertype transition shares its node with an unrelated alternative.
sharedSupertypeState :: Automaton
sharedSupertypeState =
    Node
        [ wrap "specific-box" [naturalNode]
        , wrap "general-box" [Node [unknownAtom, otherAtom]]
        ]

-- | Removing the only root transition would leave no accepted derivation.
finalStateSupertype :: Automaton
finalStateSupertype = Node [wrap "unknown" [naturalNode]]

-- | A root supertype can be removed while another root alternative remains.
finalStateWithAlternative :: Automaton
finalStateWithAlternative = Node [wrap "unknown" [naturalNode], otherAtom]

-- | Two removed transitions share a node but use different representatives.
multipleRepresentatives :: Automaton
multipleRepresentatives =
    Node
        [ wrap "pair" [shared, shared]
        , wrap "use-a" [specificANode]
        , wrap "use-b" [specificBNode]
        ]
  where
    shared = Node [plain "unknown-a", plain "unknown-b", otherAtom]

-- | Independent substitutions can affect each argument of a copied transition.
composedRepresentatives :: Automaton
composedRepresentatives =
    Node
        [ wrap "pair" [Node [plain "unknown-a", plain "other-a"], Node [plain "unknown-b", plain "other-b"]]
        , wrap "use-a" [specificANode]
        , wrap "use-b" [specificBNode]
        ]

-- | The first step copies a supertype whose original is removed by the second.
copiedSupertype :: Automaton
copiedSupertype =
    Node
        [ wrap "goal" [Node [wrap "unknown-b" [Node [plain "unknown-a"]]]]
        , wrap "use-a" [specificANode]
        , wrap "use-b" [specificBNode]
        ]

-- | A representative's other alternative makes its node recursive.
cyclicGuardRepresentative :: Automaton
cyclicGuardRepresentative =
    Node
        [ Transition "goal" Fixpoint.PTrue [Node [unknownAtom]] $ semanticConstraint $ Satisfies (path [0]) Fixpoint.PTrue
        , wrap "use" [Mu $ \self -> Node [naturalAtom, wrap "loop" [self]]]
        ]

-- | Three program nodes ordered exact-zero <: natural <: unknown.
transitiveSimilarAtoms :: Automaton
transitiveSimilarAtoms =
    Node
        [ wrap "use-specific" [Node [specificAtom]]
        , wrap "use-natural" [naturalNode]
        , wrap "use-unknown" [Node [unknownAtom]]
        ]

-- | Two incomparable subtypes both related to one supertype.
overlappingSimilarAtoms :: Automaton
overlappingSimilarAtoms =
    Node
        [ wrap "use-zero" [Node [Transition "exact-zero" (refinementFormula (\v -> v .== 0)) [] unconstrainedConstraint]]
        , wrap "use-one" [Node [Transition "exact-one" (refinementFormula (\v -> v .== 1)) [] unconstrainedConstraint]]
        , wrap "use-any" [Node [unknownAtom]]
        ]

-- | The stricter transition uses the only base term as its argument.
dependentRepresentative :: Automaton
dependentRepresentative =
    Node
        [ wrap
            "goal"
            [Node [Transition "specific" (refinementFormula (\v -> v .== 0)) [Node [unknownAtom]] unconstrainedConstraint]]
        ]

-- | A recursive alternative and its only base share one node.
recursiveRepresentative :: Automaton
recursiveRepresentative =
    Mu $ \self -> Node [unknownAtom, Transition "specific" (refinementFormula (\v -> v .== 0)) [self] unconstrainedConstraint]

-- | The subtype contains an unproductive cycle before minimization.
unproductiveRepresentative :: Automaton
unproductiveRepresentative =
    Node
        [ wrap "goal" [Node [unknownAtom]]
        , wrap "other-goal" [Node [Transition "specific" (refinementFormula (\v -> v .== 0)) [loop] unconstrainedConstraint]]
        ]
  where
    loop = Mu $ \self -> Node [wrap "loop" [self]]

-- | Two safe individual redirects form a cycle when applied together.
mutuallyDependentRepresentatives :: Automaton
mutuallyDependentRepresentatives =
    Node
        [ wrap
            "goal"
            [ Node [Transition "specific-a" (refinementFormula (\v -> v .== 0)) [Node [plain "unknown-b"]] unconstrainedConstraint]
            , Node [Transition "specific-b" (refinementFormula (\v -> v .== 0)) [Node [plain "unknown-a"]] unconstrainedConstraint]
            ]
        ]
