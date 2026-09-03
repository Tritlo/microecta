module Data.LTA.SemanticsSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import qualified Data.Map.Strict as Map

import Data.ECTA.Paths (mkEqConstraints)
import Data.LTA (
    Automaton,
    AutomatonError,
    Entailment,
    EnumerationError,
    Guard (Entails, Not, Same, Satisfies, Substitute),
    LiquidConstraint,
    LiquidTerm (LiquidTerm),
    MinimizeError (FinalSimilarityTarget, SharedSimilarityTarget),
    PruneError (ResidualLTAConstraint),
    RefinementRelation (..),
    SemanticIntersection (..),
    State (State),
    Substitution (Substitution),
    Subtyping (..),
    Transition,
    TransitionId (TransitionId),
    Verdict (No, Yes),
    accepts,
    automatonTransitions,
    denotationAtMost,
    equalityConstraint,
    minimize,
    mkAutomaton,
    path,
    prune,
    pruneSemantics,
    reduce,
    refinementRelation,
    refinementSubtypingBy,
    semanticConstraint,
    semanticIntersection,
    similarity,
    similarityPairs,
    transitionChildren,
    transitionSymbol,
    transitionsAt,
    unconstrainedConstraint,
    pattern Transition,
 )
import Data.LTA.LiquidFixpoint (withZ3)
import Data.LTA.Refinement ((./=.), (.==.), (.>=.))
import qualified Data.Tree.FTA as FTA
import qualified Language.Fixpoint.Types as Fixpoint

value :: Fixpoint.Expr
value = Fixpoint.EVar $ Fixpoint.symbol ("v" :: String)

spec :: Spec
spec =
    describe "semantic refinement comparison" $ do
        it "recognises strict subtyping" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver ->
                refinementRelation solver (value .==. (0 :: Int)) (value .>=. (0 :: Int))
                    >>= (`shouldBe` StrictSubtype)

        it "recognises logical equivalence" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver ->
                refinementRelation solver (value .>=. (0 :: Int)) (value .>=. (0 :: Int))
                    >>= (`shouldBe` Equivalent)

        it "does not merge incomparable refinements" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver ->
                refinementRelation solver (value .>=. (0 :: Int)) (value ./=. (0 :: Int))
                    >>= (`shouldBe` Incomparable)

        it "retains the antecedent when semantic intersection succeeds" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver -> do
                let exactZero = value .==. (0 :: Int)
                semanticIntersection solver exactZero (value .>=. (0 :: Int))
                    >>= (`shouldBe` RetainedAntecedent exactZero)

        it "does not reverse a directional semantic intersection" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver -> do
                let exactZero = value .==. (0 :: Int)
                semanticIntersection solver (value .>=. (0 :: Int)) exactZero
                    >>= (`shouldBe` BottomIntersection)

        it "reduces incomparable semantic transitions to bottom" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver ->
                semanticIntersection solver (value .>=. (0 :: Int)) (value ./=. (0 :: Int))
                    >>= (`shouldBe` BottomIntersection)

        it "splits heterogeneous states at semantic guard positions" $
            withZ3 declarations $ \solver ->
                checkPrunedLanguage solver semanticPairs pairTerms 5

        it "computes Figure 12's bounded denotation directly" $
            withZ3 declarations $ \solver ->
                case semanticPairs of
                    Left err -> expectationFailure $ show err
                    Right automaton -> do
                        terms <- denotationAtMost solver 1 automaton
                        fmap length terms `shouldBe` Right 5
                        case Map.findWithDefault [] (State 0) $ automatonTransitions automaton of
                            [root] -> length (transitionsAt automaton root $ path [0]) `shouldBe` 3
                            roots -> expectationFailure $ "unexpected Figure 12 roots: " <> show roots

        it "splits nested semantic positions without enumerating complete terms" $
            withZ3 declarations $ \solver ->
                checkPrunedLanguage solver nestedPairs nestedPairTerms 5

        it "partitions substitution positions by their value-naming symbol" $
            withZ3 declarations $ \solver ->
                checkPrunedLanguage solver substitutedOutputs substitutionTerms 2

        it "uses FTA product intersection to narrow syntactic equality" $
            withZ3 declarations $ \solver ->
                case syntacticPairs of
                    Left err -> expectationFailure $ show err
                    Right original -> do
                        result <- pruneSemantics solver original
                        case result of
                            Left err -> expectationFailure $ show err
                            Right reduced ->
                                case Map.findWithDefault [] (State 0) $ automatonTransitions reduced of
                                    [root] -> do
                                        FTA.transitionGuard root
                                            `shouldBe` mkEqConstraints [[path [0], path [1]]]
                                        case transitionChildren root of
                                            leftState : _ -> do
                                                map
                                                    transitionSymbol
                                                    (Map.findWithDefault [] leftState $ automatonTransitions reduced)
                                                    `shouldBe` ["shared"]
                                                let lifted = FTA.mapGuards equalityConstraint reduced
                                                traverse (accepts solver lifted) syntacticPairTerms
                                                    >>= (`shouldBe` [Yes, No, No])
                                            [] -> expectationFailure "pair transition lost its children"
                                    roots -> expectationFailure $ "unexpected root row: " <> show roots

        it "applies syntactic intersection below a nested position" $
            withZ3 declarations $ \solver ->
                case nestedSyntacticPairs of
                    Left err -> expectationFailure $ show err
                    Right original -> do
                        result <- prune solver original
                        case result of
                            Left err -> expectationFailure $ show err
                            Right reduced ->
                                case Map.findWithDefault [] (State 0) $ automatonTransitions reduced of
                                    [root] ->
                                        case transitionChildren root of
                                            leftState : _ ->
                                                case Map.findWithDefault [] leftState $ automatonTransitions reduced of
                                                    [box] ->
                                                        case transitionChildren box of
                                                            [nestedState] ->
                                                                map
                                                                    transitionSymbol
                                                                    (Map.findWithDefault [] nestedState $ automatonTransitions reduced)
                                                                    `shouldBe` ["shared"]
                                                            children -> expectationFailure $ "unexpected box children: " <> show children
                                                    row -> expectationFailure $ "unexpected nested row: " <> show row
                                            [] -> expectationFailure "pair transition lost its children"
                                    roots -> expectationFailure $ "unexpected root row: " <> show roots

        it "keeps Boolean syntactic constraints in the LTA when ECTA cannot express them" $
            withZ3 declarations $ \solver ->
                case negativeSyntacticPairs of
                    Left err -> expectationFailure $ show err
                    Right original -> do
                        reduced <- prune solver original
                        case reduced of
                            Left err -> expectationFailure $ show err
                            Right lta ->
                                traverse (accepts solver lta) syntacticPairTerms
                                    >>= (`shouldBe` [No, Yes, Yes])
                        pruneSemantics solver original
                            >>= (`shouldBe` Left (ResidualLTAConstraint (State 0) negativeEquality))

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

        it "rejects redirection from a state with unrelated alternatives" $
            withZ3 declarations $ \solver ->
                case sharedSupertypeState of
                    Left err -> expectationFailure $ show err
                    Right automaton -> do
                        inferred <- similarity (atomSubtyping solver) automaton
                        case inferred of
                            Left err -> expectationFailure $ show err
                            Right related ->
                                minimize automaton related
                                    `shouldBe` Left (SharedSimilarityTarget $ State 2)

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
                                    `shouldBe` Left (FinalSimilarityTarget $ State 2)

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

-- | Compare recognition before and after pruning, including the expected accepted count.
checkPrunedLanguage ::
    Entailment ->
    Either error Automaton ->
    [LiquidTerm] ->
    Int ->
    IO ()
checkPrunedLanguage solver constructed terms expected =
    case constructed of
        Left _ -> expectationFailure "test LTA was structurally invalid"
        Right original -> do
            result <- prune solver original
            case result of
                Left err -> expectationFailure $ show err
                Right reduced -> do
                    before <- traverse (accepts solver original) terms
                    after <- traverse (accepts solver reduced) terms
                    after `shouldBe` before
                    length (filter (== Yes) after) `shouldBe` expected
                    beforeDenotation <- denotationAtMost solver 3 original
                    afterDenotation <- denotationAtMost solver 3 reduced
                    equivalentTermSets beforeDenotation afterDenotation `shouldBe` True

-- | Compare denotations as sets without requiring an ordering for Fixpoint expressions.
equivalentTermSets ::
    Either EnumerationError [LiquidTerm] ->
    Either EnumerationError [LiquidTerm] ->
    Bool
equivalentTermSets (Right left) (Right right) =
    all (`elem` right) left && all (`elem` left) right
equivalentTermSets _ _ = False

{- | Figure 12's LTA: @f(phi1, phi2)@ where @phi1 => phi2@.

Every formula is an ordinary nullary ranked-alphabet symbol. The implementation
encodes that symbol as @LiquidSymbol "predicate" formula@; it is not metadata
outside the automaton.
-}
semanticPairs :: Either AutomatonError Automaton
semanticPairs =
    mkAutomaton
        (State 0)
        [ (State 0, [Transition "pair" Fixpoint.PTrue [State 1, State 1] pairEntailment])
        , (State 1, predicateTransitions)
        ]

-- | The same relation, with its left observation one constructor below the root.
nestedPairs :: Either AutomatonError Automaton
nestedPairs =
    mkAutomaton
        (State 0)
        [ (State 0, [Transition "pair" Fixpoint.PTrue [State 1, State 2] nestedEntailment])
        , (State 1, [Transition "box" Fixpoint.PTrue [State 2] unconstrainedConstraint])
        , (State 2, predicateTransitions)
        ]

-- | A substitution guard whose actual names select matching output refinements.
substitutedOutputs :: Either AutomatonError Automaton
substitutedOutputs =
    mkAutomaton
        (State 0)
        [
            ( State 0
            ,
                [ Transition
                    "application"
                    Fixpoint.PTrue
                    [State 1, State 2, State 3]
                    substitutedRequirement
                ]
            )
        ,
            ( State 1
            ,
                [ Transition "x" (value .==. (0 :: Int)) [] unconstrainedConstraint
                , Transition "y" (value .==. (1 :: Int)) [] unconstrainedConstraint
                ]
            )
        , (State 2, [Transition "n" Fixpoint.PTrue [] unconstrainedConstraint])
        ,
            ( State 3
            ,
                [ Transition "output-x" (value .==. variable "x") [] unconstrainedConstraint
                , Transition "output-y" (value .==. variable "y") [] unconstrainedConstraint
                ]
            )
        ]

-- | Two overlapping structural languages tied by syntactic equality.
syntacticPairs :: Either AutomatonError Automaton
syntacticPairs =
    mkAutomaton
        (State 0)
        [ (State 0, [Transition "pair" Fixpoint.PTrue [State 1, State 2] $ semanticConstraint $ Same (path [0]) (path [1])])
        ,
            ( State 1
            , [Transition "left" Fixpoint.PTrue [] unconstrainedConstraint, Transition "shared" Fixpoint.PTrue [] unconstrainedConstraint]
            )
        ,
            ( State 2
            , [Transition "shared" Fixpoint.PTrue [] unconstrainedConstraint, Transition "right" Fixpoint.PTrue [] unconstrainedConstraint]
            )
        ]

-- | One accepted equal pair followed by two rejected unequal pairs.
syntacticPairTerms :: [LiquidTerm]
syntacticPairTerms =
    [ pair "shared" "shared"
    , pair "left" "shared"
    , pair "shared" "right"
    ]
  where
    pair left right =
        LiquidTerm
            "pair"
            Fixpoint.PTrue
            [LiquidTerm left Fixpoint.PTrue [], LiquidTerm right Fixpoint.PTrue []]

-- | The same structural overlap reached below a wrapper on the left.
nestedSyntacticPairs :: Either AutomatonError Automaton
nestedSyntacticPairs =
    mkAutomaton
        (State 0)
        [ (State 0, [Transition "pair" Fixpoint.PTrue [State 1, State 2] $ semanticConstraint $ Same (path [0, 0]) (path [1])])
        ,
            ( State 1
            ,
                [ Transition "box" Fixpoint.PTrue [State 3] unconstrainedConstraint
                , Transition "empty" Fixpoint.PTrue [] unconstrainedConstraint
                ]
            )
        ,
            ( State 2
            , [Transition "shared" Fixpoint.PTrue [] unconstrainedConstraint, Transition "right" Fixpoint.PTrue [] unconstrainedConstraint]
            )
        ,
            ( State 3
            , [Transition "left" Fixpoint.PTrue [] unconstrainedConstraint, Transition "shared" Fixpoint.PTrue [] unconstrainedConstraint]
            )
        ]

-- | Negated equality is a valid LTA constraint but is not an ECTA constraint.
negativeSyntacticPairs :: Either AutomatonError Automaton
negativeSyntacticPairs =
    mkAutomaton
        (State 0)
        [ (State 0, [Transition "pair" Fixpoint.PTrue [State 1, State 2] $ semanticConstraint negativeEquality])
        ,
            ( State 1
            , [Transition "left" Fixpoint.PTrue [] unconstrainedConstraint, Transition "shared" Fixpoint.PTrue [] unconstrainedConstraint]
            )
        ,
            ( State 2
            , [Transition "shared" Fixpoint.PTrue [] unconstrainedConstraint, Transition "right" Fixpoint.PTrue [] unconstrainedConstraint]
            )
        ]

negativeEquality :: Guard
negativeEquality = Not $ Same (path [0]) (path [1])

-- | All concrete pairs from the heterogeneous atom state.
pairTerms :: [LiquidTerm]
pairTerms = [LiquidTerm "pair" Fixpoint.PTrue [left, right] | left <- predicates, right <- predicates]

-- | All concrete pairs with the left atom below a box constructor.
nestedPairTerms :: [LiquidTerm]
nestedPairTerms =
    [ LiquidTerm
        "pair"
        Fixpoint.PTrue
        [LiquidTerm "box" Fixpoint.PTrue [left], right]
    | left <- predicates
    , right <- predicates
    ]

-- | Every actual-name and output-refinement combination.
substitutionTerms :: [LiquidTerm]
substitutionTerms =
    [ LiquidTerm
        "application"
        Fixpoint.PTrue
        [actual, LiquidTerm "n" Fixpoint.PTrue [], output]
    | actual <- namedActuals
    , output <-
        [ LiquidTerm "output-x" (value .==. variable "x") []
        , LiquidTerm "output-y" (value .==. variable "y") []
        ]
    ]

-- | Three representative refinement transitions.
predicateTransitions :: [Transition]
predicateTransitions =
    [ Transition "predicate" (value .==. (0 :: Int)) [] unconstrainedConstraint
    , Transition "predicate" (value .==. (1 :: Int)) [] unconstrainedConstraint
    , Transition "predicate" (value .>=. (0 :: Int)) [] unconstrainedConstraint
    ]

-- | Concrete formula terms matching 'predicateTransitions'.
predicates :: [LiquidTerm]
predicates =
    [ LiquidTerm "predicate" (value .==. (0 :: Int)) []
    , LiquidTerm "predicate" (value .==. (1 :: Int)) []
    , LiquidTerm "predicate" (value .>=. (0 :: Int)) []
    ]

-- | Variable leaves used by the substitution example.
namedActuals :: [LiquidTerm]
namedActuals =
    [ LiquidTerm "x" (value .==. (0 :: Int)) []
    , LiquidTerm "y" (value .==. (1 :: Int)) []
    ]

-- | Direct semantic relation between sibling positions.
pairEntailment :: LiquidConstraint
pairEntailment = semanticConstraint $ Entails (path [0]) (path [1])

-- | Semantic relation whose antecedent is below a wrapper.
nestedEntailment :: LiquidConstraint
nestedEntailment = semanticConstraint $ Entails (path [0, 0]) (path [1])

-- | Substitute the actual value name for the formal before checking the output.
substitutedRequirement :: LiquidConstraint
substitutedRequirement =
    semanticConstraint $
        Substitute
            [Substitution (path [0]) (path [1])]
            (Satisfies (path [2]) $ value .==. variable "n")

-- | Integer expression naming one solver variable.
variable :: String -> Fixpoint.Expr
variable = Fixpoint.EVar . Fixpoint.symbol

-- | Declarations shared by the pruning examples.
declarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
declarations =
    [ (Fixpoint.symbol name, Fixpoint.FInt)
    | name <- ["v", "x", "y", "n"] :: [String]
    ]

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

-- | Invalid minimization shape: the supertype target also owns another term.
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

-- | Invalid paper shape: the supertype transition itself targets the final state.
finalStateSupertype :: Either AutomatonError Automaton
finalStateSupertype =
    mkAutomaton
        (State 2)
        [ (State 1, [Transition "natural" (value .>=. (0 :: Int)) [] unconstrainedConstraint])
        , (State 2, [Transition "unknown" Fixpoint.PTrue [] unconstrainedConstraint])
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
