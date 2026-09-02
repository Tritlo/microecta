module Data.LTA.SemanticsSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import qualified Data.Map.Strict as Map

import Data.LTA (
    Automaton,
    AutomatonError,
    Entailment,
    Guard (Entails, Satisfies, Substitute, Top),
    LiquidTerm (LiquidTerm),
    MinimizeError (SharedSimilarityTarget),
    RefinementRelation (..),
    SemanticIntersection (..),
    State (State),
    Substitution (Substitution),
    Subtyping,
    Transition,
    TransitionId (TransitionId),
    Verdict (Yes),
    accepts,
    automatonTransitions,
    minimize,
    mkAutomaton,
    path,
    prune,
    reduce,
    refinementRelation,
    refinementSubtypingBy,
    semanticIntersection,
    similarity,
    similarityPairs,
    transitionChildren,
    transitionSymbol,
    pattern Transition,
 )
import Data.LTA.LiquidFixpoint (withZ3)
import Data.LTA.Refinement ((./=.), (.==.), (.>=.))
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

        it "splits nested semantic positions without enumerating complete terms" $
            withZ3 declarations $ \solver ->
                checkPrunedLanguage solver nestedPairs nestedPairTerms 5

        it "partitions substitution positions by their value-naming symbol" $
            withZ3 declarations $ \solver ->
                checkPrunedLanguage solver substitutedOutputs substitutionTerms 2

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

-- | A shared atom state with three different refinement roots.
semanticPairs :: Either AutomatonError Automaton
semanticPairs =
    mkAutomaton
        (State 0)
        [ (State 0, [Transition "pair" Fixpoint.PTrue [State 1, State 1] pairEntailment])
        , (State 1, atomTransitions)
        ]

-- | The same relation, with its left observation one constructor below the root.
nestedPairs :: Either AutomatonError Automaton
nestedPairs =
    mkAutomaton
        (State 0)
        [ (State 0, [Transition "pair" Fixpoint.PTrue [State 1, State 2] nestedEntailment])
        , (State 1, [Transition "box" Fixpoint.PTrue [State 2] Top])
        , (State 2, atomTransitions)
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
                [ Transition "x" (value .==. (0 :: Int)) [] Top
                , Transition "y" (value .==. (1 :: Int)) [] Top
                ]
            )
        , (State 2, [Transition "n" Fixpoint.PTrue [] Top])
        ,
            ( State 3
            ,
                [ Transition "output-x" (value .==. variable "x") [] Top
                , Transition "output-y" (value .==. variable "y") [] Top
                ]
            )
        ]

-- | All concrete pairs from the heterogeneous atom state.
pairTerms :: [LiquidTerm]
pairTerms = [LiquidTerm "pair" Fixpoint.PTrue [left, right] | left <- atoms, right <- atoms]

-- | All concrete pairs with the left atom below a box constructor.
nestedPairTerms :: [LiquidTerm]
nestedPairTerms =
    [ LiquidTerm
        "pair"
        Fixpoint.PTrue
        [LiquidTerm "box" Fixpoint.PTrue [left], right]
    | left <- atoms
    , right <- atoms
    ]

-- | Every actual-name and output-refinement combination.
substitutionTerms :: [LiquidTerm]
substitutionTerms =
    [ LiquidTerm
        "application"
        Fixpoint.PTrue
        [actual, LiquidTerm "n" Fixpoint.PTrue [], output]
    | actual <- take 2 atoms
    , output <-
        [ LiquidTerm "output-x" (value .==. variable "x") []
        , LiquidTerm "output-y" (value .==. variable "y") []
        ]
    ]

-- | Three representative refinement transitions.
atomTransitions :: [Transition]
atomTransitions =
    [ Transition "x" (value .==. (0 :: Int)) [] Top
    , Transition "y" (value .==. (1 :: Int)) [] Top
    , Transition "natural" (value .>=. (0 :: Int)) [] Top
    ]

-- | Concrete terms matching 'atomTransitions'.
atoms :: [LiquidTerm]
atoms =
    [ LiquidTerm "x" (value .==. (0 :: Int)) []
    , LiquidTerm "y" (value .==. (1 :: Int)) []
    , LiquidTerm "natural" (value .>=. (0 :: Int)) []
    ]

-- | Direct semantic relation between sibling positions.
pairEntailment :: Guard
pairEntailment = Entails (path [0]) (path [1])

-- | Semantic relation whose antecedent is below a wrapper.
nestedEntailment :: Guard
nestedEntailment = Entails (path [0, 0]) (path [1])

-- | Substitute the actual value name for the formal before checking the output.
substitutedRequirement :: Guard
substitutedRequirement =
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

-- | Two refinements sharing one target state, as in an alternative row.
similarAtoms :: Either AutomatonError Automaton
similarAtoms =
    mkAutomaton
        (State 0)
        [
            ( State 0
            ,
                [ Transition "unknown" Fixpoint.PTrue [] Top
                , Transition "natural" (value .>=. (0 :: Int)) [] Top
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
                [ Transition "specific-box" Fixpoint.PTrue [State 1] Top
                , Transition "general-box" Fixpoint.PTrue [State 2] Top
                ]
            )
        , (State 1, [Transition "natural" (value .>=. (0 :: Int)) [] Top])
        , (State 2, [Transition "unknown" Fixpoint.PTrue [] Top])
        ]

-- | Invalid minimization shape: the supertype target also owns another term.
sharedSupertypeState :: Either AutomatonError Automaton
sharedSupertypeState =
    mkAutomaton
        (State 0)
        [
            ( State 0
            ,
                [ Transition "specific-box" Fixpoint.PTrue [State 1] Top
                , Transition "general-box" Fixpoint.PTrue [State 2] Top
                ]
            )
        , (State 1, [Transition "natural" (value .>=. (0 :: Int)) [] Top])
        ,
            ( State 2
            ,
                [ Transition "unknown" Fixpoint.PTrue [] Top
                , Transition "other" Fixpoint.PTrue [] Top
                ]
            )
        ]
