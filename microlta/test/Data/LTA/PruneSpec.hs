module Data.LTA.PruneSpec (spec) where

import qualified Data.Tree as Tree
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import Data.List (permutations)
import qualified Data.Map.Strict as Map

import qualified Data.CFTA as FTA
import Data.CFTA.Equality.Constraints (mkEqConstraints)
import Data.LTA (
    Automaton,
    AutomatonError,
    Entailment (Entailment),
    EnumerationError,
    Guard (And, Entails, Not, Or, Same, Satisfies, Substitute, Top),
    LiquidConstraint,
    LiquidSymbol (LiquidSymbol),
    PruneError (PruneUnknown, ResidualLTAConstraint),
    State (State),
    Substitution (Substitution),
    Transition,
    Verdict (No, Unknown, Yes),
    accepts,
    automatonTransitions,
    denotationAtMost,
    equalityConstraint,
    lowerToEqualityAutomaton,
    mkAutomaton,
    path,
    prune,
    pruneToECTA,
    semanticConstraint,
    transitionChildren,
    transitionSymbol,
    transitionsAt,
    unconstrainedConstraint,
    pattern Transition,
 )
import qualified Data.LTA.Guard as Guard
import Data.LTA.LiquidFixpoint (withZ3)
import Data.LTA.Refinement (value, variable, (.==.), (.>=.))
import Data.LTA.TestSupport (declarations)
import qualified Language.Fixpoint.Types as Fixpoint

spec :: Spec
spec =
    describe "semantic pruning" $ do
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

        it "preserves terms with an absent path under negation" $
            withZ3 declarations $ \solver ->
                checkPrunedLanguage
                    solver
                    (optionalDescendant $ Not $ Satisfies (path [0, 0]) Fixpoint.PTrue)
                    optionalDescendantTerms
                    1

        it "preserves terms with an absent path in a satisfied disjunction" $
            withZ3 declarations $ \solver ->
                checkPrunedLanguage
                    solver
                    (optionalDescendant $ Or [Top, Satisfies (path [0, 0]) Fixpoint.PTrue])
                    optionalDescendantTerms
                    2

        it "retains optional reflexive equality until complete paths can be checked" $ do
            let solver = Entailment $ \_ _ -> pure Unknown
                guard = Same (path [0, 0]) (path [0, 0])
            case optionalDescendant guard of
                Left err -> expectationFailure $ show err
                Right original -> do
                    traverse (accepts solver original) optionalDescendantTerms >>= (`shouldBe` [No, Yes])
                    checkPrunedLanguage solver (Right original :: Either AutomatonError Automaton) optionalDescendantTerms 1
                    lowerToEqualityAutomaton original `shouldBe` Left (ResidualLTAConstraint (State 0) guard)
                    pruneToECTA solver original >>= (`shouldBe` Left (ResidualLTAConstraint (State 0) guard))

        it "lowers reflexive equality when every transition has the observed path" $ do
            let solver = Entailment $ \_ _ -> pure Unknown
            case optionalDescendant $ Same (path [0]) (path [0]) of
                Left err -> expectationFailure $ show err
                Right original -> case lowerToEqualityAutomaton original of
                    Left err -> expectationFailure $ show err
                    Right lowered ->
                        traverse (accepts solver $ FTA.mapGuards equalityConstraint lowered) optionalDescendantTerms
                            >>= (`shouldBe` [Yes, Yes])

        it "does not erase absent descendants implied by an ancestor equality" $ do
            let solver = Entailment $ \_ _ -> pure Unknown
                absent = Same (path [0, 0]) (path [1, 0])
                constraint = semanticConstraint $ And [Same (path [0]) (path [1]), absent]
                leaf = Tree.Node (LiquidSymbol "a" Fixpoint.PTrue) []
            case mkAutomaton
                (State 0)
                [ (State 0, [Transition "pair" Fixpoint.PTrue [State 1, State 1] constraint])
                , (State 1, [Transition "a" Fixpoint.PTrue [] unconstrainedConstraint])
                ] of
                Left err -> expectationFailure $ show err
                Right original -> do
                    accepts solver original (Tree.Node (LiquidSymbol "pair" Fixpoint.PTrue) [leaf, leaf]) >>= (`shouldBe` No)
                    lowerToEqualityAutomaton original `shouldBe` Left (ResidualLTAConstraint (State 0) absent)

        it "keeps semantic and syntactic split states distinct at Int bounds" $
            withZ3 declarations $ \solver -> do
                let zero = value .==. (0 :: Int)
                    one = value .==. (1 :: Int)
                    rows =
                        [ (State 1, [Transition "a" zero [] unconstrainedConstraint, Transition "b" one [] unconstrainedConstraint])
                        , (State maxBound, [])
                        , (State minBound, [Transition "sentinel" Fixpoint.PTrue [] unconstrainedConstraint])
                        ]
                    leafA = Tree.Node (LiquidSymbol "a" zero) []
                    leafB = Tree.Node (LiquidSymbol "b" one) []
                    semantic =
                        mkAutomaton (State 0) $
                            (State 0, [Transition "f" Fixpoint.PTrue [State 1] $ semanticConstraint $ Satisfies (path [0]) zero]) : rows
                    syntactic =
                        mkAutomaton (State 0) $
                            (State 0, [Transition "pair" Fixpoint.PTrue [State 1, State 1] $ semanticConstraint $ Same (path [0]) (path [1])])
                                : rows
                checkPrunedLanguage
                    solver
                    semantic
                    [ Tree.Node (LiquidSymbol "f" Fixpoint.PTrue) [child]
                    | child <- [leafA, leafB, Tree.Node (LiquidSymbol "sentinel" Fixpoint.PTrue) []]
                    ]
                    1
                checkPrunedLanguage
                    solver
                    syntactic
                    [Tree.Node (LiquidSymbol "pair" Fixpoint.PTrue) [left, right] | left <- [leafA, leafB], right <- [leafA, leafB]]
                    2

        it "partitions substitution positions by their value-naming symbol" $
            withZ3 declarations $ \solver ->
                checkPrunedLanguage solver substitutedOutputs substitutionTerms 2

        it "preserves scoped syntactic equality and its Boolean forms as residual LTA guards" $ do
            let solver = Entailment $ \_ _ -> fail "syntactic equality queried the solver"
                same = Same (path [2]) (path [3])
                scope = Substitute [Substitution (path [0]) (path [1])]
                allPairs = [(left, right) | left <- ["x", "y", "z"], right <- ["x", "y", "z"]]
                equalPairs = [("x", "x"), ("x", "y"), ("y", "x"), ("y", "y"), ("z", "z")]
                differentPairs = filter (`notElem` equalPairs) allPairs
                term (left, right) =
                    Tree.Node
                        ( LiquidSymbol
                            "scoped"
                            Fixpoint.PTrue
                        )
                        [Tree.Node (LiquidSymbol symbol Fixpoint.PTrue) [] | symbol <- ["x", "y", left, right]]
                automaton guard =
                    mkAutomaton
                        (State 0)
                        [ (State 0, [Transition "scoped" Fixpoint.PTrue [State 1, State 2, State 3, State 3] $ semanticConstraint guard])
                        , (State 1, [Transition "x" Fixpoint.PTrue [] unconstrainedConstraint])
                        , (State 2, [Transition "y" Fixpoint.PTrue [] unconstrainedConstraint])
                        , (State 3, [Transition symbol Fixpoint.PTrue [] unconstrainedConstraint | symbol <- ["x", "y", "z"]])
                        ]
                check (guard, acceptedPairs) = case automaton guard of
                    Left err -> expectationFailure $ show err
                    Right original -> do
                        denotationAtMost solver 1 original >>= (`shouldBe` Right (map term acceptedPairs))
                        checkPrunedLanguage
                            solver
                            (Right original :: Either AutomatonError Automaton)
                            (map term allPairs)
                            (length acceptedPairs)
                        result <- prune solver original
                        case result of
                            Left err -> expectationFailure $ show err
                            Right reduced -> do
                                denotationAtMost solver 1 reduced >>= (`shouldBe` Right (map term acceptedPairs))
                                lowerToEqualityAutomaton reduced `shouldBe` Left (ResidualLTAConstraint (State 0) guard)
                        pruneToECTA solver original >>= (`shouldBe` Left (ResidualLTAConstraint (State 0) guard))
            mapM_
                check
                [ (scope same, equalPairs)
                , (scope $ Not same, differentPairs)
                , (scope $ Or [same, Not same], allPairs)
                ]

        it "retains guards whose compound actual identities need complete terms" $
            withZ3 ([(Fixpoint.symbol name, Fixpoint.FInt) | name <- ["app", "known"] :: [String]] <> declarations) $ \solver ->
                case compoundActuals of
                    Left err -> expectationFailure $ show err
                    Right original -> do
                        before <- denotationAtMost solver 2 original
                        fmap length before `shouldBe` Right 3
                        result <- prune solver original
                        case result of
                            Left err -> expectationFailure $ show err
                            Right reduced -> do
                                after <- denotationAtMost solver 2 reduced
                                equivalentTermSets before after `shouldBe` True
                                automatonTransitions reduced `shouldBe` automatonTransitions original
                                lowerToEqualityAutomaton reduced
                                    `shouldBe` Left (ResidualLTAConstraint (State 0) compoundEqualityGuard)

        it "reports solver uncertainty when actual identities are known" $
            case optionalDescendant $ Satisfies (path [0]) Fixpoint.PTrue of
                Left err -> expectationFailure $ show err
                Right original ->
                    prune (Entailment $ \_ _ -> pure Unknown) original
                        >>= (`shouldBe` Left (PruneUnknown $ State 0))

        it "uses FTA product intersection to narrow syntactic equality" $
            withZ3 declarations $ \solver ->
                case syntacticPairs of
                    Left err -> expectationFailure $ show err
                    Right original -> do
                        result <- pruneToECTA solver original
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
                        pruneToECTA solver original
                            >>= (`shouldBe` Left (ResidualLTAConstraint (State 0) negativeEquality))

        it "lowers nested positive conjunctions in every requirement order" $
            withZ3 declarations $ \solver -> do
                let requirements =
                        [ Guard.isSameTermAs (Guard.argument 0) (Guard.argument 1)
                        , Guard.isSameTermAs (Guard.argument 1) (Guard.argument 2)
                        , Guard.requires (Guard.argument 0) Fixpoint.PTrue
                        ]
                    check order =
                        case equalTriples $ Guard.allOf order of
                            Left err -> expectationFailure $ show err
                            Right original -> do
                                before <- denotationAtMost solver 1 original
                                result <- pruneToECTA solver original
                                case result of
                                    Left err -> expectationFailure $ show err
                                    Right reduced -> do
                                        after <- denotationAtMost solver 1 $ FTA.mapGuards equalityConstraint reduced
                                        equivalentTermSets before after `shouldBe` True
                                        fmap length after `shouldBe` Right 2
                mapM_ check $ permutations requirements

-- | Compare recognition before and after pruning, including the expected accepted count.
checkPrunedLanguage ::
    Entailment ->
    Either error Automaton ->
    [Tree.Tree LiquidSymbol] ->
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
    Either EnumerationError [Tree.Tree LiquidSymbol] ->
    Either EnumerationError [Tree.Tree LiquidSymbol] ->
    Bool
equivalentTermSets (Right left) (Right right) =
    all (`elem` right) left && all (`elem` left) right
equivalentTermSets _ _ = False

-- | A descendant exists in only one alternative of the child state.
optionalDescendant :: Guard -> Either AutomatonError Automaton
optionalDescendant guard =
    mkAutomaton
        (State 0)
        [ (State 0, [Transition "f" Fixpoint.PTrue [State 1] $ semanticConstraint guard])
        ,
            ( State 1
            ,
                [ Transition "a" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "b" Fixpoint.PTrue [State 2] unconstrainedConstraint
                ]
            )
        , (State 2, [Transition "a" Fixpoint.PTrue [] unconstrainedConstraint])
        ]

-- | Both finite terms of 'optionalDescendant' before its guard is checked.
optionalDescendantTerms :: [Tree.Tree LiquidSymbol]
optionalDescendantTerms =
    [ Tree.Node (LiquidSymbol "f" Fixpoint.PTrue) [leaf]
    , Tree.Node (LiquidSymbol "f" Fixpoint.PTrue) [Tree.Node (LiquidSymbol "b" Fixpoint.PTrue) [leaf]]
    ]
  where
    leaf = Tree.Node (LiquidSymbol "a" Fixpoint.PTrue) []

-- | Three independent choices constrained by positive equalities and entailment.
equalTriples :: LiquidConstraint -> Either AutomatonError Automaton
equalTriples constraint =
    mkAutomaton
        (State 0)
        [ (State 0, [Transition "triple" Fixpoint.PTrue [State 1, State 1, State 1] constraint])
        ,
            ( State 1
            ,
                [ Transition "a" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "b" Fixpoint.PTrue [] unconstrainedConstraint
                ]
            )
        ]

-- | Compare the values of two complete compound actual terms.
compoundEqualityGuard :: Guard
compoundEqualityGuard =
    Substitute
        [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
        (Satisfies (path []) $ variable "x" .==. variable "y")

-- | Root observations do not distinguish equal and unequal actual subtrees.
compoundActuals :: Either AutomatonError Automaton
compoundActuals =
    mkAutomaton
        (State 0)
        [
            ( State 0
            , [Transition "pair" Fixpoint.PTrue [State 1, State 1, State 2, State 3] $ semanticConstraint compoundEqualityGuard]
            )
        ,
            ( State 1
            ,
                [ Transition "known" (value .==. (0 :: Int)) [] unconstrainedConstraint
                , Transition "app" Fixpoint.PTrue [State 4] unconstrainedConstraint
                ]
            )
        , (State 2, [Transition "x" Fixpoint.PTrue [] unconstrainedConstraint])
        , (State 3, [Transition "y" Fixpoint.PTrue [] unconstrainedConstraint])
        ,
            ( State 4
            ,
                [ Transition "a" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "b" Fixpoint.PTrue [] unconstrainedConstraint
                ]
            )
        ]

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
            ,
                [ Transition "left" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "shared" Fixpoint.PTrue [] unconstrainedConstraint
                ]
            )
        ,
            ( State 2
            ,
                [ Transition "shared" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "right" Fixpoint.PTrue [] unconstrainedConstraint
                ]
            )
        ]

-- | One accepted equal pair followed by two rejected unequal pairs.
syntacticPairTerms :: [Tree.Tree LiquidSymbol]
syntacticPairTerms =
    [ pair "shared" "shared"
    , pair "left" "shared"
    , pair "shared" "right"
    ]
  where
    pair left right =
        Tree.Node
            ( LiquidSymbol
                "pair"
                Fixpoint.PTrue
            )
            [Tree.Node (LiquidSymbol left Fixpoint.PTrue) [], Tree.Node (LiquidSymbol right Fixpoint.PTrue) []]

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
            ,
                [ Transition "shared" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "right" Fixpoint.PTrue [] unconstrainedConstraint
                ]
            )
        ,
            ( State 3
            ,
                [ Transition "left" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "shared" Fixpoint.PTrue [] unconstrainedConstraint
                ]
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
            ,
                [ Transition "left" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "shared" Fixpoint.PTrue [] unconstrainedConstraint
                ]
            )
        ,
            ( State 2
            ,
                [ Transition "shared" Fixpoint.PTrue [] unconstrainedConstraint
                , Transition "right" Fixpoint.PTrue [] unconstrainedConstraint
                ]
            )
        ]

negativeEquality :: Guard
negativeEquality = Not $ Same (path [0]) (path [1])

-- | All concrete pairs from the heterogeneous atom state.
pairTerms :: [Tree.Tree LiquidSymbol]
pairTerms = [Tree.Node (LiquidSymbol "pair" Fixpoint.PTrue) [left, right] | left <- predicates, right <- predicates]

-- | All concrete pairs with the left atom below a box constructor.
nestedPairTerms :: [Tree.Tree LiquidSymbol]
nestedPairTerms =
    [ Tree.Node
        ( LiquidSymbol
            "pair"
            Fixpoint.PTrue
        )
        [Tree.Node (LiquidSymbol "box" Fixpoint.PTrue) [left], right]
    | left <- predicates
    , right <- predicates
    ]

-- | Every actual-name and output-refinement combination.
substitutionTerms :: [Tree.Tree LiquidSymbol]
substitutionTerms =
    [ Tree.Node
        ( LiquidSymbol
            "application"
            Fixpoint.PTrue
        )
        [actual, Tree.Node (LiquidSymbol "n" Fixpoint.PTrue) [], output]
    | actual <- namedActuals
    , output <-
        [ Tree.Node (LiquidSymbol "output-x" (value .==. variable "x")) []
        , Tree.Node (LiquidSymbol "output-y" (value .==. variable "y")) []
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
predicates :: [Tree.Tree LiquidSymbol]
predicates =
    [ Tree.Node (LiquidSymbol "predicate" (value .==. (0 :: Int))) []
    , Tree.Node (LiquidSymbol "predicate" (value .==. (1 :: Int))) []
    , Tree.Node (LiquidSymbol "predicate" (value .>=. (0 :: Int))) []
    ]

-- | Variable leaves used by the substitution example.
namedActuals :: [Tree.Tree LiquidSymbol]
namedActuals =
    [ Tree.Node (LiquidSymbol "x" (value .==. (0 :: Int))) []
    , Tree.Node (LiquidSymbol "y" (value .==. (1 :: Int))) []
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
