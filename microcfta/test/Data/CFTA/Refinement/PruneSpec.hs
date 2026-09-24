{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.PruneSpec (spec) where

import qualified Data.Tree as Tree
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldMatchList)

import Data.List (permutations)

import Data.CFTA.Constraint (Constraint (equalities))
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Refinement (
    Automaton,
    DenotationError,
    Entailment (Entailment),
    Guard (And, Entails, Not, Or, Same, Satisfies, Substitute, Top),
    LiquidConstraint (constraintGuard),
    LiquidSymbol (LiquidSymbol),
    Node (EmptyNode, Node),
    PruneError (PruneUnknown),
    Substitution (Substitution),
    Symbol,
    Transition,
    Verdict (No, Unknown, Yes),
    accepts,
    denotationAtMost,
    edgeConstraint,
    nodeEdges,
    path,
    prune,
    semanticConstraint,
    transitionSymbol,
    transitionsAt,
    unconstrainedConstraint,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (refinementFormula, variable, (.==), (.>=))
import qualified Data.CFTA.Refinement.Guard as Guard
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Refinement.TestSupport (declarations)
import qualified Language.Fixpoint.Types as Fixpoint

spec :: Spec
spec =
    describe "semantic pruning" $ do
        it "splits heterogeneous nodes at semantic guard positions" $
            withZ3 declarations $ \solver ->
                checkPrunedLanguage solver semanticPairs pairTerms 5

        it "computes Figure 12's bounded denotation directly" $
            withZ3 declarations $ \solver -> do
                terms <- denotationAtMost solver 1 semanticPairs
                fmap length terms `shouldBe` Right 5
                case nodeEdges semanticPairs of
                    [root] -> length (transitionsAt root $ path [0]) `shouldBe` 3
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
                original = optionalDescendant guard
            traverse (accepts solver original) optionalDescendantTerms >>= (`shouldBe` [No, Yes])
            checkPrunedLanguage solver original optionalDescendantTerms 1
            reduced <- prune solver original
            fmap (map (constraintGuard . edgeConstraint) . nodeEdges) reduced `shouldBe` Right [guard]

        it "keeps reflexive equality on an always-present path as a residual guard" $ do
            let solver = Entailment $ \_ _ -> pure Unknown
            reduced <- prune solver $ optionalDescendant $ Same (path [0]) (path [0])
            case reduced of
                Left err -> expectationFailure $ show err
                Right pruned ->
                    traverse (accepts solver pruned) optionalDescendantTerms >>= (`shouldBe` [Yes, Yes])

        it "removes a transition whose equalities need an absent descendant" $ do
            let solver = Entailment $ \_ _ -> pure Unknown
                constraint = semanticConstraint $ And [Same (path [0]) (path [1]), Same (path [0, 0]) (path [1, 0])]
                leaf = Tree.Node (LiquidSymbol "a" Fixpoint.PTrue) []
                original = Node [Transition "pair" Fixpoint.PTrue [atomA, atomA] constraint]
            accepts solver original (Tree.Node (LiquidSymbol "pair" Fixpoint.PTrue) [leaf, leaf]) >>= (`shouldBe` No)
            prune solver original >>= (`shouldBe` Right EmptyNode)

        it "keeps semantic and syntactic splits apart" $
            withZ3 declarations $ \solver -> do
                let zero = refinementFormula (\v -> v .== 0)
                    one = refinementFormula (\v -> v .== 1)
                    atoms =
                        Node
                            [ Transition "a" zero [] unconstrainedConstraint
                            , Transition "b" one [] unconstrainedConstraint
                            ]
                    leafA = Tree.Node (LiquidSymbol "a" zero) []
                    leafB = Tree.Node (LiquidSymbol "b" one) []
                    semantic =
                        Node [Transition "f" Fixpoint.PTrue [atoms] $ semanticConstraint $ Satisfies (path [0]) zero]
                    syntactic =
                        Node [Transition "pair" Fixpoint.PTrue [atoms, atoms] $ semanticConstraint $ Same (path [0]) (path [1])]
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
                        (LiquidSymbol "scoped" Fixpoint.PTrue)
                        [Tree.Node (LiquidSymbol symbol Fixpoint.PTrue) [] | symbol <- ["x", "y", left, right]]
                automaton guard =
                    Node
                        [ Transition
                            "scoped"
                            Fixpoint.PTrue
                            [leafNode "x", leafNode "y", xyz, xyz]
                            (semanticConstraint guard)
                        ]
                xyz = Node [Transition symbol Fixpoint.PTrue [] unconstrainedConstraint | symbol <- ["x", "y", "z"]]
                check (guard, acceptedPairs) = do
                    let original = automaton guard
                    denotationAtMost solver 1 original
                        >>= either (expectationFailure . show) (`shouldMatchList` map term acceptedPairs)
                    checkPrunedLanguage solver original (map term allPairs) (length acceptedPairs)
                    result <- prune solver original
                    case result of
                        Left err -> expectationFailure $ show err
                        Right reduced -> do
                            denotationAtMost solver 1 reduced
                                >>= either (expectationFailure . show) (`shouldMatchList` map term acceptedPairs)
                            map (constraintGuard . edgeConstraint) (nodeEdges reduced) `shouldBe` [guard]
            mapM_
                check
                [ (scope same, equalPairs)
                , (scope $ Not same, differentPairs)
                , (scope $ Or [same, Not same], allPairs)
                ]

        it "retains guards whose compound actual identities need complete terms" $
            withZ3 ([(Fixpoint.symbol name, Fixpoint.FInt) | name <- ["app", "known"] :: [String]] <> declarations) $ \solver -> do
                before <- denotationAtMost solver 2 compoundActuals
                fmap length before `shouldBe` Right 3
                result <- prune solver compoundActuals
                case result of
                    Left err -> expectationFailure $ show err
                    Right reduced -> do
                        after <- denotationAtMost solver 2 reduced
                        equivalentTermSets before after `shouldBe` True
                        reduced `shouldBe` compoundActuals

        it "reports solver uncertainty when actual identities are known" $ do
            result <- prune (Entailment $ \_ _ -> pure Unknown) $ optionalDescendant $ Satisfies (path [0]) Fixpoint.PTrue
            case result of
                Left (PruneUnknown _) -> pure ()
                other -> expectationFailure $ "expected an undecided guard, got " <> show other

        it "narrows syntactic equality to the intersection of the equal positions" $
            withZ3 declarations $ \solver -> do
                result <- prune solver syntacticPairs
                case result of
                    Left err -> expectationFailure $ show err
                    Right reduced -> case nodeEdges reduced of
                        [root] -> do
                            equalities (edgeConstraint root) `shouldBe` mkEqConstraints [[path [0], path [1]]]
                            map transitionSymbol (transitionsAt root $ path [0]) `shouldBe` ["shared"]
                            map transitionSymbol (transitionsAt root $ path [1]) `shouldBe` ["shared"]
                            traverse (accepts solver reduced) syntacticPairTerms >>= (`shouldBe` [Yes, No, No])
                        roots -> expectationFailure $ "unexpected root alternatives: " <> show roots

        it "applies syntactic intersection below a nested position" $
            withZ3 declarations $ \solver -> do
                result <- prune solver nestedSyntacticPairs
                case result of
                    Left err -> expectationFailure $ show err
                    Right reduced -> case nodeEdges reduced of
                        [root] -> do
                            map transitionSymbol (transitionsAt root $ path [0]) `shouldBe` ["box"]
                            map transitionSymbol (transitionsAt root $ path [0, 0]) `shouldBe` ["shared"]
                            map transitionSymbol (transitionsAt root $ path [1]) `shouldBe` ["shared"]
                        roots -> expectationFailure $ "unexpected root alternatives: " <> show roots

        it "keeps Boolean syntactic constraints in the LTA when equality classes cannot express them" $
            withZ3 declarations $ \solver -> do
                reduced <- prune solver negativeSyntacticPairs
                case reduced of
                    Left err -> expectationFailure $ show err
                    Right lta -> do
                        traverse (accepts solver lta) syntacticPairTerms >>= (`shouldBe` [No, Yes, Yes])
                        map (constraintGuard . edgeConstraint) (nodeEdges lta) `shouldBe` [negativeEquality]

        it "solves nested positive conjunctions in every requirement order" $
            withZ3 declarations $ \solver -> do
                let requirements =
                        [ Guard.isSameTermAs (Guard.argument 0) (Guard.argument 1)
                        , Guard.isSameTermAs (Guard.argument 1) (Guard.argument 2)
                        , Guard.requires (Guard.argument 0) (const Fixpoint.PTrue)
                        ]
                    check order = do
                        let original = equalTriples $ Guard.allOf order
                        before <- denotationAtMost solver 1 original
                        result <- prune solver original
                        case result of
                            Left err -> expectationFailure $ show err
                            Right reduced -> do
                                after <- denotationAtMost solver 1 reduced
                                equivalentTermSets before after `shouldBe` True
                                fmap length after `shouldBe` Right 2
                mapM_ check $ permutations requirements

-- | Compare recognition before and after pruning, including the expected accepted count.
checkPrunedLanguage :: Entailment -> Automaton -> [Tree.Tree LiquidSymbol] -> Int -> IO ()
checkPrunedLanguage solver original terms expected = do
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
    Either DenotationError [Tree.Tree LiquidSymbol] ->
    Either DenotationError [Tree.Tree LiquidSymbol] ->
    Bool
equivalentTermSets (Right left) (Right right) =
    all (`elem` right) left && all (`elem` left) right
equivalentTermSets _ _ = False

-- | A node with one unrefined, unconstrained leaf.
leafNode :: Symbol -> Automaton
leafNode symbol = Node [Transition symbol Fixpoint.PTrue [] unconstrainedConstraint]

-- | The leaf @a@.
atomA :: Automaton
atomA = leafNode "a"

-- | The leaves @a@ and @b@.
atomsAB :: Automaton
atomsAB =
    Node
        [ Transition "a" Fixpoint.PTrue [] unconstrainedConstraint
        , Transition "b" Fixpoint.PTrue [] unconstrainedConstraint
        ]

-- | A descendant exists in only one alternative of the child node.
optionalDescendant :: Guard -> Automaton
optionalDescendant guard =
    Node [Transition "f" Fixpoint.PTrue [choice] $ semanticConstraint guard]
  where
    choice =
        Node
            [ Transition "a" Fixpoint.PTrue [] unconstrainedConstraint
            , Transition "b" Fixpoint.PTrue [atomA] unconstrainedConstraint
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
equalTriples :: LiquidConstraint -> Automaton
equalTriples constraint =
    Node [Transition "triple" Fixpoint.PTrue [atomsAB, atomsAB, atomsAB] constraint]

-- | Compare the values of two complete compound actual terms.
compoundEqualityGuard :: Guard
compoundEqualityGuard =
    Substitute
        [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
        (Satisfies (path []) $ variable "x" .== variable "y")

-- | Root observations do not distinguish equal and unequal actual subtrees.
compoundActuals :: Automaton
compoundActuals =
    Node
        [ Transition "pair" Fixpoint.PTrue [known, known, leafNode "x", leafNode "y"] $
            semanticConstraint compoundEqualityGuard
        ]
  where
    known =
        Node
            [ Transition "known" (refinementFormula (\v -> v .== 0)) [] unconstrainedConstraint
            , Transition "app" Fixpoint.PTrue [atomsAB] unconstrainedConstraint
            ]

{- | Figure 12's LTA: @f(phi1, phi2)@ where @phi1 => phi2@.

Every formula is an ordinary nullary ranked-alphabet symbol. The implementation
encodes that symbol as @LiquidSymbol "predicate" formula@; it is not metadata
outside the automaton.
-}
semanticPairs :: Automaton
semanticPairs = Node [Transition "pair" Fixpoint.PTrue [predicateNode, predicateNode] pairEntailment]

-- | The same relation, with its left observation one constructor below the root.
nestedPairs :: Automaton
nestedPairs = Node [Transition "pair" Fixpoint.PTrue [box, predicateNode] nestedEntailment]
  where
    box = Node [Transition "box" Fixpoint.PTrue [predicateNode] unconstrainedConstraint]

-- | A substitution guard whose actual names select matching output refinements.
substitutedOutputs :: Automaton
substitutedOutputs =
    Node
        [ Transition
            "application"
            Fixpoint.PTrue
            [actuals, leafNode "n", outputs]
            substitutedRequirement
        ]
  where
    actuals =
        Node
            [ Transition "x" (refinementFormula (\v -> v .== 0)) [] unconstrainedConstraint
            , Transition "y" (refinementFormula (\v -> v .== 1)) [] unconstrainedConstraint
            ]
    outputs =
        Node
            [ Transition "output-x" (refinementFormula (\v -> v .== variable "x")) [] unconstrainedConstraint
            , Transition "output-y" (refinementFormula (\v -> v .== variable "y")) [] unconstrainedConstraint
            ]

-- | The leaves @left@ and @shared@.
leftOrShared :: Automaton
leftOrShared =
    Node
        [ Transition "left" Fixpoint.PTrue [] unconstrainedConstraint
        , Transition "shared" Fixpoint.PTrue [] unconstrainedConstraint
        ]

-- | The leaves @shared@ and @right@.
sharedOrRight :: Automaton
sharedOrRight =
    Node
        [ Transition "shared" Fixpoint.PTrue [] unconstrainedConstraint
        , Transition "right" Fixpoint.PTrue [] unconstrainedConstraint
        ]

-- | Two overlapping structural languages tied by syntactic equality.
syntacticPairs :: Automaton
syntacticPairs =
    Node [Transition "pair" Fixpoint.PTrue [leftOrShared, sharedOrRight] $ semanticConstraint $ Same (path [0]) (path [1])]

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
            (LiquidSymbol "pair" Fixpoint.PTrue)
            [Tree.Node (LiquidSymbol left Fixpoint.PTrue) [], Tree.Node (LiquidSymbol right Fixpoint.PTrue) []]

-- | The same structural overlap reached below a wrapper on the left.
nestedSyntacticPairs :: Automaton
nestedSyntacticPairs =
    Node [Transition "pair" Fixpoint.PTrue [boxOrEmpty, sharedOrRight] $ semanticConstraint $ Same (path [0, 0]) (path [1])]
  where
    boxOrEmpty =
        Node
            [ Transition "box" Fixpoint.PTrue [leftOrShared] unconstrainedConstraint
            , Transition "empty" Fixpoint.PTrue [] unconstrainedConstraint
            ]

-- | Negated equality is a valid LTA constraint but is not an equality class.
negativeSyntacticPairs :: Automaton
negativeSyntacticPairs =
    Node [Transition "pair" Fixpoint.PTrue [leftOrShared, sharedOrRight] $ semanticConstraint negativeEquality]

negativeEquality :: Guard
negativeEquality = Not $ Same (path [0]) (path [1])

-- | All concrete pairs from the heterogeneous atom node.
pairTerms :: [Tree.Tree LiquidSymbol]
pairTerms = [Tree.Node (LiquidSymbol "pair" Fixpoint.PTrue) [left, right] | left <- predicates, right <- predicates]

-- | All concrete pairs with the left atom below a box constructor.
nestedPairTerms :: [Tree.Tree LiquidSymbol]
nestedPairTerms =
    [ Tree.Node
        (LiquidSymbol "pair" Fixpoint.PTrue)
        [Tree.Node (LiquidSymbol "box" Fixpoint.PTrue) [left], right]
    | left <- predicates
    , right <- predicates
    ]

-- | Every actual-name and output-refinement combination.
substitutionTerms :: [Tree.Tree LiquidSymbol]
substitutionTerms =
    [ Tree.Node
        (LiquidSymbol "application" Fixpoint.PTrue)
        [actual, Tree.Node (LiquidSymbol "n" Fixpoint.PTrue) [], output]
    | actual <- namedActuals
    , output <-
        [ Tree.Node (LiquidSymbol "output-x" (refinementFormula (\v -> v .== variable "x"))) []
        , Tree.Node (LiquidSymbol "output-y" (refinementFormula (\v -> v .== variable "y"))) []
        ]
    ]

-- | Three representative refinement transitions.
predicateTransitions :: [Transition]
predicateTransitions =
    [ Transition "predicate" (refinementFormula (\v -> v .== 0)) [] unconstrainedConstraint
    , Transition "predicate" (refinementFormula (\v -> v .== 1)) [] unconstrainedConstraint
    , Transition "predicate" (refinementFormula (\v -> v .>= 0)) [] unconstrainedConstraint
    ]

-- | The node of the three predicate transitions.
predicateNode :: Automaton
predicateNode = Node predicateTransitions

-- | Concrete formula terms matching 'predicateTransitions'.
predicates :: [Tree.Tree LiquidSymbol]
predicates =
    [ Tree.Node (LiquidSymbol "predicate" (refinementFormula (\v -> v .== 0))) []
    , Tree.Node (LiquidSymbol "predicate" (refinementFormula (\v -> v .== 1))) []
    , Tree.Node (LiquidSymbol "predicate" (refinementFormula (\v -> v .>= 0))) []
    ]

-- | Variable leaves used by the substitution example.
namedActuals :: [Tree.Tree LiquidSymbol]
namedActuals =
    [ Tree.Node (LiquidSymbol "x" (refinementFormula (\v -> v .== 0))) []
    , Tree.Node (LiquidSymbol "y" (refinementFormula (\v -> v .== 1))) []
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
            (Satisfies (path [2]) $ refinementFormula (\v -> v .== variable "n"))
