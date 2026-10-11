{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.PruneSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import Data.List (permutations)

import Data.CFTA.Constraint (equalities)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Refinement (
    Automaton,
    Constraint (constraintGuard),
    DenotationError,
    Entailment,
    Guard (Entails, Not, Or, Same, Satisfies, Substitute, Top),
    Node (Node),
    Substitution (Substitution),
    Symbol (RefinedSymbol),
    Transition,
    Verdict (No, Yes),
    accepts,
    denotationAtMost,
    edgeConstraint,
    noConstraint,
    nodeEdges,
    path,
    prune,
    semanticConstraint,
    transitionSymbol,
    transitionsAt,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (refinementFormula, variable, (.==), (.>=))
import qualified Data.CFTA.Refinement.Guard as Guard
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import Data.CFTA.Refinement.TestSupport (declarations)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term
import qualified Language.Fixpoint.Types as Fixpoint

spec :: Spec
spec =
    describe "semantic pruning" $ do
        it "keeps the language when it prunes heterogeneous nodes at semantic guard positions" $
            withZ3 declarations $ \solver ->
                checkPrunedLanguage solver semanticPairs pairTerms 5

        it "computes Figure 12's bounded denotation directly" $
            withZ3 declarations $ \solver -> do
                terms <- denotationAtMost solver 1 semanticPairs
                fmap length terms `shouldBe` Right 5
                case nodeEdges semanticPairs of
                    [root] -> length (transitionsAt root $ path [0]) `shouldBe` 3
                    roots -> expectationFailure $ "unexpected Figure 12 roots: " <> show roots

        it "keeps the language when it prunes nested semantic positions" $
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

        it "keeps semantic and syntactic splits apart" $
            withZ3 declarations $ \solver -> do
                let zero = refinementFormula (\v -> v .== 0)
                    one = refinementFormula (\v -> v .== 1)
                    atoms =
                        Node
                            [ Transition "a" zero [] noConstraint
                            , Transition "b" one [] noConstraint
                            ]
                    leafA = Term.Node (RefinedSymbol "a" zero) []
                    leafB = Term.Node (RefinedSymbol "b" one) []
                    semantic =
                        Node [Transition "f" Fixpoint.PTrue [atoms] $ semanticConstraint $ Satisfies (path [0]) zero]
                    syntactic =
                        Node [Transition "pair" Fixpoint.PTrue [atoms, atoms] $ semanticConstraint $ Same (path [0]) (path [1])]
                checkPrunedLanguage
                    solver
                    semantic
                    [ Term.Node (RefinedSymbol "f" Fixpoint.PTrue) [child]
                    | child <- [leafA, leafB, Term.Node (RefinedSymbol "sentinel" Fixpoint.PTrue) []]
                    ]
                    1
                checkPrunedLanguage
                    solver
                    syntactic
                    [Term.Node (RefinedSymbol "pair" Fixpoint.PTrue) [left, right] | left <- [leafA, leafB], right <- [leafA, leafB]]
                    2

        it "partitions substitution positions by their value-naming symbol" $
            withZ3 declarations $ \solver ->
                checkPrunedLanguage solver substitutedOutputs substitutionTerms 2

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
checkPrunedLanguage :: Entailment -> Automaton -> [Term Symbol] -> Int -> IO ()
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
    Either DenotationError [Term Symbol] ->
    Either DenotationError [Term Symbol] ->
    Bool
equivalentTermSets (Right left) (Right right) =
    all (`elem` right) left && all (`elem` left) right
equivalentTermSets _ _ = False

-- | A node with one unrefined, unconstrained leaf.
leafNode :: Symbol -> Automaton
leafNode symbol = Node [Transition symbol Fixpoint.PTrue [] noConstraint]

-- | The leaf @a@.
atomA :: Automaton
atomA = leafNode "a"

-- | The leaves @a@ and @b@.
atomsAB :: Automaton
atomsAB =
    Node
        [ Transition "a" Fixpoint.PTrue [] noConstraint
        , Transition "b" Fixpoint.PTrue [] noConstraint
        ]

-- | A descendant exists in only one alternative of the child node.
optionalDescendant :: Guard -> Automaton
optionalDescendant guard =
    Node [Transition "f" Fixpoint.PTrue [choice] $ semanticConstraint guard]
  where
    choice =
        Node
            [ Transition "a" Fixpoint.PTrue [] noConstraint
            , Transition "b" Fixpoint.PTrue [atomA] noConstraint
            ]

-- | Both finite terms of 'optionalDescendant' before its guard is checked.
optionalDescendantTerms :: [Term Symbol]
optionalDescendantTerms =
    [ Term.Node (RefinedSymbol "f" Fixpoint.PTrue) [leaf]
    , Term.Node (RefinedSymbol "f" Fixpoint.PTrue) [Term.Node (RefinedSymbol "b" Fixpoint.PTrue) [leaf]]
    ]
  where
    leaf = Term.Node (RefinedSymbol "a" Fixpoint.PTrue) []

-- | Three independent choices constrained by positive equalities and entailment.
equalTriples :: Constraint -> Automaton
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
            [ Transition "known" (refinementFormula (\v -> v .== 0)) [] noConstraint
            , Transition "app" Fixpoint.PTrue [atomsAB] noConstraint
            ]

{- | Figure 12's LTA: @f(phi1, phi2)@ where @phi1 => phi2@.

Every formula is an ordinary nullary ranked-alphabet symbol. The implementation
encodes that symbol as @RefinedSymbol "predicate" formula@; it is not metadata
outside the automaton.
-}
semanticPairs :: Automaton
semanticPairs = Node [Transition "pair" Fixpoint.PTrue [predicateNode, predicateNode] pairEntailment]

-- | The same relation, with its left observation one constructor below the root.
nestedPairs :: Automaton
nestedPairs = Node [Transition "pair" Fixpoint.PTrue [box, predicateNode] nestedEntailment]
  where
    box = Node [Transition "box" Fixpoint.PTrue [predicateNode] noConstraint]

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
            [ Transition "x" (refinementFormula (\v -> v .== 0)) [] noConstraint
            , Transition "y" (refinementFormula (\v -> v .== 1)) [] noConstraint
            ]
    outputs =
        Node
            [ Transition "output-x" (refinementFormula (\v -> v .== variable "x")) [] noConstraint
            , Transition "output-y" (refinementFormula (\v -> v .== variable "y")) [] noConstraint
            ]

-- | The leaves @left@ and @shared@.
leftOrShared :: Automaton
leftOrShared =
    Node
        [ Transition "left" Fixpoint.PTrue [] noConstraint
        , Transition "shared" Fixpoint.PTrue [] noConstraint
        ]

-- | The leaves @shared@ and @right@.
sharedOrRight :: Automaton
sharedOrRight =
    Node
        [ Transition "shared" Fixpoint.PTrue [] noConstraint
        , Transition "right" Fixpoint.PTrue [] noConstraint
        ]

-- | Two overlapping structural languages tied by syntactic equality.
syntacticPairs :: Automaton
syntacticPairs =
    Node [Transition "pair" Fixpoint.PTrue [leftOrShared, sharedOrRight] $ semanticConstraint $ Same (path [0]) (path [1])]

-- | One accepted equal pair followed by two rejected unequal pairs.
syntacticPairTerms :: [Term Symbol]
syntacticPairTerms =
    [ pair "shared" "shared"
    , pair "left" "shared"
    , pair "shared" "right"
    ]
  where
    pair left right =
        Term.Node
            (RefinedSymbol "pair" Fixpoint.PTrue)
            [Term.Node (RefinedSymbol left Fixpoint.PTrue) [], Term.Node (RefinedSymbol right Fixpoint.PTrue) []]

-- | The same structural overlap reached below a wrapper on the left.
nestedSyntacticPairs :: Automaton
nestedSyntacticPairs =
    Node [Transition "pair" Fixpoint.PTrue [boxOrEmpty, sharedOrRight] $ semanticConstraint $ Same (path [0, 0]) (path [1])]
  where
    boxOrEmpty =
        Node
            [ Transition "box" Fixpoint.PTrue [leftOrShared] noConstraint
            , Transition "empty" Fixpoint.PTrue [] noConstraint
            ]

-- | Negated equality is a valid LTA constraint but is not an equality class.
negativeSyntacticPairs :: Automaton
negativeSyntacticPairs =
    Node [Transition "pair" Fixpoint.PTrue [leftOrShared, sharedOrRight] $ semanticConstraint negativeEquality]

negativeEquality :: Guard
negativeEquality = Not $ Same (path [0]) (path [1])

-- | All concrete pairs from the heterogeneous atom node.
pairTerms :: [Term Symbol]
pairTerms = [Term.Node (RefinedSymbol "pair" Fixpoint.PTrue) [left, right] | left <- predicates, right <- predicates]

-- | All concrete pairs with the left atom below a box constructor.
nestedPairTerms :: [Term Symbol]
nestedPairTerms =
    [ Term.Node
        (RefinedSymbol "pair" Fixpoint.PTrue)
        [Term.Node (RefinedSymbol "box" Fixpoint.PTrue) [left], right]
    | left <- predicates
    , right <- predicates
    ]

-- | Every actual-name and output-refinement combination.
substitutionTerms :: [Term Symbol]
substitutionTerms =
    [ Term.Node
        (RefinedSymbol "application" Fixpoint.PTrue)
        [actual, Term.Node (RefinedSymbol "n" Fixpoint.PTrue) [], output]
    | actual <- namedActuals
    , output <-
        [ Term.Node (RefinedSymbol "output-x" (refinementFormula (\v -> v .== variable "x"))) []
        , Term.Node (RefinedSymbol "output-y" (refinementFormula (\v -> v .== variable "y"))) []
        ]
    ]

-- | Three representative refinement transitions.
predicateTransitions :: [Transition]
predicateTransitions =
    [ Transition "predicate" (refinementFormula (\v -> v .== 0)) [] noConstraint
    , Transition "predicate" (refinementFormula (\v -> v .== 1)) [] noConstraint
    , Transition "predicate" (refinementFormula (\v -> v .>= 0)) [] noConstraint
    ]

-- | The node of the three predicate transitions.
predicateNode :: Automaton
predicateNode = Node predicateTransitions

-- | Concrete formula terms matching 'predicateTransitions'.
predicates :: [Term Symbol]
predicates =
    [ Term.Node (RefinedSymbol "predicate" (refinementFormula (\v -> v .== 0))) []
    , Term.Node (RefinedSymbol "predicate" (refinementFormula (\v -> v .== 1))) []
    , Term.Node (RefinedSymbol "predicate" (refinementFormula (\v -> v .>= 0))) []
    ]

-- | Variable leaves used by the substitution example.
namedActuals :: [Term Symbol]
namedActuals =
    [ Term.Node (RefinedSymbol "x" (refinementFormula (\v -> v .== 0))) []
    , Term.Node (RefinedSymbol "y" (refinementFormula (\v -> v .== 1))) []
    ]

-- | Direct semantic relation between sibling positions.
pairEntailment :: Constraint
pairEntailment = semanticConstraint $ Entails (path [0]) (path [1])

-- | Semantic relation whose antecedent is below a wrapper.
nestedEntailment :: Constraint
nestedEntailment = semanticConstraint $ Entails (path [0, 0]) (path [1])

-- | Substitute the actual value name for the formal before checking the output.
substitutedRequirement :: Constraint
substitutedRequirement =
    semanticConstraint $
        Substitute
            [Substitution (path [0]) (path [1])]
            (Satisfies (path [2]) $ refinementFormula (\v -> v .== variable "n"))
