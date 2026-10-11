{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.PruneSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldMatchList)

import Data.CFTA.Refinement (
    Automaton,
    Constraint (constraintGuard),
    DenotationError,
    Entailment (Entailment),
    Guard (And, Not, Or, Same, Satisfies, Substitute),
    Node (EmptyNode, Node),
    PruneError (PruneUnknown),
    Substitution (Substitution),
    Symbol (RefinedSymbol),
    Verdict (No, Unknown, Yes),
    accepts,
    denotationAtMost,
    edgeConstraint,
    noConstraint,
    nodeEdges,
    path,
    prune,
    semanticConstraint,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (true)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec =
    describe "semantic pruning" $ do
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
                leaf = Term.Node (RefinedSymbol "a" true) []
                original = Node [Transition "pair" true [atomA, atomA] constraint]
            accepts solver original (Term.Node (RefinedSymbol "pair" true) [leaf, leaf]) >>= (`shouldBe` No)
            prune solver original >>= (`shouldBe` Right EmptyNode)

        it "preserves scoped syntactic equality and its Boolean forms as residual LTA guards" $ do
            let solver = Entailment $ \_ _ -> fail "syntactic equality queried the solver"
                same = Same (path [2]) (path [3])
                scope = Substitute [Substitution (path [0]) (path [1])]
                allPairs = [(left, right) | left <- ["x", "y", "z"], right <- ["x", "y", "z"]]
                equalPairs = [("x", "x"), ("x", "y"), ("y", "x"), ("y", "y"), ("z", "z")]
                differentPairs = filter (`notElem` equalPairs) allPairs
                term (left, right) =
                    Term.Node
                        (RefinedSymbol "scoped" true)
                        [Term.Node (RefinedSymbol symbol true) [] | symbol <- ["x", "y", left, right]]
                automaton guard =
                    Node
                        [ Transition
                            "scoped"
                            true
                            [leafNode "x", leafNode "y", xyz, xyz]
                            (semanticConstraint guard)
                        ]
                xyz = Node [Transition symbol true [] noConstraint | symbol <- ["x", "y", "z"]]
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

        it "reports solver uncertainty when actual identities are known" $ do
            result <- prune (Entailment $ \_ _ -> pure Unknown) $ optionalDescendant $ Satisfies (path [0]) true
            case result of
                Left (PruneUnknown _) -> pure ()
                other -> expectationFailure $ "expected an undecided guard, got " <> show other

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

-- | Compare denotations as sets without requiring an ordering for formulas.
equivalentTermSets ::
    Either DenotationError [Term Symbol] ->
    Either DenotationError [Term Symbol] ->
    Bool
equivalentTermSets (Right left) (Right right) =
    all (`elem` right) left && all (`elem` left) right
equivalentTermSets _ _ = False

-- | A node with one unrefined, unconstrained leaf.
leafNode :: Symbol -> Automaton
leafNode symbol = Node [Transition symbol true [] noConstraint]

-- | The leaf @a@.
atomA :: Automaton
atomA = leafNode "a"

-- | A descendant exists in only one alternative of the child node.
optionalDescendant :: Guard -> Automaton
optionalDescendant guard =
    Node [Transition "f" true [choice] $ semanticConstraint guard]
  where
    choice =
        Node
            [ Transition "a" true [] noConstraint
            , Transition "b" true [atomA] noConstraint
            ]

-- | Both finite terms of 'optionalDescendant' before its guard is checked.
optionalDescendantTerms :: [Term Symbol]
optionalDescendantTerms =
    [ Term.Node (RefinedSymbol "f" true) [leaf]
    , Term.Node (RefinedSymbol "f" true) [Term.Node (RefinedSymbol "b" true) [leaf]]
    ]
  where
    leaf = Term.Node (RefinedSymbol "a" true) []
