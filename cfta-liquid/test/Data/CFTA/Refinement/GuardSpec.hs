{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.GuardSpec (spec) where

import Control.Exception (evaluate)
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Refinement (
    Automaton,
    Guard (Bottom, Not, Or, Same, Satisfies, Substitute),
    Leafness (Mixed),
    Node (Node),
    Observed (Observed),
    Substitution (Substitution),
    Symbol (RefinedSymbol),
    Verdict (..),
    equalityConstraint,
    evaluateConstraint,
    evaluateGuard,
    evaluateGuardWithShape,
    intersect,
    noConstraint,
    path,
    semanticConstraint,
    termsWith,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (refinementFormula, true, variable, (.==), (.>=))
import Data.CFTA.Refinement.Guard (anyOf, buildGuard, isSameTermAs, notGuard, requires, withActualFor)
import Data.CFTA.Refinement.TestSupport (tableEntailment)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec =
    describe "LTA guard syntax" $ do
        it "states a literal precondition without a phantom predicate child" $ do
            let nonNegative v = v .>= 0
                guard = buildGuard $ \denominator -> denominator `requires` nonNegative
                term = Term.Node (RefinedSymbol "divide" true) [Term.Node (RefinedSymbol "n" (refinementFormula nonNegative)) []]
            guard `shouldBe` semanticConstraint (Satisfies (path [0]) (refinementFormula nonNegative))
            evaluateConstraint tableEntailment guard term >>= (`shouldBe` Yes)

        it "rejects a child whose refinement does not establish the requirement" $ do
            let nonNegative v = v .>= 0
                guard = buildGuard $ \denominator -> denominator `requires` nonNegative
                term = Term.Node (RefinedSymbol "divide" true) [Term.Node (RefinedSymbol "n" true) []]
            evaluateConstraint tableEntailment guard term >>= (`shouldBe` No)

        it "keeps syntactic equality inside the full Boolean constraint language" $ do
            let same = buildGuard $ \left right -> left `isSameTermAs` right
                different = notGuard same
                equalTerm = Term.Node (RefinedSymbol "pair" true) [Term.Node (RefinedSymbol "x" true) [], Term.Node (RefinedSymbol "x" true) []]
                differentTerm = Term.Node (RefinedSymbol "pair" true) [Term.Node (RefinedSymbol "x" true) [], Term.Node (RefinedSymbol "y" true) []]
                differentlyRefinedTerm =
                    Term.Node
                        ( RefinedSymbol
                            "pair"
                            true
                        )
                        [Term.Node (RefinedSymbol "x" true) [], Term.Node (RefinedSymbol "x" (refinementFormula (\v -> v .== 1))) []]
                equalityOrRequirement = anyOf [same, buildGuard $ \left -> left `requires` const true]
            same `shouldBe` semanticConstraint (Same (path [0]) (path [1]))
            evaluateConstraint tableEntailment same differentlyRefinedTerm >>= (`shouldBe` No)
            evaluateConstraint tableEntailment different equalTerm >>= (`shouldBe` No)
            evaluateConstraint tableEntailment different differentTerm >>= (`shouldBe` Yes)
            evaluateConstraint tableEntailment equalityOrRequirement differentTerm >>= (`shouldBe` Yes)

        it "rejects equality at missing paths and accepts its negation" $ do
            let term = Term.Node (RefinedSymbol "leaf" true) []
                absent = path [0]
            evaluateGuard tableEntailment (Same absent absent) term >>= (`shouldBe` No)
            evaluateGuard tableEntailment (Same (path []) absent) term >>= (`shouldBe` No)
            evaluateGuard tableEntailment (Same absent (path [])) term >>= (`shouldBe` No)
            evaluateGuard tableEntailment (Not $ Same absent absent) term >>= (`shouldBe` Yes)
            evaluateGuard tableEntailment (Same (path []) (path [])) term >>= (`shouldBe` Yes)

        it "decides sparse reflexive equality without assuming distinct subtrees are equal" $ do
            let left = path [0]
                right = path [1]
                observe target
                    | target == left || target == right = Just $ Observed "app" Mixed
                    | otherwise = Nothing
            evaluateGuardWithShape tableEntailment observe (Same left left) >>= (`shouldBe` Yes)
            evaluateGuardWithShape tableEntailment observe (Same left right) >>= (`shouldBe` Unknown)
            evaluateGuardWithShape tableEntailment observe (Same (path [2]) (path [2])) >>= (`shouldBe` No)

        it "compares renamed variable leaves only inside an explicit substitution scope" $ do
            let term = Term.Node (RefinedSymbol "pair" true) [Term.Node (RefinedSymbol "x" true) [], Term.Node (RefinedSymbol "y" true) []]
                same = Same (path [0]) (path [1])
                scoped = Substitute [Substitution (path [0]) (path [1])] same
            evaluateGuard tableEntailment same term >>= (`shouldBe` No)
            evaluateGuard tableEntailment scoped term >>= (`shouldBe` Yes)
            evaluateGuard tableEntailment (Substitute [] same) term >>= (`shouldBe` No)
            evaluateGuard tableEntailment same term >>= (`shouldBe` No)

        it "puts cached positive equality inside the named substitution scope" $ do
            let term = Term.Node (RefinedSymbol "pair" true) [Term.Node (RefinedSymbol "x" true) [], Term.Node (RefinedSymbol "y" true) []]
                cached = equalityConstraint $ mkEqConstraints [[path [0], path [1]]]
                scoped = buildGuard $ \actual formal -> withActualFor actual formal cached
            evaluateConstraint tableEntailment cached term >>= (`shouldBe` No)
            evaluateConstraint tableEntailment scoped term >>= (`shouldBe` Yes)

        it "renames nested constructor symbols and free refinement names before comparison" $ do
            let annotated symbol name =
                    Term.Node
                        ( RefinedSymbol
                            "box"
                            (refinementFormula (\v -> v .== variable name))
                        )
                        [Term.Node (RefinedSymbol symbol (refinementFormula (\v -> v .== variable name))) []]
                term =
                    Term.Node
                        ( RefinedSymbol
                            "context"
                            true
                        )
                        [ Term.Node (RefinedSymbol "x" true) []
                        , Term.Node (RefinedSymbol "y" true) []
                        , annotated "x" "x"
                        , annotated "y" "y"
                        ]
                same = Same (path [2]) (path [3])
                scoped = Substitute [Substitution (path [0]) (path [1])] same
            evaluateGuard tableEntailment same term >>= (`shouldBe` No)
            evaluateGuard tableEntailment scoped term >>= (`shouldBe` Yes)

        it "does not replace a formal leaf with the whole actual subtree" $ do
            let term =
                    Term.Node
                        ( RefinedSymbol
                            "context"
                            true
                        )
                        [ Term.Node (RefinedSymbol "app" true) [Term.Node (RefinedSymbol "argument" true) []]
                        , Term.Node (RefinedSymbol "formal" true) []
                        ]
                guard =
                    Substitute
                        [Substitution (path [0]) (path [1])]
                        (Same (path [0]) (path [1]))
            evaluateGuard tableEntailment guard term >>= (`shouldBe` No)

        it "applies a symbol swap simultaneously within one equality scope" $ do
            let term = Term.Node (RefinedSymbol "pair" true) [Term.Node (RefinedSymbol "x" true) [], Term.Node (RefinedSymbol "y" true) []]
                scope =
                    Substitute
                        [Substitution (path [0]) (path [1]), Substitution (path [1]) (path [0])]
                annotated =
                    Term.Node
                        ( RefinedSymbol
                            "context"
                            true
                        )
                        [ Term.Node (RefinedSymbol "x" true) []
                        , Term.Node (RefinedSymbol "y" true) []
                        , Term.Node (RefinedSymbol "predicate" (refinementFormula (\v -> v .== variable "x"))) []
                        , Term.Node (RefinedSymbol "predicate" (refinementFormula (\v -> v .== variable "y"))) []
                        ]
            evaluateGuard tableEntailment (scope $ Same (path [0]) (path [1])) term >>= (`shouldBe` No)
            evaluateGuard tableEntailment (scope $ Same (path [2]) (path [3])) annotated >>= (`shouldBe` No)

        it "uses the first nonidentity replacement for duplicate formal names" $ do
            let term =
                    Term.Node
                        ( RefinedSymbol
                            "context"
                            true
                        )
                        [ Term.Node (RefinedSymbol "a" (refinementFormula (\v -> v .== variable "a"))) []
                        , Term.Node (RefinedSymbol "b" (refinementFormula (\v -> v .== variable "b"))) []
                        , Term.Node (RefinedSymbol "x" (refinementFormula (\v -> v .== variable "x"))) []
                        , Term.Node (RefinedSymbol "x" (refinementFormula (\v -> v .== variable "x"))) []
                        ]
                duplicates =
                    Substitute
                        [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
                identityFirst =
                    Substitute
                        [Substitution (path [2]) (path [3]), Substitution (path [0]) (path [2])]
            evaluateGuard tableEntailment (duplicates $ Same (path [0]) (path [2])) term >>= (`shouldBe` Yes)
            evaluateGuard tableEntailment (duplicates $ Same (path [1]) (path [2])) term >>= (`shouldBe` No)
            evaluateGuard tableEntailment (identityFirst $ Same (path [0]) (path [3])) term >>= (`shouldBe` Yes)
            evaluateGuard tableEntailment (identityFirst $ Same (path [1]) (path [3])) term >>= (`shouldBe` No)

        it "applies nested equality scopes from the inner scope to the outer scope" $ do
            let term =
                    Term.Node
                        ( RefinedSymbol
                            "triple"
                            true
                        )
                        [ Term.Node (RefinedSymbol "x" (refinementFormula (\v -> v .== variable "x"))) []
                        , Term.Node (RefinedSymbol "y" (refinementFormula (\v -> v .== variable "y"))) []
                        , Term.Node (RefinedSymbol "z" (refinementFormula (\v -> v .== variable "z"))) []
                        ]
                guard =
                    Substitute [Substitution (path [0]) (path [1])]
                        $ Substitute [Substitution (path [1]) (path [2])]
                        $ Same (path [0]) (path [2])
            evaluateGuard tableEntailment guard term >>= (`shouldBe` Yes)

        it "retains Boolean and missing-path behavior inside equality substitution scopes" $ do
            let term = Term.Node (RefinedSymbol "pair" true) [Term.Node (RefinedSymbol "x" true) [], Term.Node (RefinedSymbol "y" true) []]
                scope = Substitute [Substitution (path [0]) (path [1])]
                same = Same (path [0]) (path [1])
                missing = Same (path [2]) (path [2])
            evaluateGuard tableEntailment (scope $ Not same) term >>= (`shouldBe` No)
            evaluateGuard tableEntailment (scope $ Or [Bottom, same]) term >>= (`shouldBe` Yes)
            evaluateGuard tableEntailment (scope missing) term >>= (`shouldBe` No)
            evaluateGuard tableEntailment (scope $ Not missing) term >>= (`shouldBe` Yes)
            evaluateGuard tableEntailment (scope $ Or [missing, same]) term >>= (`shouldBe` Yes)

        it "rejects an equality scope whose actual or formal position is absent" $ do
            let term = Term.Node (RefinedSymbol "leaf" true) []
                same = Same (path []) (path [])
                missingActual = Substitute [Substitution (path [0]) (path [])] same
                missingFormal = Substitute [Substitution (path []) (path [0])] same
            evaluateGuard tableEntailment missingActual term >>= (`shouldBe` No)
            evaluateGuard tableEntailment missingFormal term >>= (`shouldBe` No)
            evaluateGuard tableEntailment (Not missingActual) term >>= (`shouldBe` Yes)

        it "checks scoped syntactic equality without comparing huge actual value identities" $ do
            let huge =
                    iterate (\child -> Term.Node (RefinedSymbol "app" true) [child, child]) (Term.Node (RefinedSymbol "leaf" true) []) !! 45
                term =
                    Term.Node
                        ( RefinedSymbol
                            "context"
                            true
                        )
                        [huge, huge, Term.Node (RefinedSymbol "x" true) [], Term.Node (RefinedSymbol "y" true) []]
                scope =
                    Substitute
                        [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
            result <- timeout 60000000 $ do
                reflexive <- evaluateGuard tableEntailment (scope $ Same (path []) (path [])) term >>= evaluate
                literalNames <- evaluateGuard tableEntailment (scope $ Same (path [2]) (path [3])) term >>= evaluate
                pure (reflexive, literalNames)
            result `shouldBe` Just (Yes, Yes)

        it "empties an edge whose guard equalities are contradictory" $ do
            -- Same 0 (0.0) asks a child to equal its own child, which no term
            -- does. The guard is not contradictory as a guard, but its
            -- equalities are, so mkEdge empties the edge. An intersection
            -- builds the same contradiction from two guards that terms meet.
            let leafA = Node [Transition "a" true [] noConstraint]
                inner = Node [Transition "f" true [leafA] noConstraint, Transition "a" true [] noConstraint]
                guarded guard = Node [Transition "f" true [inner] (semanticConstraint guard)] :: Automaton
                pairs guard = Node [Transition "g" true [inner, inner] (semanticConstraint guard)] :: Automaton
                count = length . termsWith (RefinedSymbol "Mu" true)
            count (guarded (Same (path [0]) (path [0, 0]))) `shouldBe` 0
            count (pairs (Same (path [0]) (path [1]))) `shouldBe` 2
            count (pairs (Same (path [1]) (path [0, 0]))) `shouldBe` 1
            count (pairs (Same (path [0]) (path [1])) `intersect` pairs (Same (path [1]) (path [0, 0]))) `shouldBe` 0
