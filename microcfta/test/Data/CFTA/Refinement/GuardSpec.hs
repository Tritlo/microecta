{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.GuardSpec (spec) where

import Control.Exception (IOException, evaluate, try)
import qualified Data.Tree as Tree
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Constraint (contractTermName)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Refinement (
    Automaton,
    Entailment (entails),
    Guard (Bottom, Entails, Holds, Not, Or, Same, Satisfies, Substitute),
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
import Data.CFTA.Refinement.Expression (false, refinementFormula, toExpr, true, variable, (.&&), (.==), (.>=))
import Data.CFTA.Refinement.Guard (anyOf, buildGuard, isSameTermAs, notGuard, requires, withActualFor)
import Data.CFTA.Refinement.LiquidFixpoint (TimeLimitReached (..), withZ3, withZ3Timeout)
import Data.CFTA.Refinement.TestSupport (tableEntailment)
import qualified Language.Fixpoint.Types as Fixpoint

spec :: Spec
spec =
    describe "LTA guard syntax" $ do
        it "states a literal precondition without a phantom predicate child" $ do
            let nonNegative v = v .>= 0
                guard = buildGuard $ \denominator -> denominator `requires` nonNegative
                term = Tree.Node (RefinedSymbol "divide" true) [Tree.Node (RefinedSymbol "n" (refinementFormula nonNegative)) []]
            guard `shouldBe` semanticConstraint (Satisfies (path [0]) (refinementFormula nonNegative))
            evaluateConstraint tableEntailment guard term >>= (`shouldBe` Yes)

        it "rejects a child whose refinement does not establish the requirement" $ do
            let nonNegative v = v .>= 0
                guard = buildGuard $ \denominator -> denominator `requires` nonNegative
                term = Tree.Node (RefinedSymbol "divide" true) [Tree.Node (RefinedSymbol "n" true) []]
            evaluateConstraint tableEntailment guard term >>= (`shouldBe` No)

        it "keeps syntactic equality inside the full Boolean constraint language" $ do
            let same = buildGuard $ \left right -> left `isSameTermAs` right
                different = notGuard same
                equalTerm = Tree.Node (RefinedSymbol "pair" true) [Tree.Node (RefinedSymbol "x" true) [], Tree.Node (RefinedSymbol "x" true) []]
                differentTerm = Tree.Node (RefinedSymbol "pair" true) [Tree.Node (RefinedSymbol "x" true) [], Tree.Node (RefinedSymbol "y" true) []]
                differentlyRefinedTerm =
                    Tree.Node
                        ( RefinedSymbol
                            "pair"
                            true
                        )
                        [Tree.Node (RefinedSymbol "x" true) [], Tree.Node (RefinedSymbol "x" (refinementFormula (\v -> v .== 1))) []]
                equalityOrRequirement = anyOf [same, buildGuard $ \left -> left `requires` const true]
            same `shouldBe` semanticConstraint (Same (path [0]) (path [1]))
            evaluateConstraint tableEntailment same differentlyRefinedTerm >>= (`shouldBe` No)
            evaluateConstraint tableEntailment different equalTerm >>= (`shouldBe` No)
            evaluateConstraint tableEntailment different differentTerm >>= (`shouldBe` Yes)
            evaluateConstraint tableEntailment equalityOrRequirement differentTerm >>= (`shouldBe` Yes)

        it "rejects equality at missing paths and accepts its negation" $ do
            let term = Tree.Node (RefinedSymbol "leaf" true) []
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
            let term = Tree.Node (RefinedSymbol "pair" true) [Tree.Node (RefinedSymbol "x" true) [], Tree.Node (RefinedSymbol "y" true) []]
                same = Same (path [0]) (path [1])
                scoped = Substitute [Substitution (path [0]) (path [1])] same
            evaluateGuard tableEntailment same term >>= (`shouldBe` No)
            evaluateGuard tableEntailment scoped term >>= (`shouldBe` Yes)
            evaluateGuard tableEntailment (Substitute [] same) term >>= (`shouldBe` No)
            evaluateGuard tableEntailment same term >>= (`shouldBe` No)

        it "puts cached positive equality inside the named substitution scope" $ do
            let term = Tree.Node (RefinedSymbol "pair" true) [Tree.Node (RefinedSymbol "x" true) [], Tree.Node (RefinedSymbol "y" true) []]
                cached = equalityConstraint $ mkEqConstraints [[path [0], path [1]]]
                scoped = buildGuard $ \actual formal -> withActualFor actual formal cached
            evaluateConstraint tableEntailment cached term >>= (`shouldBe` No)
            evaluateConstraint tableEntailment scoped term >>= (`shouldBe` Yes)

        it "renames nested constructor symbols and free refinement names before comparison" $ do
            let annotated symbol name =
                    Tree.Node
                        ( RefinedSymbol
                            "box"
                            (refinementFormula (\v -> v .== variable name))
                        )
                        [Tree.Node (RefinedSymbol symbol (refinementFormula (\v -> v .== variable name))) []]
                term =
                    Tree.Node
                        ( RefinedSymbol
                            "context"
                            true
                        )
                        [ Tree.Node (RefinedSymbol "x" true) []
                        , Tree.Node (RefinedSymbol "y" true) []
                        , annotated "x" "x"
                        , annotated "y" "y"
                        ]
                same = Same (path [2]) (path [3])
                scoped = Substitute [Substitution (path [0]) (path [1])] same
            evaluateGuard tableEntailment same term >>= (`shouldBe` No)
            evaluateGuard tableEntailment scoped term >>= (`shouldBe` Yes)

        it "does not replace a formal leaf with the whole actual subtree" $ do
            let term =
                    Tree.Node
                        ( RefinedSymbol
                            "context"
                            true
                        )
                        [ Tree.Node (RefinedSymbol "app" true) [Tree.Node (RefinedSymbol "argument" true) []]
                        , Tree.Node (RefinedSymbol "formal" true) []
                        ]
                guard =
                    Substitute
                        [Substitution (path [0]) (path [1])]
                        (Same (path [0]) (path [1]))
            evaluateGuard tableEntailment guard term >>= (`shouldBe` No)

        it "applies a symbol swap simultaneously within one equality scope" $ do
            let term = Tree.Node (RefinedSymbol "pair" true) [Tree.Node (RefinedSymbol "x" true) [], Tree.Node (RefinedSymbol "y" true) []]
                scope =
                    Substitute
                        [Substitution (path [0]) (path [1]), Substitution (path [1]) (path [0])]
                annotated =
                    Tree.Node
                        ( RefinedSymbol
                            "context"
                            true
                        )
                        [ Tree.Node (RefinedSymbol "x" true) []
                        , Tree.Node (RefinedSymbol "y" true) []
                        , Tree.Node (RefinedSymbol "predicate" (refinementFormula (\v -> v .== variable "x"))) []
                        , Tree.Node (RefinedSymbol "predicate" (refinementFormula (\v -> v .== variable "y"))) []
                        ]
            evaluateGuard tableEntailment (scope $ Same (path [0]) (path [1])) term >>= (`shouldBe` No)
            evaluateGuard tableEntailment (scope $ Same (path [2]) (path [3])) annotated >>= (`shouldBe` No)

        it "uses the first nonidentity replacement for duplicate formal names" $ do
            let term =
                    Tree.Node
                        ( RefinedSymbol
                            "context"
                            true
                        )
                        [ Tree.Node (RefinedSymbol "a" (refinementFormula (\v -> v .== variable "a"))) []
                        , Tree.Node (RefinedSymbol "b" (refinementFormula (\v -> v .== variable "b"))) []
                        , Tree.Node (RefinedSymbol "x" (refinementFormula (\v -> v .== variable "x"))) []
                        , Tree.Node (RefinedSymbol "x" (refinementFormula (\v -> v .== variable "x"))) []
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
                    Tree.Node
                        ( RefinedSymbol
                            "triple"
                            true
                        )
                        [ Tree.Node (RefinedSymbol "x" (refinementFormula (\v -> v .== variable "x"))) []
                        , Tree.Node (RefinedSymbol "y" (refinementFormula (\v -> v .== variable "y"))) []
                        , Tree.Node (RefinedSymbol "z" (refinementFormula (\v -> v .== variable "z"))) []
                        ]
                guard =
                    Substitute [Substitution (path [0]) (path [1])]
                        $ Substitute [Substitution (path [1]) (path [2])]
                        $ Same (path [0]) (path [2])
            evaluateGuard tableEntailment guard term >>= (`shouldBe` Yes)

        it "retains Boolean and missing-path behavior inside equality substitution scopes" $ do
            let term = Tree.Node (RefinedSymbol "pair" true) [Tree.Node (RefinedSymbol "x" true) [], Tree.Node (RefinedSymbol "y" true) []]
                scope = Substitute [Substitution (path [0]) (path [1])]
                same = Same (path [0]) (path [1])
                missing = Same (path [2]) (path [2])
            evaluateGuard tableEntailment (scope $ Not same) term >>= (`shouldBe` No)
            evaluateGuard tableEntailment (scope $ Or [Bottom, same]) term >>= (`shouldBe` Yes)
            evaluateGuard tableEntailment (scope missing) term >>= (`shouldBe` No)
            evaluateGuard tableEntailment (scope $ Not missing) term >>= (`shouldBe` Yes)
            evaluateGuard tableEntailment (scope $ Or [missing, same]) term >>= (`shouldBe` Yes)

        it "rejects an equality scope whose actual or formal position is absent" $ do
            let term = Tree.Node (RefinedSymbol "leaf" true) []
                same = Same (path []) (path [])
                missingActual = Substitute [Substitution (path [0]) (path [])] same
                missingFormal = Substitute [Substitution (path []) (path [0])] same
            evaluateGuard tableEntailment missingActual term >>= (`shouldBe` No)
            evaluateGuard tableEntailment missingFormal term >>= (`shouldBe` No)
            evaluateGuard tableEntailment (Not missingActual) term >>= (`shouldBe` Yes)

        it "does not capture a free refinement name when comparing quantified annotations" $ do
            let quantified body = Fixpoint.PAll [(Fixpoint.symbol ("x" :: String), Fixpoint.FInt)] body
                term =
                    Tree.Node
                        ( RefinedSymbol
                            "context"
                            true
                        )
                        [ Tree.Node (RefinedSymbol "x" true) []
                        , Tree.Node (RefinedSymbol "y" true) []
                        , Tree.Node (RefinedSymbol "predicate" (quantified $ variable "y" .== variable "x")) []
                        , Tree.Node (RefinedSymbol "predicate" (quantified $ variable "x" .== variable "x")) []
                        ]
                guard =
                    Substitute
                        [Substitution (path [0]) (path [1])]
                        (Same (path [2]) (path [3]))
            evaluateGuard tableEntailment guard term >>= (`shouldBe` No)

        it "checks scoped syntactic equality without comparing huge actual value identities" $ do
            let huge =
                    iterate (\child -> Tree.Node (RefinedSymbol "app" true) [child, child]) (Tree.Node (RefinedSymbol "leaf" true) []) !! 45
                term =
                    Tree.Node
                        ( RefinedSymbol
                            "context"
                            true
                        )
                        [huge, huge, Tree.Node (RefinedSymbol "x" true) [], Tree.Node (RefinedSymbol "y" true) []]
                scope =
                    Substitute
                        [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
            result <- timeout 60000000 $ do
                reflexive <- evaluateGuard tableEntailment (scope $ Same (path []) (path [])) term >>= evaluate
                literalNames <- evaluateGuard tableEntailment (scope $ Same (path [2]) (path [3])) term >>= evaluate
                pure (reflexive, literalNames)
            result `shouldBe` Just (Yes, Yes)

        it "connects a substituted node symbol to that node's refinement" $ do
            let model :: Fixpoint.Expr
                model = Fixpoint.EVar $ Fixpoint.symbol ("model" :: String)
                declarations =
                    [ (Fixpoint.symbol name, Fixpoint.FInt)
                    | name <- ["v", "model", "previous"] :: [String]
                    ]
                guard =
                    Substitute
                        [Substitution (path [0]) (path [1, 0])]
                        (Entails (path [1, 1]) (path []))
                term =
                    Tree.Node
                        ( RefinedSymbol
                            "step"
                            (refinementFormula (\v -> v .== 1))
                        )
                        [ Tree.Node (RefinedSymbol "previous" (refinementFormula (\v -> v .== 0))) []
                        , Tree.Node
                            ( RefinedSymbol
                                "command"
                                true
                            )
                            [ Tree.Node (RefinedSymbol "model" true) []
                            , Tree.Node (RefinedSymbol "post-state" (refinementFormula (\v -> v .== (toExpr model + 1)))) []
                            ]
                        ]
            withZ3 declarations $ \solver ->
                evaluateGuard solver guard term >>= (`shouldBe` Yes)

        it "names one term for two indexes of a contract with the same path" $ do
            -- Both names denote the child, so the contract is reflexive and its
            -- negation is refuted.
            let term = Tree.Node (RefinedSymbol "host" true) [Tree.Node (RefinedSymbol "x" (variable "v" .>= 0)) []]
                reflexive = Holds [path [0], path [0]] (variable (contractTermName 0) .== variable (contractTermName 1))
            withZ3 [] $ \solver -> do
                evaluateGuard solver reflexive term >>= (`shouldBe` Yes)
                evaluateGuard solver (Not reflexive) term >>= (`shouldBe` No)

        it "answers correctly after the solver rejects a query" $ do
            -- Z3 rejects the assertion that applies the Int constant f, and it
            -- still answers the check-sat. The rejection is an exception. The
            -- next queries go to a new solver process, so each one reads its
            -- own answer, not the answer of the query before it.
            let x = Fixpoint.EVar (Fixpoint.symbol ("x" :: String))
                f = Fixpoint.EVar (Fixpoint.symbol ("f" :: String))
                rejected = Fixpoint.PAtom Fixpoint.Gt (Fixpoint.EApp f x) (Fixpoint.expr (0 :: Int))
                positive = Fixpoint.PAtom Fixpoint.Gt x (Fixpoint.expr (0 :: Int))
                nonNegative = Fixpoint.PAtom Fixpoint.Ge x (Fixpoint.expr (0 :: Int))
            withZ3 [(Fixpoint.symbol ("x" :: String), Fixpoint.FInt), (Fixpoint.symbol ("f" :: String), Fixpoint.FInt)] $ \solver -> do
                rejection <- try (entails solver rejected positive) :: IO (Either IOException Verdict)
                either (const True) (const False) rejection `shouldBe` True
                results <- mapM (uncurry $ entails solver) [(positive, nonNegative), (nonNegative, positive), (positive, nonNegative)]
                results `shouldBe` [Yes, No, Yes]

        it "answers correctly after a query is interrupted" $ do
            -- An interrupted query can leave its answer unread in the solver
            -- process. The next query goes to a new process, so it reads its
            -- own answer. The waits cover interruptions before the query is
            -- sent, while Z3 runs, and after it answers.
            let v = variable "v"
            withZ3 [] $ \solver -> do
                answers <-
                    mapM
                        ( \micros -> do
                            _ <- timeout micros (entails solver (v .== 0) (v .>= 0))
                            entails solver (v .== 0) (v .== 1)
                        )
                        [1, 5, 20, 50, 100, 200, 500, 1000, 2000, 5000]
                answers `shouldBe` replicate 10 No

        it "raises TimeLimitReached when a query reaches the time limit" $ do
            -- Z3 did not decide this query about cubes in five minutes, so a
            -- limit of 200 milliseconds stops it. The next query still gets
            -- its own answer.
            let x = variable "x"
                y = variable "y"
                z = variable "z"
                cubes = x .>= 1 .&& y .>= 1 .&& z .>= 1 .&& x * x * x + y * y * y .== z * z * z
            withZ3Timeout 200 [] [] $ \solver -> do
                reached <- try (entails solver cubes false)
                reached `shouldBe` (Left (TimeLimitReached 200) :: Either TimeLimitReached Verdict)
                entails solver (x .>= 1) (x .>= 0) >>= (`shouldBe` Yes)

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
