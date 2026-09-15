module Data.LTA.GuardSpec (spec) where

import Control.Exception (evaluate)
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.ECTA.Paths (mkEqConstraints)
import Data.LTA (
    Guard (Bottom, Entails, Not, Or, Same, Satisfies, Substitute),
    LiquidTerm (LiquidTerm),
    Substitution (Substitution),
    Verdict (..),
    equalityConstraint,
    evaluateConstraint,
    evaluateGuard,
    evaluateGuardWithShape,
    path,
    semanticConstraint,
 )
import Data.LTA.Guard (anyOf, buildGuard, isSameTermAs, notGuard, requires, withActualFor)
import Data.LTA.LiquidFixpoint (withZ3)
import Data.LTA.Refinement (true, value, variable, (.+.), (.==.), (.>=.))
import Data.LTA.TestSupport (tableEntailment)
import qualified Language.Fixpoint.Types as Fixpoint

spec :: Spec
spec =
    describe "LTA guard syntax" $ do
        it "states a literal precondition without a phantom predicate child" $ do
            let nonNegative = value .>=. (0 :: Int)
                guard = buildGuard $ \denominator -> denominator `requires` nonNegative
                term = LiquidTerm "divide" true [LiquidTerm "n" nonNegative []]
            guard `shouldBe` semanticConstraint (Satisfies (path [0]) nonNegative)
            evaluateConstraint tableEntailment guard term >>= (`shouldBe` Yes)

        it "rejects a child whose refinement does not establish the requirement" $ do
            let nonNegative = value .>=. (0 :: Int)
                guard = buildGuard $ \denominator -> denominator `requires` nonNegative
                term = LiquidTerm "divide" true [LiquidTerm "n" true []]
            evaluateConstraint tableEntailment guard term >>= (`shouldBe` No)

        it "keeps syntactic equality inside the full Boolean constraint language" $ do
            let same = buildGuard $ \left right -> left `isSameTermAs` right
                different = notGuard same
                equalTerm = LiquidTerm "pair" true [LiquidTerm "x" true [], LiquidTerm "x" true []]
                differentTerm = LiquidTerm "pair" true [LiquidTerm "x" true [], LiquidTerm "y" true []]
                differentlyRefinedTerm =
                    LiquidTerm
                        "pair"
                        true
                        [LiquidTerm "x" true [], LiquidTerm "x" (value .==. (1 :: Int)) []]
                equalityOrRequirement = anyOf [same, buildGuard $ \left -> left `requires` true]
            same `shouldBe` semanticConstraint (Same (path [0]) (path [1]))
            evaluateConstraint tableEntailment same differentlyRefinedTerm >>= (`shouldBe` No)
            evaluateConstraint tableEntailment different equalTerm >>= (`shouldBe` No)
            evaluateConstraint tableEntailment different differentTerm >>= (`shouldBe` Yes)
            evaluateConstraint tableEntailment equalityOrRequirement differentTerm >>= (`shouldBe` Yes)

        it "rejects equality at missing paths and accepts its negation" $ do
            let term = LiquidTerm "leaf" true []
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
                    | target == left || target == right = Just ("app", true)
                    | otherwise = Nothing
            evaluateGuardWithShape tableEntailment observe (const Nothing) (Same left left) >>= (`shouldBe` Yes)
            evaluateGuardWithShape tableEntailment observe (const Nothing) (Same left right) >>= (`shouldBe` Unknown)
            evaluateGuardWithShape tableEntailment observe (const Nothing) (Same (path [2]) (path [2])) >>= (`shouldBe` No)

        it "compares renamed variable leaves only inside an explicit substitution scope" $ do
            let term = LiquidTerm "pair" true [LiquidTerm "x" true [], LiquidTerm "y" true []]
                same = Same (path [0]) (path [1])
                scoped = Substitute [Substitution (path [0]) (path [1])] same
            evaluateGuard tableEntailment same term >>= (`shouldBe` No)
            evaluateGuard tableEntailment scoped term >>= (`shouldBe` Yes)
            evaluateGuard tableEntailment (Substitute [] same) term >>= (`shouldBe` No)
            evaluateGuard tableEntailment same term >>= (`shouldBe` No)

        it "puts cached positive equality inside the named substitution scope" $ do
            let term = LiquidTerm "pair" true [LiquidTerm "x" true [], LiquidTerm "y" true []]
                cached = equalityConstraint $ mkEqConstraints [[path [0], path [1]]]
                scoped = buildGuard $ \actual formal -> withActualFor actual formal cached
            evaluateConstraint tableEntailment cached term >>= (`shouldBe` No)
            evaluateConstraint tableEntailment scoped term >>= (`shouldBe` Yes)

        it "renames nested constructor symbols and free refinement names before comparison" $ do
            let annotated symbol name =
                    LiquidTerm
                        "box"
                        (value .==. variable name)
                        [LiquidTerm symbol (value .==. variable name) []]
                term =
                    LiquidTerm
                        "context"
                        true
                        [ LiquidTerm "x" true []
                        , LiquidTerm "y" true []
                        , annotated "x" "x"
                        , annotated "y" "y"
                        ]
                same = Same (path [2]) (path [3])
                scoped = Substitute [Substitution (path [0]) (path [1])] same
            evaluateGuard tableEntailment same term >>= (`shouldBe` No)
            evaluateGuard tableEntailment scoped term >>= (`shouldBe` Yes)

        it "does not replace a formal leaf with the whole actual subtree" $ do
            let term =
                    LiquidTerm
                        "context"
                        true
                        [ LiquidTerm "app" true [LiquidTerm "argument" true []]
                        , LiquidTerm "formal" true []
                        ]
                guard =
                    Substitute
                        [Substitution (path [0]) (path [1])]
                        (Same (path [0]) (path [1]))
            evaluateGuard tableEntailment guard term >>= (`shouldBe` No)

        it "applies a symbol swap simultaneously within one equality scope" $ do
            let term = LiquidTerm "pair" true [LiquidTerm "x" true [], LiquidTerm "y" true []]
                scope =
                    Substitute
                        [Substitution (path [0]) (path [1]), Substitution (path [1]) (path [0])]
                annotated =
                    LiquidTerm
                        "context"
                        true
                        [ LiquidTerm "x" true []
                        , LiquidTerm "y" true []
                        , LiquidTerm "predicate" (value .==. variable "x") []
                        , LiquidTerm "predicate" (value .==. variable "y") []
                        ]
            evaluateGuard tableEntailment (scope $ Same (path [0]) (path [1])) term >>= (`shouldBe` No)
            evaluateGuard tableEntailment (scope $ Same (path [2]) (path [3])) annotated >>= (`shouldBe` No)

        it "uses the first nonidentity replacement for duplicate formal names" $ do
            let term =
                    LiquidTerm
                        "context"
                        true
                        [ LiquidTerm "a" (value .==. variable "a") []
                        , LiquidTerm "b" (value .==. variable "b") []
                        , LiquidTerm "x" (value .==. variable "x") []
                        , LiquidTerm "x" (value .==. variable "x") []
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
                    LiquidTerm
                        "triple"
                        true
                        [ LiquidTerm "x" (value .==. variable "x") []
                        , LiquidTerm "y" (value .==. variable "y") []
                        , LiquidTerm "z" (value .==. variable "z") []
                        ]
                guard =
                    Substitute [Substitution (path [0]) (path [1])]
                        $ Substitute [Substitution (path [1]) (path [2])]
                        $ Same (path [0]) (path [2])
            evaluateGuard tableEntailment guard term >>= (`shouldBe` Yes)

        it "retains Boolean and missing-path behavior inside equality substitution scopes" $ do
            let term = LiquidTerm "pair" true [LiquidTerm "x" true [], LiquidTerm "y" true []]
                scope = Substitute [Substitution (path [0]) (path [1])]
                same = Same (path [0]) (path [1])
                missing = Same (path [2]) (path [2])
            evaluateGuard tableEntailment (scope $ Not same) term >>= (`shouldBe` No)
            evaluateGuard tableEntailment (scope $ Or [Bottom, same]) term >>= (`shouldBe` Yes)
            evaluateGuard tableEntailment (scope missing) term >>= (`shouldBe` No)
            evaluateGuard tableEntailment (scope $ Not missing) term >>= (`shouldBe` Yes)
            evaluateGuard tableEntailment (scope $ Or [missing, same]) term >>= (`shouldBe` Yes)

        it "rejects an equality scope whose actual or formal position is absent" $ do
            let term = LiquidTerm "leaf" true []
                same = Same (path []) (path [])
                missingActual = Substitute [Substitution (path [0]) (path [])] same
                missingFormal = Substitute [Substitution (path []) (path [0])] same
            evaluateGuard tableEntailment missingActual term >>= (`shouldBe` No)
            evaluateGuard tableEntailment missingFormal term >>= (`shouldBe` No)
            evaluateGuard tableEntailment (Not missingActual) term >>= (`shouldBe` Yes)

        it "does not capture a free refinement name when comparing quantified annotations" $ do
            let quantified body = Fixpoint.PAll [(Fixpoint.symbol ("x" :: String), Fixpoint.FInt)] body
                term =
                    LiquidTerm
                        "context"
                        true
                        [ LiquidTerm "x" true []
                        , LiquidTerm "y" true []
                        , LiquidTerm "predicate" (quantified $ variable "y" .==. variable "x") []
                        , LiquidTerm "predicate" (quantified $ variable "x" .==. variable "x") []
                        ]
                guard =
                    Substitute
                        [Substitution (path [0]) (path [1])]
                        (Same (path [2]) (path [3]))
            evaluateGuard tableEntailment guard term >>= (`shouldBe` No)

        it "checks scoped syntactic equality without comparing huge actual value identities" $ do
            let huge = iterate (\child -> LiquidTerm "app" true [child, child]) (LiquidTerm "leaf" true []) !! 45
                term =
                    LiquidTerm
                        "context"
                        true
                        [huge, huge, LiquidTerm "x" true [], LiquidTerm "y" true []]
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
                    LiquidTerm
                        "step"
                        (value .==. (1 :: Int))
                        [ LiquidTerm "previous" (value .==. (0 :: Int)) []
                        , LiquidTerm
                            "command"
                            true
                            [ LiquidTerm "model" true []
                            , LiquidTerm "post-state" (value .==. (model .+. (1 :: Int))) []
                            ]
                        ]
            withZ3 declarations $ \solver ->
                evaluateGuard solver guard term >>= (`shouldBe` Yes)
