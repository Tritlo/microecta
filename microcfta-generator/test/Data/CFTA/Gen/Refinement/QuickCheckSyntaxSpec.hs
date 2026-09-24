module Data.CFTA.Gen.Refinement.QuickCheckSyntaxSpec (spec) where

import Control.Monad (forM_, void)
import qualified Data.Tree as Tree
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.CFTA.Gen.Refinement as LTAGen
import Data.CFTA.Gen.Refinement.TestSupport (termsOf, values)
import Data.CFTA.Gen.Refinement.TypedExpressionLanguage (nonNegative)
import Data.CFTA.Refinement (
    AutomatonError (GuardArityMismatch),
    Entailment (Entailment),
    Guard (Bottom, Entails, Satisfies, Top),
    LiquidSymbol (LiquidSymbol),
    Verdict (No, Unknown, Yes),
    path,
    semanticConstraint,
 )
import Data.CFTA.Refinement.Expression (Expr, false, refinementFormula, toExpr, true, (.<), (.==))
import Data.CFTA.Refinement.Guard (
    anyOf,
    argument,
    buildGuard,
    isSameTermAs,
    isSubtypeOf,
    notGuard,
    requires,
    root,
    withActualFor,
    withActualsFor,
 )
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import qualified Language.Fixpoint.Types as Fixpoint

spec :: Spec
spec = do
    describe "QuickCheck-facing LTA syntax" $ do
        it "turns named lambda arguments into paths without magic indices" $
            buildGuard (\actual expected -> actual `isSubtypeOf` expected)
                `shouldBe` semanticConstraint (Entails (path [0]) (path [1]))

        it "keeps explicit positions as a programmatic escape hatch" $
            argument 0 `isSubtypeOf` argument 1
                `shouldBe` buildGuard (\actual expected -> actual `isSubtypeOf` expected)

        it "states ordinary preconditions in the vocabulary of a property writer" $
            buildGuard (`requires` nonNegative)
                `shouldBe` semanticConstraint (Satisfies (path [0]) (refinementFormula nonNegative))

        it "reports a named guard mismatch before any candidate is built" $ do
            let generator = LTAGen.refinedNode "wrap" (const true) (\actual expected -> actual `isSubtypeOf` expected) atom
                expectedError = Left $ LTAGen.InvalidSupport $ GuardArityMismatch "wrap" 1 2
            complete <- LTAGen.compileWith unusedEntailment generator
            checked <- LTAGen.validOutcomes unusedEntailment generator
            (complete >>= LTAGen.cardinality) `shouldBe` expectedError
            fmap length checked `shouldBe` expectedError
            void (LTAGen.support generator) `shouldBe` expectedError

        it "checks guard arity without enumerating a large child product" $ do
            let source = LTAGen.namedPool [LTAGen.Refined (0 :: Int) "zero" (const true), LTAGen.Refined 1 "one" (const true)]
                forest = foldr (\_ rest -> (:) <$> source <*> rest) (pure []) [1 .. 50 :: Int]
                generator = LTAGen.refinedNode "many" (const true) (`requires` const true) forest
            compiled <- LTAGen.compileWith unusedEntailment generator
            (compiled >>= LTAGen.cardinality)
                `shouldBe` Left (LTAGen.InvalidSupport $ GuardArityMismatch "many" 50 1)

    describe "accepted alternatives" $ do
        it "ignores a rejected alternative" $ do
            let generator = LTAGen.oneof [atom, nested Bottom]
            complete <- LTAGen.compileWith unusedEntailment generator
            (complete >>= LTAGen.cardinality) `shouldBe` Right 1
            fmap values complete `shouldBe` Right [1]

        it "retains only the groups accepted by a parent guard" $ do
            let choices =
                    LTAGen.oneof [LTAGen.leaf (1 :: Int) "x" (const false), nested Top]
            let generator = LTAGen.refinedNode "parent" (const true) (Satisfies (path [0]) false) choices
                entailment = Entailment $ \antecedent consequent ->
                    pure $ if antecedent == false || consequent == true || antecedent == consequent then Yes else No
            complete <- LTAGen.compileWith entailment generator
            (complete >>= LTAGen.cardinality) `shouldBe` Right 1
            fmap values complete `shouldBe` Right [1]

        it "compiles a compact product without decoding members" $ do
            let source = LTAGen.namedPool [LTAGen.Refined (0 :: Int) "zero" (const true), LTAGen.Refined 1 "one" (const true)]
                forest = foldr (\_ rest -> (:) <$> source <*> rest) (pure []) [1 .. 50 :: Int]
            compiled <- LTAGen.compileWith unusedEntailment $ LTAGen.node "many" forest
            (compiled >>= LTAGen.cardinality) `shouldBe` Right (2 ^ (50 :: Int))

        it "preserves fresh value declarations through the compilation cache" $
            withZ3 [(Fixpoint.symbol name, Fixpoint.FInt) | name <- ["v", "app", "x", "y"] :: [String]] $ \solver -> do
                let variable :: String -> Expr
                    variable = toExpr . Fixpoint.EVar . Fixpoint.symbol
                    actual :: Int -> LTAGen.LTAGen Int
                    actual integer =
                        LTAGen.refinedNode "app" (const $ variable "v" .== fromIntegral integer) Top $
                            LTAGen.leaf integer "input" (const true)
                    forest =
                        (,,,)
                            <$> actual (0 :: Int)
                            <*> actual 1
                            <*> LTAGen.leaf () "x" (const true)
                            <*> LTAGen.leaf () "y" (const true)
                    constraint =
                        withActualsFor [(argument 0, argument 2), (argument 1, argument 3)] $
                            root `requires` const (variable "x" .< variable "y")
                    generator = LTAGen.refinedNode "pair" (const true) constraint forest
                complete <- LTAGen.compileWith solver generator
                (complete >>= LTAGen.cardinality) `shouldBe` Right 1
                fmap values complete `shouldBe` Right [(0, 1, (), ())]

    describe "relational substitution identity" $ do
        it "treats repeated nominal leaves as the same actual value" $ do
            let nominal = LTAGen.leaf (1 :: Int) "shared" (const true)
            result <- compileActualEquality nominal nominal
            result `shouldBe` Right 2

        it "reports unavailable compound identity when distinct subtrees have matching roots" $ do
            let application symbol value = LTAGen.refinedNode "app" (const true) Top $ LTAGen.leaf value symbol (const true)
            result <- compileActualEquality (application "left-input" 0) (application "right-input" 1)
            result `shouldBe` Left LTAGen.SolverUnknown

        it "reports unavailable compound identity without enumerating actuals" $ do
            let application = LTAGen.refinedNode "app" (const true) Top $ LTAGen.leaf 1 "input" (const true)
            result <- compileActualEquality application application
            result `shouldBe` Left LTAGen.SolverUnknown

    describe "structural equality under explicit substitution" $ do
        it "compares renamed symbols and refinements while preserving source values and witnesses" $ do
            let variable :: String -> Expr
                variable = toExpr . Fixpoint.EVar . Fixpoint.symbol
                annotation name = const (variable "v" .== variable name)
                actuals =
                    LTAGen.namedPool
                        [ LTAGen.Refined (10 :: Int) "a" $ annotation "a"
                        , LTAGen.Refined 20 "b" $ annotation "b"
                        ]
                formal = LTAGen.leaf (99 :: Int) "x" $ annotation "x"
                generator =
                    LTAGen.refinedNode
                        "pair"
                        (const true)
                        (\actual formalPosition -> withActualFor actual formalPosition $ actual `isSameTermAs` formalPosition)
                        $ (,) <$> actuals <*> formal
                expected =
                    [ ( (actual, 99)
                      , Tree.Node
                            (LiquidSymbol "pair" true)
                            [ Tree.Node (LiquidSymbol symbol (refinementFormula $ annotation name)) []
                            , Tree.Node (LiquidSymbol "x" (refinementFormula $ annotation "x")) []
                            ]
                      )
                    | (actual, symbol, name) <- [(10, "a", "a"), (20, "b", "b")]
                    ]
            compiled <- LTAGen.compileWith unusedEntailment generator >>= either (fail . show) pure
            LTAGen.cardinality compiled `shouldBe` Right 2
            LTAGen.validOutcomes unusedEntailment generator >>= (`shouldBe` Right (map fst expected))
            zip (values compiled) (termsOf compiled) `shouldBe` expected

        it "keeps tree shape when scoped equality occurs inside negation and disjunction" $ do
            let actuals =
                    LTAGen.oneof
                        [ LTAGen.leaf (1 :: Int) "atom" (const true)
                        , LTAGen.node "box" $ LTAGen.leaf 2 "payload" (const true)
                        ]
            let atomTerm = Tree.Node (LiquidSymbol "atom" true) []
                compoundTerm = Tree.Node (LiquidSymbol "box" true) [Tree.Node (LiquidSymbol "payload" true) []]
                acceptedAtoms = [(1, atomTerm)]
                acceptedCompounds = [(2, compoundTerm)]
                alternatives =
                    [ (id, acceptedAtoms)
                    , (notGuard, acceptedCompounds)
                    , (\same -> anyOf [same, notGuard same], acceptedAtoms <> acceptedCompounds)
                    ]
            forM_ alternatives $ \(predicate, accepted) -> do
                let generator =
                        LTAGen.refinedNode
                            "pair"
                            (const true)
                            (\actual formal -> withActualFor actual formal $ predicate $ actual `isSameTermAs` formal)
                            $ (,) <$> actuals <*> LTAGen.leaf (9 :: Int) "x" (const true)
                    expected =
                        [ ((actual, 9), Tree.Node (LiquidSymbol "pair" true) [term, Tree.Node (LiquidSymbol "x" true) []])
                        | (actual, term) <- accepted
                        ]
                compiled <- LTAGen.compileWith unusedEntailment generator >>= either (fail . show) pure
                LTAGen.cardinality compiled `shouldBe` Right (toInteger $ length expected)
                LTAGen.validOutcomes unusedEntailment generator >>= (`shouldBe` Right (map fst expected))
                zip (values compiled) (termsOf compiled) `shouldBe` expected
  where
    unusedEntailment = Entailment $ \_ _ -> pure Unknown
    atom = LTAGen.leaf (1 :: Int) "x" (const true)
    nested guard = LTAGen.refinedNode "x" (const true) guard $ LTAGen.leaf (2 :: Int) "item" (const true)

-- | Compile an actual-value equality with one unconstrained alternative.
compileActualEquality ::
    LTAGen.LTAGen Int ->
    LTAGen.LTAGen Int ->
    IO (Either LTAGen.GenError Integer)
compileActualEquality left right =
    withZ3 [(Fixpoint.symbol name, Fixpoint.FInt) | name <- ["v", "shared", "app", "x", "y"] :: [String]] $ \solver -> do
        let variable :: String -> Expr
            variable = toExpr . Fixpoint.EVar . Fixpoint.symbol
            forest =
                (\actualLeft actualRight _ _ -> (actualLeft, actualRight))
                    <$> left
                    <*> right
                    <*> LTAGen.leaf () "x" (const true)
                    <*> LTAGen.leaf () "y" (const true)
            constraint =
                withActualsFor [(argument 0, argument 2), (argument 1, argument 3)] $
                    root `requires` const (variable "x" .== variable "y")
        let generator =
                LTAGen.oneof [LTAGen.refinedNode "pair" (const true) constraint forest, LTAGen.leaf (-1, -1) "sentinel" (const true)]
        complete <- LTAGen.compileWith solver generator
        pure $ complete >>= LTAGen.cardinality
