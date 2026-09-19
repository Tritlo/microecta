module Data.CFTA.Gen.Refinement.QuickCheckSyntaxSpec (spec) where

import Control.Monad (forM_, void)
import qualified Data.Tree as Tree
import Test.Hspec (Spec, describe, it, shouldBe)

import qualified Data.CFTA.Gen.Refinement as LTA
import Data.CFTA.Gen.Refinement.TypedExpressionLanguage (nonNegative)
import Data.CFTA.Refinement (
    AutomatonError (GuardArityMismatch, InconsistentArity),
    Entailment (Entailment),
    Guard (Bottom, Entails, Satisfies, Top),
    LiquidSymbol (LiquidSymbol),
    Verdict (No, Unknown, Yes),
    path,
    semanticConstraint,
 )
import Data.CFTA.Refinement.Expression (false, true, (.<.), (.==.))
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
                `shouldBe` semanticConstraint (Satisfies (path [0]) nonNegative)

        it "reports a named guard mismatch before either compiler filters candidates" $ do
            let generator = LTA.node "wrap" (\actual expected -> actual `isSubtypeOf` expected) atom
                expectedError = Left $ LTA.InvalidSupport $ GuardArityMismatch "wrap" 1 2
            complete <- LTA.compile unusedEntailment generator
            relational <- LTA.compileRelational unusedEntailment generator
            checked <- LTA.validOutcomes unusedEntailment generator
            fmap LTA.cardinality complete `shouldBe` expectedError
            fmap LTA.cardinality relational `shouldBe` expectedError
            fmap length checked `shouldBe` Left (LTA.InvalidSupport $ GuardArityMismatch "wrap" 1 2)
            void (LTA.support generator)
                `shouldBe` Left (LTA.InvalidSupport $ GuardArityMismatch "wrap" 1 2)

        it "checks guard arity without enumerating a large child product" $ do
            let source = LTA.pool [LTA.refined (0 :: Int) "zero" true, LTA.refined 1 "one" true]
                forest = foldr (\_ rest -> (:) <$> LTA.children source <*> rest) (pure []) [1 .. 50 :: Int]
                generator = LTA.node "many" (`requires` true) forest
            compiled <- LTA.compile unusedEntailment generator
            fmap LTA.cardinality compiled
                `shouldBe` Left (LTA.InvalidSupport $ GuardArityMismatch "many" 50 1)

    describe "relational alphabet validation" $ do
        it "rejects one symbol at different arities in the same witness" $ do
            let generator = LTA.node "x" Top $ LTA.leaf (1 :: Int) "x" true
            complete <- LTA.compile unusedEntailment generator
            relational <- LTA.compileRelational unusedEntailment generator
            fmap LTA.cardinality complete
                `shouldBe` Left (LTA.InvalidSupport $ InconsistentArity "x" 0 1)
            fmap LTA.cardinality relational
                `shouldBe` Left (LTA.InvalidSupport $ InconsistentArity "x" 0 1)

        it "rejects incompatible arities across accepted alternatives" $ do
            let generator = LTA.oneof [atom, nested Top]
            complete <- LTA.compile unusedEntailment generator
            relational <- LTA.compileRelational unusedEntailment generator
            fmap LTA.cardinality complete
                `shouldBe` Left (LTA.InvalidSupport $ InconsistentArity "x" 0 1)
            fmap LTA.cardinality relational `shouldBe` fmap LTA.cardinality complete

        it "ignores the alphabet of a rejected alternative" $ do
            let generator = LTA.oneof [atom, nested Bottom]
            complete <- LTA.compile unusedEntailment generator
            relational <- LTA.compileRelational unusedEntailment generator
            fmap LTA.cardinality complete `shouldBe` Right 1
            fmap selectedValues relational `shouldBe` fmap selectedValues complete

        it "retains arities only for the groups accepted by a parent guard" $ do
            let choices =
                    LTA.oneof [LTA.leaf (1 :: Int) "x" false, nested Top]
            let generator = LTA.node "parent" (Satisfies (path [0]) false) choices
                entailment = Entailment $ \antecedent consequent ->
                    pure $ if antecedent == false || consequent == true || antecedent == consequent then Yes else No
            complete <- LTA.compile entailment generator
            relational <- LTA.compileRelational entailment generator
            fmap LTA.cardinality complete `shouldBe` Right 1
            fmap selectedValues relational `shouldBe` fmap selectedValues complete

        it "checks the alphabet of a compact product without decoding members" $ do
            let source = LTA.pool [LTA.refined (0 :: Int) "zero" true, LTA.refined 1 "one" true]
                forest = foldr (\_ rest -> (:) <$> LTA.children source <*> rest) (pure []) [1 .. 50 :: Int]
            compiled <- LTA.compileRelational unusedEntailment $ LTA.node "many" Top forest
            fmap LTA.cardinality compiled `shouldBe` Right (2 ^ (50 :: Int))

        it "preserves fresh value declarations through both compilation caches" $
            withZ3 [(Fixpoint.symbol name, Fixpoint.FInt) | name <- ["v", "app", "x", "y"] :: [String]] $ \solver -> do
                let variable :: String -> Fixpoint.Expr
                    variable = Fixpoint.EVar . Fixpoint.symbol
                    actual :: Int -> LTA.LTAGen Int
                    actual integer =
                        LTA.unary id "app" (variable "v" .==. integer) Top $
                            LTA.leaf integer "input" true
                    forest =
                        (,,,)
                            <$> LTA.children (actual (0 :: Int))
                            <*> LTA.children (actual 1)
                            <*> LTA.children (LTA.leaf () "x" true)
                            <*> LTA.children (LTA.leaf () "y" true)
                    constraint =
                        withActualsFor [(argument 0, argument 2), (argument 1, argument 3)] $
                            root `requires` (variable "x" .<. variable "y")
                    generator = LTA.node "pair" constraint forest
                complete <- LTA.compile solver generator
                relational <- LTA.compileRelational solver generator
                fmap LTA.cardinality complete `shouldBe` Right 1
                fmap selectedValues relational `shouldBe` fmap selectedValues complete

    describe "relational substitution identity" $ do
        it "treats repeated nominal leaves as the same actual value" $ do
            let nominal = LTA.leaf (1 :: Int) "shared" true
            result <- compileActualEquality nominal nominal
            result `shouldBe` (Right 2, Right 2)

        it "reports unavailable compound identity when distinct subtrees have matching roots" $ do
            let application symbol value = LTA.unary id "app" true Top $ LTA.leaf value symbol true
            result <- compileActualEquality (application "left-input" 0) (application "right-input" 1)
            result `shouldBe` (Left LTA.SolverUnknown, Left LTA.SolverUnknown)

        it "reports unavailable compound identity without enumerating actuals" $ do
            let application = LTA.unary id "app" true Top $ LTA.leaf 1 "input" true
            result <- compileActualEquality application application
            result `shouldBe` (Left LTA.SolverUnknown, Left LTA.SolverUnknown)

    describe "structural equality under explicit substitution" $ do
        it "compares renamed symbols and refinements while preserving source values and witnesses" $ do
            let variable :: String -> Fixpoint.Expr
                variable = Fixpoint.EVar . Fixpoint.symbol
                annotation name = variable "v" .==. variable name
                actuals =
                    LTA.pool
                        [ LTA.refined (10 :: Int) "a" $ annotation "a"
                        , LTA.refined 20 "b" $ annotation "b"
                        ]
                formal = LTA.leaf (99 :: Int) "x" $ annotation "x"
                generator =
                    LTA.node
                        "pair"
                        (\actual formalPosition -> withActualFor actual formalPosition $ actual `isSameTermAs` formalPosition)
                        $ (,) <$> LTA.children actuals <*> LTA.children formal
                expected =
                    [ LTA.Generated 1 (actual, 99) $
                        Tree.Node
                            (LiquidSymbol "pair" true)
                            [ Tree.Node (LiquidSymbol symbol (annotation name)) []
                            , Tree.Node (LiquidSymbol "x" (annotation "x")) []
                            ]
                    | (actual, symbol, name) <- [(10, "a", "a"), (20, "b", "b")]
                    ]
            compiled <- LTA.compile unusedEntailment generator >>= either (fail . show) pure
            LTA.cardinality compiled `shouldBe` 2
            LTA.validOutcomes unusedEntailment generator >>= (`shouldBe` Right expected)
            forM_ (zip [0 ..] expected) $ \(rank, member) ->
                LTA.unrank compiled rank `shouldBe` Right member

        it "keeps tree shape when scoped equality occurs inside negation and disjunction" $ do
            let actuals =
                    LTA.oneof
                        [ LTA.leaf (1 :: Int) "atom" true
                        , LTA.node "box" Top $ LTA.leaf 2 "payload" true
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
                        LTA.node
                            "pair"
                            (\actual formal -> withActualFor actual formal $ predicate $ actual `isSameTermAs` formal)
                            $ (,) <$> LTA.children actuals <*> LTA.children (LTA.leaf (9 :: Int) "x" true)
                    expected =
                        [ LTA.Generated 1 (actual, 9) $ Tree.Node (LiquidSymbol "pair" true) [term, Tree.Node (LiquidSymbol "x" true) []]
                        | (actual, term) <- accepted
                        ]
                compiled <- LTA.compile unusedEntailment generator >>= either (fail . show) pure
                LTA.cardinality compiled `shouldBe` toInteger (length expected)
                LTA.validOutcomes unusedEntailment generator >>= (`shouldBe` Right expected)
                forM_ (zip [0 ..] expected) $ \(rank, member) ->
                    LTA.unrank compiled rank `shouldBe` Right member
  where
    unusedEntailment = Entailment $ \_ _ -> pure Unknown
    atom = LTA.leaf (1 :: Int) "x" true
    nested guard = LTA.node "x" guard $ LTA.leaf (2 :: Int) "item" true
    selectedValues compiled =
        [ (LTA.generatedValue generated, LTA.generatedTerm generated)
        | rank <- [0 .. LTA.cardinality compiled - 1]
        , Right generated <- [LTA.unrank compiled rank]
        ]

-- | Compile an actual-value equality with one unconstrained alternative.
compileActualEquality ::
    LTA.LTAGen Int ->
    LTA.LTAGen Int ->
    IO (Either LTA.GenError Integer, Either LTA.GenError Integer)
compileActualEquality left right =
    withZ3 [(Fixpoint.symbol name, Fixpoint.FInt) | name <- ["v", "shared", "app", "x", "y"] :: [String]] $ \solver -> do
        let variable :: String -> Fixpoint.Expr
            variable = Fixpoint.EVar . Fixpoint.symbol
            forest =
                (\actualLeft actualRight _ _ -> (actualLeft, actualRight))
                    <$> LTA.children left
                    <*> LTA.children right
                    <*> LTA.children (LTA.leaf () "x" true)
                    <*> LTA.children (LTA.leaf () "y" true)
            constraint =
                withActualsFor [(argument 0, argument 2), (argument 1, argument 3)] $
                    root `requires` (variable "x" .==. variable "y")
        let generator =
                LTA.oneof [LTA.node "pair" constraint forest, LTA.leaf (-1, -1) "sentinel" true]
        complete <- LTA.compile solver generator
        relational <- LTA.compileRelational solver generator
        pure (fmap LTA.cardinality complete, fmap LTA.cardinality relational)
