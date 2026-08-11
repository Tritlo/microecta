module Data.ECTA.TypedExpressionGenSpec (spec) where

import Data.List (isSuffixOf)
import qualified Data.Map.Strict as Map
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import qualified Test.QuickCheck as QC

import Data.ECTA (Node, edgeChildren, getAllTerms, nodeEdges)
import qualified Data.ECTA.Gen.QuickCheck as ECTAGen
import Data.ECTA.Internal.ECTA.Type (edgeEcs)
import Data.ECTA.Paths (unsafeGetEclasses)
import Data.ECTA.TypedExpressionLanguage

-- | Infer a ground type independently of either generator.
inferType :: Expression -> Maybe Type
inferType (IntLiteral _) = Just TInt
inferType (BoolLiteral _) = Just TBool
inferType (CharLiteral _) = Just TChar
inferType (ApplyBinary function_ first second) = do
    firstType <- inferType first
    secondType <- inferType second
    case function_ of
        Const -> Just firstType
        FlipConst -> Just secondType
        Equal
            | firstType == secondType -> Just TBool
            | otherwise -> Nothing
        Add -> homogeneous TInt firstType secondType
        Multiply -> homogeneous TInt firstType secondType
        Or -> homogeneous TBool firstType secondType
        And -> homogeneous TBool firstType secondType
  where
    homogeneous expected firstType secondType
        | firstType == expected && secondType == expected = Just expected
        | otherwise = Nothing

-- | Number of application layers in an expression.
expressionDepth :: Expression -> Int
expressionDepth (ApplyBinary _ first second) =
    1 + max (expressionDepth first) (expressionDepth second)
expressionDepth _ = 0

-- | Check the generated annotation against independent inference.
isWellTyped :: TypedExpression -> Bool
isWellTyped typed =
    inferType (expression typed) == Just (expressionType typed)

-- | Find a joined edge that retains both argument equality constraints.
hasTwoArgumentConstraints :: Node -> Bool
hasTwoArgumentConstraints node = any edgeMatches $ nodeEdges node
  where
    edgeMatches edge =
        length (unsafeGetEclasses $ edgeEcs edge) == 2
            || any hasTwoArgumentConstraints (edgeChildren edge)

-- | Exercise the same generators and invariants as the prototype executable.
spec :: Spec
spec =
    describe "typed expression generation" $ do
        it "matches the exact uniform 29,456-expression depth-two language" $ do
            let depthTwoCount = sum $ map (expressionCount 2) allTypes
                expectedMass = 1 / fromIntegral depthTwoCount
                depthTwoGenerator = expressionGenAtDepth 2
            depthTwoCount `shouldBe` 29456
            case ECTAGen.pmf depthTwoGenerator of
                Left err -> expectationFailure $ show err
                Right outcomes -> do
                    toInteger (length outcomes) `shouldBe` depthTwoCount
                    all ((== expectedMass) . snd) outcomes `shouldBe` True
            case ECTAGen.support depthTwoGenerator of
                Left err -> expectationFailure $ show err
                Right node -> length (getAllTerms node) `shouldBe` 29456

        it "represents both argument constraints in one ECTA edge" $
            case ECTAGen.support (expressionGenAtDepth 1) of
                Right node -> hasTwoArgumentConstraints node `shouldBe` True
                Left err -> expectationFailure $ show err

        it "counts the exact depth-three language without enumerating it" $
            ECTAGen.cardinality (expressionGenAtDepth 3)
                `shouldBe` Right 2760555776

        it "constructs the exact depth-four language from compact groups" $ do
            let depthFourCount = sum $ map (expressionCount 4) allTypes
            depthFourCount `shouldBe` 26679325111164403712
            ECTAGen.cardinality (expressionGenAtDepth 4)
                `shouldBe` Right depthFourCount

        it "retains the exact depth-four result-type groups" $ do
            let intCount = 4356154180428103680
                boolCount = 20761924256729464832
                charCount = 1561246674006835200
                boundaries =
                    [ (0, TInt)
                    , (intCount - 1, TInt)
                    , (intCount, TBool)
                    , (intCount + boolCount - 1, TBool)
                    , (intCount + boolCount, TChar)
                    , (26679325111164403712 - 1, TChar)
                    ]
            ECTAGen.sizes (depthByType 4)
                `shouldBe` Right
                    ( Map.fromList
                        [ (TInt, intCount)
                        , (TBool, boolCount)
                        , (TChar, charCount)
                        ]
                    )
            traverse
                (\(rank, _) -> expressionType <$> ECTAGen.unrank (expressionGenAtDepth 4) rank)
                boundaries
                `shouldBe` Right (map snd boundaries)

        it "unranks representative depth-four expressions" $ do
            let total = 26679325111164403712
            traverse
                (ECTAGen.unrank $ expressionGenAtDepth 4)
                [0, total `div` 2, total - 1]
                `shouldSatisfy` either (const False) (all isWellTyped)

        it "counts exact depth-one coverage by result type" $
            ECTAGen.countBy expressionType (expressionGenAtDepth 1)
                `shouldBe` Right
                    ( Map.fromList
                        [ (TInt, 32)
                        , (TBool, 44)
                        , (TChar, 24)
                        ]
                    )

        it "builds the uniform depth-at-most-two language with frequencies" $ do
            let expectedMass = 1 / fromIntegral (upToDepthCount 2)
                generator = ECTAGen.ungroup $ upToDepthByType 2
            upToDepthCount 2 `shouldBe` 32970
            ECTAGen.sizes (upToDepthByType 2)
                `shouldBe` Right
                    ( Map.fromList
                        [ (TInt, 9522)
                        , (TBool, 17934)
                        , (TChar, 5514)
                        ]
                    )
            case ECTAGen.pmf generator of
                Left err -> expectationFailure $ show err
                Right outcomes -> do
                    toInteger (length outcomes) `shouldBe` upToDepthCount 2
                    all ((== expectedMass) . snd) outcomes `shouldBe` True

        it "counts the depth-at-most-four language without enumerating it" $
            ECTAGen.cardinality (ECTAGen.ungroup $ upToDepthByType 4)
                `shouldBe` Right (upToDepthCount 4)

        it "shrinks any failing expression to the minimal application" $ do
            let generator = ECTAGen.ungroup $ upToDepthByType 2
                minimal =
                    TypedExpression TInt $
                        ApplyBinary Const (IntLiteral 0) (IntLiteral 0)
            result <-
                QC.quickCheckWithResult QC.stdArgs{QC.chatty = False} $
                    QC.withNumTests 300 $
                        ECTAGen.forAll generator $ \typed ->
                            expressionDepth (expression typed) == 0
            case result of
                QC.Failure{QC.failingTestCase = [shown]} ->
                    shown `shouldSatisfy` (show minimal `isSuffixOf`)
                _ -> expectationFailure "expected the depth property to fail"

        it "shrinks to the globally smallest failing member" $ do
            let generator = ECTAGen.ungroup $ upToDepthByType 2
                containsAdd (ApplyBinary function_ first second) =
                    function_ == Add || containsAdd first || containsAdd second
                containsAdd _ = False
                nodes (ApplyBinary _ first second) = 1 + nodes first + nodes second
                nodes _ = 1
                failing typed =
                    containsAdd (expression typed)
                        && expressionDepth (expression typed) >= 2
                minimalFailingNodes = case ECTAGen.pmf generator of
                    Right outcomes ->
                        minimum [nodes (expression typed) | (typed, _) <- outcomes, failing typed]
                    Left err -> error $ show err
            result <-
                QC.quickCheckWithResult QC.stdArgs{QC.chatty = False} $
                    QC.withNumTests 500 $
                        ECTAGen.forAll generator $ \typed ->
                            not (failing typed)
            case result of
                QC.Failure{QC.failingTestCase = [shown]} -> do
                    let rank = read (takeWhile (/= ':') (drop 5 shown)) :: Integer
                    case ECTAGen.unrank generator rank of
                        Right shrunk -> do
                            failing shrunk `shouldBe` True
                            nodes (expression shrunk) `shouldBe` minimalFailingNodes
                        Left err -> expectationFailure $ show err
                _ -> expectationFailure "expected the property to fail"

        it "samples only well-typed depth-at-most-four expressions" $
            QC.withNumTests 1000 $
                QC.forAll (ECTAGen.toGen $ ECTAGen.ungroup $ upToDepthByType 4) $ \typed ->
                    QC.counterexample (show typed) $ QC.property $ isWellTyped typed

        it "samples only well-typed depth-four expressions through ECTA" $
            QC.withNumTests 1000 $
                QC.forAll (ECTAGen.toGen $ expressionGenAtDepth 4) $ \typed ->
                    QC.counterexample (show typed) $ QC.property $ isWellTyped typed

        it "samples only well-typed depth-four expressions through handwritten sharing" $
            QC.withNumTests 1000 $
                QC.forAll (handwrittenExpressionGen 4) $ \typed ->
                    QC.counterexample (show typed) $ QC.property $ isWellTyped typed
