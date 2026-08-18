module Data.ECTA.TypedExpressionGenSpec (spec) where

import Data.List (isSuffixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import qualified Test.QuickCheck as QC

import Data.ECTA (Node, edgeChildren, getAllTerms, nodeEdges, numNestedMu, unfoldBounded)
import qualified Data.ECTA.Gen.QuickCheck as ECTAGen
import Data.ECTA.Internal.ECTA.Type (edgeEcs)
import Data.ECTA.Paths (unsafeGetEclasses)
import Data.ECTA.TypedExpressionLanguage

-- | Infer a ground type independently of either generator.
inferType :: Expression -> Maybe Type
inferType (IntLiteral _) = Just TInt
inferType (BoolLiteral _) = Just TBool
inferType (Not value) = do
    valueType <- inferType value
    if valueType == TBool then Just TBool else Nothing
inferType (ApplyBinary function_ first second) = do
    firstType <- inferType first
    secondType <- inferType second
    case function_ of
        Const -> Just firstType
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
inferType (IfExpression condition ifTrue ifFalse) = do
    conditionType <- inferType condition
    trueType <- inferType ifTrue
    falseType <- inferType ifFalse
    if conditionType == TBool && trueType == falseType
        then Just trueType
        else Nothing

-- | Number of application layers in an expression.
expressionDepth :: Expression -> Int
expressionDepth (Not value) = 1 + expressionDepth value
expressionDepth (ApplyBinary _ first second) =
    1 + max (expressionDepth first) (expressionDepth second)
expressionDepth (IfExpression condition ifTrue ifFalse) =
    1 + maximum [expressionDepth condition, expressionDepth ifTrue, expressionDepth ifFalse]
expressionDepth _ = 0

-- | Check the generated annotation against independent inference.
isWellTyped :: TypedExpression -> Bool
isWellTyped typed =
    inferType (expression typed) == Just (expressionType typed)

-- | Find a joined edge that retains the requested argument constraints.
hasArgumentConstraints :: Int -> Node -> Bool
hasArgumentConstraints count node = any edgeMatches $ nodeEdges node
  where
    edgeMatches edge =
        length (unsafeGetEclasses $ edgeEcs edge) == count
            || any (hasArgumentConstraints count) (edgeChildren edge)

-- | Independently enumerate the exact-depth reference language.
referenceExpressions :: Int -> Type -> [Expression]
referenceExpressions 0 TInt = [IntLiteral 0, IntLiteral 1]
referenceExpressions 0 TBool = [BoolLiteral False, BoolLiteral True]
referenceExpressions depth TInt =
    [ ApplyBinary Const first second
    | first <- integers
    , second <- integers <> booleans
    ]
        <> [ ApplyBinary function_ first second
           | function_ <- [Add, Multiply]
           , first <- integers
           , second <- integers
           ]
        <> [ IfExpression condition ifTrue ifFalse
           | condition <- booleans
           , ifTrue <- integers
           , ifFalse <- integers
           ]
  where
    integers = referenceExpressions (depth - 1) TInt
    booleans = referenceExpressions (depth - 1) TBool
referenceExpressions depth TBool =
    [Not value | value <- booleans]
        <> [ ApplyBinary Const first second
           | first <- booleans
           , second <- integers <> booleans
           ]
        <> [ ApplyBinary Equal first second
           | values <- [integers, booleans]
           , first <- values
           , second <- values
           ]
        <> [ ApplyBinary function_ first second
           | function_ <- [Or, And]
           , first <- booleans
           , second <- booleans
           ]
        <> [ IfExpression condition ifTrue ifFalse
           | condition <- booleans
           , ifTrue <- booleans
           , ifFalse <- booleans
           ]
  where
    integers = referenceExpressions (depth - 1) TInt
    booleans = referenceExpressions (depth - 1) TBool

-- | Exercise the same generators and invariants as the prototype executable.
spec :: Spec
spec =
    describe "typed expression generation" $ do
        it "matches the independent uniform 67,482-expression depth-two language" $ do
            let depthTwoCount = sum $ map (expressionCount 2) allTypes
                expectedMass = 1 / fromIntegral depthTwoCount
                depthTwoGenerator = expressionGenAtDepth 2
                expectedLanguage =
                    Set.fromList
                        [ TypedExpression result value
                        | result <- allTypes
                        , value <- referenceExpressions 2 result
                        ]
            depthTwoCount `shouldBe` 67482
            case ECTAGen.pmf depthTwoGenerator of
                Left err -> expectationFailure $ show err
                Right outcomes -> do
                    toInteger (length outcomes) `shouldBe` depthTwoCount
                    all ((== expectedMass) . snd) outcomes `shouldBe` True
                    Set.fromList (map fst outcomes) `shouldBe` expectedLanguage
            case ECTAGen.support depthTwoGenerator of
                Left err -> expectationFailure $ show err
                Right node -> length (getAllTerms node) `shouldBe` 67482

        it "represents unary, binary, and ternary dependencies in ECTA edges" $
            case ECTAGen.support (expressionGenAtDepth 1) of
                Right node ->
                    map (`hasArgumentConstraints` node) [1, 2, 3]
                        `shouldBe` [True, True, True]
                Left err -> expectationFailure $ show err

        it "counts the exact depth-three language without enumerating it" $
            ECTAGen.cardinality (expressionGenAtDepth 3)
                `shouldBe` Right 115512218596578

        it "constructs the exact depth-four language from compact groups" $ do
            let depthFourCount = sum $ map (expressionCount 4) allTypes
            depthFourCount
                `shouldBe` 858249006412648850898429671908047368055066
            ECTAGen.cardinality (expressionGenAtDepth 4)
                `shouldBe` Right depthFourCount

        it "retains the exact depth-four result-type groups" $ do
            let intCount = 46024447425199375286078532919911917419200
                boolCount = 812224558987449475612351138988135450635866
                total = intCount + boolCount
                boundaries =
                    [ (0, TInt)
                    , (intCount - 1, TInt)
                    , (intCount, TBool)
                    , (total - 1, TBool)
                    ]
            ECTAGen.sizes (depthByType 4)
                `shouldBe` Right
                    ( Map.fromList
                        [ (TInt, intCount)
                        , (TBool, boolCount)
                        ]
                    )
            traverse
                (\(rank, _) -> expressionType <$> ECTAGen.unrank (expressionGenAtDepth 4) rank)
                boundaries
                `shouldBe` Right (map snd boundaries)

        it "unranks representative depth-four expressions" $ do
            let total = 858249006412648850898429671908047368055066
            traverse
                (ECTAGen.unrank $ expressionGenAtDepth 4)
                [0, total `div` 2, total - 1]
                `shouldSatisfy` either (const False) (all isWellTyped)

        it "counts exact depth-one coverage by result type" $
            ECTAGen.countBy expressionType (expressionGenAtDepth 1)
                `shouldBe` Right
                    ( Map.fromList
                        [ (TInt, 24)
                        , (TBool, 34)
                        ]
                    )

        it "builds the uniform depth-at-most-two language with frequencies" $ do
            let expectedMass = 1 / fromIntegral (upToDepthCount 2)
                generator = ECTAGen.ungroup $ upToDepthByType 2
            upToDepthCount 2 `shouldBe` 80792
            ECTAGen.sizes (upToDepthByType 2)
                `shouldBe` Right
                    ( Map.fromList
                        [ (TInt, 27302)
                        , (TBool, 53490)
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
                    TypedExpression TBool $
                        Not (BoolLiteral False)
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
                containsAdd (Not value) = containsAdd value
                containsAdd (IfExpression condition ifTrue ifFalse) =
                    any containsAdd [condition, ifTrue, ifFalse]
                containsAdd _ = False
                nodes :: Expression -> Int
                nodes (Not value) = 1 + nodes value
                nodes (ApplyBinary _ first second) = 1 + nodes first + nodes second
                nodes (IfExpression condition ifTrue ifFalse) =
                    1 + nodes condition + nodes ifTrue + nodes ifFalse
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

        it "counts the recursive family by structural size" $ do
            let flat = ECTAGen.ungroup recursiveExpressions
            traverse (ECTAGen.countAtSize flat) [1 .. 4]
                `shouldBe` Right
                    [4, 2, 42, 82]
            traverse
                ( \result ->
                    traverse
                        (ECTAGen.countAtSize $ ECTAGen.atKey result recursiveExpressions)
                        [1 .. 4]
                )
                allTypes
                `shouldBe` Right [[2, 0, 16, 12], [2, 2, 26, 70]]

        it "generates exactly the first four finite size classes" $ do
            let bounded = ECTAGen.upToSize 4 $ ECTAGen.ungroup recursiveExpressions
                members generator = case ECTAGen.cardinality generator of
                    Right total ->
                        traverse (ECTAGen.unrank generator) [0 .. total - 1]
                    Left err -> Left err
            ECTAGen.cardinality bounded `shouldBe` Right 130
            members bounded `shouldSatisfy` either (const False) (all isWellTyped)

        it "retains one recursive automaton whose cycle carries the constraints" $
            case ECTAGen.support (ECTAGen.ungroup recursiveExpressions) of
                Left err -> expectationFailure $ show err
                Right node -> do
                    numNestedMu node `shouldBe` 1
                    -- Unfolding the recursion twice admits the atoms and one
                    -- application layer, and nothing ill-typed: 62 members.
                    length (getAllTerms $ unfoldBounded 2 node) `shouldBe` 62

        it "keeps every recursive group at its own result type" $
            traverse
                ( \result ->
                    let bounded = ECTAGen.upToSize 5 $ ECTAGen.atKey result recursiveExpressions
                     in fmap
                            (all (== result))
                            ( traverse
                                (fmap expressionType . ECTAGen.unrank bounded)
                                [0 .. either (const 0) id (ECTAGen.cardinality bounded) - 1]
                            )
                )
                allTypes
                `shouldBe` Right [True, True]

        it "samples only well-typed expressions from the recursive family" $
            QC.withNumTests 500 $
                QC.forAll (QC.resize 7 $ ECTAGen.toGen $ ECTAGen.ungroup recursiveExpressions) $
                    \typed -> QC.counterexample (show typed) $ QC.property $ isWellTyped typed

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
