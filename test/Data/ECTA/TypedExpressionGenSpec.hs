{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE QualifiedDo #-}

module Data.ECTA.TypedExpressionGenSpec (spec) where

import qualified Data.Map.Strict as Map
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import qualified Test.QuickCheck as QC

import Data.ECTA (Node, edgeChildren, getAllTerms, nodeEdges)
import Data.ECTA.Gen.QuickCheck (ECTAGen, ECTAGenBy, (-->))
import qualified Data.ECTA.Gen.QuickCheck as ECTAGen
import Data.ECTA.Internal.ECTA.Type (edgeEcs)
import Data.ECTA.Paths (unsafeGetEclasses)

-- | Ground types in the expression language.
data Type = TInt | TBool | TChar
    deriving (Bounded, Enum, Eq, Ord, Show)

-- | Polymorphic and monomorphic binary functions available to expressions.
data Function
    = Const
    | FlipConst
    | Equal
    | Add
    | Multiply
    | Or
    | And
    deriving (Bounded, Enum, Eq, Ord, Show)

-- | One ground instantiation of a binary function.
data BinaryFunctionInstance = BinaryFunctionInstance
    { binaryFunction :: !Function
    , firstArgumentType :: !Type
    , secondArgumentType :: !Type
    , binaryResultType :: !Type
    }
    deriving (Eq, Ord, Show)

-- | Untyped expression syntax.
data Expression
    = IntLiteral !Int
    | BoolLiteral !Bool
    | CharLiteral !Char
    | ApplyBinary !Function !Expression !Expression
    deriving (Eq, Ord, Show)

-- | An expression paired with its inferred ground type.
data TypedExpression = TypedExpression
    { expressionType :: !Type
    , expression :: !Expression
    }
    deriving (Eq, Ord, Show)

{- | The dependency information needed to apply one function.

The first two types select child result-type groups whose paths are equated; the
third is retained as the completed application's result-type key.
-}
type FunctionSignature = ECTAGen.Sig '[Type, Type] Type

-- | All ground types.
allTypes :: [Type]
allTypes = [minBound .. maxBound]

-- | Every valid ground instantiation of the available functions.
binaryFunctionInstances :: [BinaryFunctionInstance]
binaryFunctionInstances =
    [ BinaryFunctionInstance Const first second first
    | first <- allTypes
    , second <- allTypes
    ]
        <> [ BinaryFunctionInstance FlipConst first second second
           | first <- allTypes
           , second <- allTypes
           ]
        <> [ BinaryFunctionInstance Equal argument argument TBool
           | argument <- allTypes
           ]
        <> [ BinaryFunctionInstance function_ TInt TInt TInt
           | function_ <- [Add, Multiply]
           ]
        <> [ BinaryFunctionInstance function_ TBool TBool TBool
           | function_ <- [Or, And]
           ]

-- | Two literals of each ground type.
atoms :: [TypedExpression]
atoms =
    [ TypedExpression TInt (IntLiteral 0)
    , TypedExpression TInt (IntLiteral 1)
    , TypedExpression TBool (BoolLiteral False)
    , TypedExpression TBool (BoolLiteral True)
    , TypedExpression TChar (CharLiteral 'a')
    , TypedExpression TChar (CharLiteral 'z')
    ]

-- | Extract the complete ground signature of a function instance.
functionSignature :: BinaryFunctionInstance -> FunctionSignature
functionSignature instance_ =
    firstArgumentType instance_
        --> secondArgumentType instance_
        --> binaryResultType instance_

{- | Function instances grouped by their complete ground signature.

An 'ECTAGenBy' does not generate the signature as part of its result. The
projected signature classifies functions into groups; matching key values tell
joins which groups should receive equal internal labels on constrained ECTA
paths. Conceptually, this is a compact map from each signature to the sublanguage
of functions having that signature.
-}
functionsBySignature :: ECTAGenBy FunctionSignature BinaryFunctionInstance
functionsBySignature =
    ECTAGen.elementsBy functionSignature binaryFunctionInstances

{- | Literals grouped by their ground type.

Each projected @Type@ classifies literals into a group. Those keys let later
applications match compatible children and equate their ECTA paths without
enumerating or inspecting every expression.
-}
atomsByType :: ECTAGenBy Type TypedExpression
atomsByType = ECTAGen.elementsBy expressionType atoms

{- | Add one application layer and retain its result type for the next layer.

The qualified do-block builds exactly one 'ECTAGen.apply' join: the first
bind chooses the operation family and the remaining binds choose its
arguments. Each function signature reads as
@leftArgumentType '-->' rightArgumentType '-->' resultType@. The
join matches the two signature keys with the two child result-type groups,
equates their paths, takes their compact Cartesian product, and retains
@resultType@ as the application's key.
The dependency is therefore enforced structurally rather than by generating
three arbitrary values and rejecting ill-typed combinations.

Keeping the result group is what lets the operation compose recursively at the
next depth.
-}
applicationGen :: ECTAGenBy Type TypedExpression -> ECTAGenBy Type TypedExpression
applicationGen children = ECTAGen.do
    operation <- functionsBySignature
    left <- children
    right <- children
    ECTAGen.pure (compileApplication operation left right)

{- | Exact-depth expressions grouped by result type.

Retaining the result-type classification at every layer is the crucial
difference from an ordinary 'ECTAGen': each completed language can immediately
serve as both typed child inputs to the following application layer, where
matching result-type groups have their paths equated.
-}
depthByType :: Int -> ECTAGenBy Type TypedExpression
depthByType 0 = atomsByType
depthByType depth
    | depth > 0 = applicationGen $ depthByType $ depth - 1
    | otherwise = error $ "negative expression depth: " <> show depth

{- | Return an ordinary ECTA generator after composing the requested depth.

'ECTAGen.ungroup' is the boundary back to the familiar generator interface.
It discards the path-key classification after composition and merges the
result-type groups with their exact probability masses; the generated value is
still only a 'TypedExpression'.
-}
expressionGenAtDepth :: Int -> ECTAGen TypedExpression
expressionGenAtDepth = ECTAGen.ungroup . depthByType

-- | Erase the ground instantiation after constructing a typed expression.
compileApplication ::
    BinaryFunctionInstance -> TypedExpression -> TypedExpression -> TypedExpression
compileApplication instance_ first second =
    TypedExpression
        (binaryResultType instance_)
        (ApplyBinary (binaryFunction instance_) (expression first) (expression second))

-- | Number of exact-depth expressions with the requested result type.
expressionCount :: Int -> Type -> Integer
expressionCount 0 result =
    toInteger $ length $ filter ((== result) . expressionType) atoms
expressionCount depth result =
    sum
        [ expressionCount childDepth (firstArgumentType instance_)
            * expressionCount childDepth (secondArgumentType instance_)
        | instance_ <- binaryFunctionInstances
        , binaryResultType instance_ == result
        ]
  where
    childDepth = depth - 1

{- | The handwritten generator makes the dependency explicit by accepting the
desired result type and selecting only compatible function instances. Its
weights make every expression of a given exact depth equally likely.
-}
handwrittenExpressionOfType :: Int -> Type -> QC.Gen TypedExpression
handwrittenExpressionOfType 0 result =
    QC.elements $ filter ((== result) . expressionType) atoms
handwrittenExpressionOfType depth result =
    frequencyInteger
        [ ( expressionCount childDepth (firstArgumentType instance_)
                * expressionCount childDepth (secondArgumentType instance_)
          , do
                first <-
                    handwrittenExpressionOfType
                        childDepth
                        (firstArgumentType instance_)
                second <-
                    handwrittenExpressionOfType
                        childDepth
                        (secondArgumentType instance_)
                pure $ compileApplication instance_ first second
          )
        | instance_ <- binaryFunctionInstances
        , binaryResultType instance_ == result
        ]
  where
    childDepth = depth - 1

-- | Generate uniformly from all well-typed expressions at one exact depth.
handwrittenExpressionGen :: Int -> QC.Gen TypedExpression
handwrittenExpressionGen depth =
    frequencyInteger
        [ (expressionCount depth result, handwrittenExpressionOfType depth result)
        | result <- allTypes
        ]

-- | Preserve exact relative weights while fitting QuickCheck's Int interface.
frequencyInteger :: [(Integer, QC.Gen a)] -> QC.Gen a
frequencyInteger [] = error "frequencyInteger: empty alternatives"
frequencyInteger alternatives =
    QC.frequency
        [ (fromInteger $ weight `div` commonFactor, generator)
        | (weight, generator) <- alternatives
        ]
  where
    commonFactor = foldl' gcd 0 $ map fst alternatives

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
            ECTAGen.sizeBy (depthByType 4)
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

        it "samples only well-typed depth-four expressions through ECTA" $
            QC.withNumTests 1000 $
                QC.forAll (ECTAGen.toGen $ expressionGenAtDepth 4) $ \typed ->
                    QC.counterexample (show typed) $ QC.property $ isWellTyped typed

        it "samples only well-typed depth-four expressions through handwritten sharing" $
            QC.withNumTests 1000 $
                QC.forAll (handwrittenExpressionGen 4) $ \typed ->
                    QC.counterexample (show typed) $ QC.property $ isWellTyped typed
