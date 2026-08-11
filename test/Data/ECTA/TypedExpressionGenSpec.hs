module Data.ECTA.TypedExpressionGenSpec (spec) where

import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Ratio ((%))
import Test.Hspec (Expectation, Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import qualified Test.QuickCheck as QC

import Data.ECTA (Node, edgeChildren, getAllTerms, nodeEdges)
import Data.ECTA.Gen.QuickCheck (ECTAGen, KeyedECTAGen)
import qualified Data.ECTA.Gen.QuickCheck as ECTAGen
import Data.ECTA.Internal.ECTA.Type (edgeEcs)
import Data.ECTA.Paths (unsafeGetEclasses)

-- | The ground types in the expression language.
data Type = TInt | TBool | TChar
    deriving (Eq, Ord, Show)

{- | Polymorphic functions available to generated expressions.

'Const' and 'FlipConst' are parametric in both argument types. 'Equal'
represents the constrained type @forall a. Eq a => a -> a -> Bool@.
'Add' and 'Multiply' operate on 'TInt'; 'Or' and 'And' operate on 'TBool'.
-}
data Function
    = Const
    | FlipConst
    | Equal
    | Add
    | Multiply
    | Or
    | And
    deriving (Eq, Ord, Show)

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

-- | An independently selected function instance and two arguments.
data Candidate = Candidate !BinaryFunctionInstance !TypedExpression !TypedExpression
    deriving (Show)

-- | All ground types used to instantiate polymorphic functions.
allTypes :: [Type]
allTypes = [TInt, TBool, TChar]

-- | Every binary ground instance, including the polymorphic schemes.
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

-- | Two literal expressions of each ground type.
atoms :: [TypedExpression]
atoms =
    [ TypedExpression TInt (IntLiteral 0)
    , TypedExpression TInt (IntLiteral 1)
    , TypedExpression TBool (BoolLiteral False)
    , TypedExpression TBool (BoolLiteral True)
    , TypedExpression TChar (CharLiteral 'a')
    , TypedExpression TChar (CharLiteral 'z')
    ]

-- | The argument and result types retained for one function partition.
type FunctionSignature = (Type, Type, Type)

-- | Extract the retained signature of one ground function instance.
functionSignature :: BinaryFunctionInstance -> FunctionSignature
functionSignature instance_ =
    ( firstArgumentType instance_
    , secondArgumentType instance_
    , binaryResultType instance_
    )

-- | Uniform function instances partitioned by complete ground signature.
functionsBySignature :: KeyedECTAGen FunctionSignature BinaryFunctionInstance
functionsBySignature =
    ECTAGen.keyedElements functionSignature binaryFunctionInstances

-- | Uniform literals partitioned by their ground type.
atomsByType :: KeyedECTAGen Type TypedExpression
atomsByType = ECTAGen.keyedElements expressionType atoms

{- | Generate a well-typed binary application over one child language.

One three-way join constrains both argument types against the selected function
instance.
-}
applicationGen :: KeyedECTAGen Type TypedExpression -> KeyedECTAGen Type TypedExpression
applicationGen children =
    ECTAGen.mapKeyed (compileCandidate . toBinaryCandidate) $
        ECTAGen.innerJoin3Keyed
            id
            functionsBySignature
            children
            children
  where
    toBinaryCandidate (instance_, first, second) =
        Candidate instance_ first second

-- | Literal expressions, partitioned by type.
depthZeroByType :: KeyedECTAGen Type TypedExpression
depthZeroByType = atomsByType

-- | Function applications over literals, partitioned by result type.
depthOneByType :: KeyedECTAGen Type TypedExpression
depthOneByType = applicationGen depthZeroByType

-- | Function applications over depth-one children, partitioned by result type.
depthTwoByType :: KeyedECTAGen Type TypedExpression
depthTwoByType = applicationGen depthOneByType

-- | Function applications over depth-two children, partitioned by result type.
depthThreeByType :: KeyedECTAGen Type TypedExpression
depthThreeByType = applicationGen depthTwoByType

-- | Function applications over depth-three children, partitioned by result type.
depthFourByType :: KeyedECTAGen Type TypedExpression
depthFourByType = applicationGen depthThreeByType

-- | Function applications over literals.
depthOneExpressionGen :: ECTAGen TypedExpression
depthOneExpressionGen = ECTAGen.forgetKey depthOneByType

-- | Function applications whose children are depth-one applications.
depthTwoExpressionGen :: ECTAGen TypedExpression
depthTwoExpressionGen = ECTAGen.forgetKey depthTwoByType

-- | Exact-depth-three applications as an ordinary generator.
depthThreeExpressionGen :: ECTAGen TypedExpression
depthThreeExpressionGen = ECTAGen.forgetKey depthThreeByType

-- | Exact-depth-four applications as an ordinary generator.
depthFourExpressionGen :: ECTAGen TypedExpression
depthFourExpressionGen = ECTAGen.forgetKey depthFourByType

-- | The complete independent candidate space over one child language.
allCandidatesFor :: [TypedExpression] -> [Candidate]
allCandidatesFor children =
    [ Candidate instance_ first second
    | instance_ <- binaryFunctionInstances
    , first <- children
    , second <- children
    ]

-- | The exact accepted expression language over one child language.
acceptedExpressionsFor :: [TypedExpression] -> [TypedExpression]
acceptedExpressionsFor =
    sort
        . map compileCandidate
        . filter candidateMatches
        . allCandidatesFor

-- | Exact depth-one expression language.
depthOneExpressions :: [TypedExpression]
depthOneExpressions = acceptedExpressionsFor atoms

-- | Exact depth-two expression language.
depthTwoExpressions :: [TypedExpression]
depthTwoExpressions = acceptedExpressionsFor depthOneExpressions

-- | Check whether both argument types match a function instantiation.
candidateMatches :: Candidate -> Bool
candidateMatches (Candidate instance_ first second) =
    firstArgumentType instance_ == expressionType first
        && secondArgumentType instance_ == expressionType second

-- | Erase the ground instantiation after constructing a typed expression.
compileCandidate :: Candidate -> TypedExpression
compileCandidate (Candidate instance_ first second) =
    TypedExpression
        (binaryResultType instance_)
        (ApplyBinary (binaryFunction instance_) (expression first) (expression second))

-- | Generate the independent candidate space over one child generator.
quickCheckCandidateGen :: QC.Gen TypedExpression -> QC.Gen Candidate
quickCheckCandidateGen childGen =
    Candidate
        <$> QC.elements binaryFunctionInstances
        <*> childGen
        <*> childGen

-- | Generate one application layer using QuickCheck rejection sampling.
quickCheckApplicationGen :: QC.Gen TypedExpression -> QC.Gen TypedExpression
quickCheckApplicationGen childGen =
    compileCandidate
        <$> (quickCheckCandidateGen childGen `QC.suchThat` candidateMatches)

-- | QuickCheck literals, with no rejection.
quickCheckDepthZeroGen :: QC.Gen TypedExpression
quickCheckDepthZeroGen = QC.elements atoms

-- | QuickCheck applications over literals.
quickCheckDepthOneGen :: QC.Gen TypedExpression
quickCheckDepthOneGen = quickCheckApplicationGen quickCheckDepthZeroGen

-- | QuickCheck applications over depth-one applications.
quickCheckDepthTwoGen :: QC.Gen TypedExpression
quickCheckDepthTwoGen = quickCheckApplicationGen quickCheckDepthOneGen

-- | Infer the type of an expression, rejecting ill-typed equality.
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
        Add -> homogeneousBinary TInt firstType secondType
        Multiply -> homogeneousBinary TInt firstType secondType
        Or -> homogeneousBinary TBool firstType secondType
        And -> homogeneousBinary TBool firstType secondType
  where
    homogeneousBinary expected firstType secondType
        | firstType == expected && secondType == expected = Just expected
        | otherwise = Nothing

-- | Check the generated type annotation against independent inference.
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

-- | Check an ECTA generator against an exact, uniformly weighted language.
shouldMatchExactLanguage ::
    ECTAGen TypedExpression ->
    [TypedExpression] ->
    Expectation
shouldMatchExactLanguage generator expected =
    case ECTAGen.pmf generator of
        Left err -> expectationFailure $ show err
        Right outcomes -> do
            map fst outcomes `shouldBe` expected
            map snd outcomes
                `shouldBe` replicate
                    (length expected)
                    (1 % toInteger (length expected))

-- | Compare ECTA conditioning with ordinary QuickCheck rejection sampling.
spec :: Spec
spec =
    describe "typed expression generation" $ do
        it "matches the exact depth-one language accepted by rejection sampling" $
            shouldMatchExactLanguage depthOneExpressionGen depthOneExpressions

        it "matches the exact 29,456-expression depth-two language" $ do
            length depthTwoExpressions `shouldBe` 29456
            shouldMatchExactLanguage depthTwoExpressionGen depthTwoExpressions
            case ECTAGen.support depthTwoExpressionGen of
                Left err -> expectationFailure $ show err
                Right node -> length (getAllTerms node) `shouldBe` 29456

        it "represents both argument constraints in one ECTA edge" $
            case ECTAGen.support depthOneExpressionGen of
                Right node -> hasTwoArgumentConstraints node `shouldBe` True
                Left err -> expectationFailure $ show err

        it "counts the exact depth-three language without enumerating it" $
            ECTAGen.cardinality depthThreeExpressionGen
                `shouldBe` Right 2760555776

        it "constructs the exact depth-four language from compact partitions" $
            ECTAGen.cardinality depthFourExpressionGen
                `shouldBe` Right 26679325111164403712

        it "retains the exact depth-four result-type partitions" $ do
            let intCount = 4356154180428103680
                boolCount = 20761924256729464832
                boundaries =
                    [ (0, TInt)
                    , (intCount - 1, TInt)
                    , (intCount, TBool)
                    , (intCount + boolCount - 1, TBool)
                    , (intCount + boolCount, TChar)
                    , (26679325111164403712 - 1, TChar)
                    ]
            traverse
                (\(rank, _) -> expressionType <$> ECTAGen.unrank depthFourExpressionGen rank)
                boundaries
                `shouldBe` Right (map snd boundaries)

        it "unranks representative depth-four expressions" $ do
            let total = 26679325111164403712
            traverse
                (ECTAGen.unrank depthFourExpressionGen)
                [0, total `div` 2, total - 1]
                `shouldSatisfy` either (const False) (all isWellTyped)

        it "counts exact depth-one coverage by result type" $
            ECTAGen.countBy expressionType depthOneExpressionGen
                `shouldBe` Right
                    ( Map.fromList
                        [ (TInt, 32)
                        , (TBool, 44)
                        , (TChar, 24)
                        ]
                    )

        it "accepts only one ninth of the independent QuickCheck candidates" $
            ( toInteger (length depthOneExpressions)
                % toInteger (length $ allCandidatesFor atoms)
            )
                `shouldBe` 1 % 9

        it "samples only well-typed depth-two expressions through ECTA" $
            QC.property $
                QC.forAll (ECTAGen.toGen depthTwoExpressionGen) $ \typed ->
                    QC.counterexample (show typed) $ QC.property $ isWellTyped typed

        it "samples only well-typed depth-four expressions through ECTA" $
            QC.property $
                QC.forAll (ECTAGen.toGen depthFourExpressionGen) $ \typed ->
                    QC.counterexample (show typed) $ QC.property $ isWellTyped typed

        it "samples well-typed depth-two expressions through nested QuickCheck rejection" $
            QC.property $
                QC.forAll quickCheckDepthTwoGen $ \typed ->
                    QC.counterexample (show typed) $ QC.property $ isWellTyped typed
