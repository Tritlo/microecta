module Data.ECTA.TypedExpressionGenSpec (spec) where

import Data.List (sort)
import Data.Ratio ((%))
import Test.Hspec (Expectation, Spec, describe, expectationFailure, it, shouldBe)
import qualified Test.QuickCheck as QC

import Data.ECTA (getAllTerms)
import Data.ECTA.Gen.QuickCheck (ECTAGen)
import qualified Data.ECTA.Gen.QuickCheck as ECTAGen

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

-- | Uniformly select a binary function instance inside ECTA.
binaryFunctionInstanceGen :: ECTAGen BinaryFunctionInstance
binaryFunctionInstanceGen = ECTAGen.elements binaryFunctionInstances

-- | Uniformly select a typed literal inside ECTA.
atomGen :: ECTAGen TypedExpression
atomGen = ECTAGen.elements atoms

{- | Generate a well-typed binary application over one child language.

The first join constrains the first argument. The second join composes with
that result and constrains the second argument.
-}
applicationGen :: ECTAGen TypedExpression -> ECTAGen TypedExpression
applicationGen childGen =
    compileCandidate . toBinaryCandidate
        <$> ECTAGen.innerJoinOn
            (secondArgumentType . fst)
            expressionType
            withFirstArgument
            childGen
  where
    withFirstArgument =
        ECTAGen.innerJoinOn
            firstArgumentType
            expressionType
            binaryFunctionInstanceGen
            childGen

    toBinaryCandidate ((instance_, first), second) =
        Candidate instance_ first second

-- | Literal expressions, with no function application.
depthZeroExpressionGen :: ECTAGen TypedExpression
depthZeroExpressionGen = atomGen

-- | Function applications over literals.
depthOneExpressionGen :: ECTAGen TypedExpression
depthOneExpressionGen = applicationGen depthZeroExpressionGen

-- | Function applications whose children are depth-one applications.
depthTwoExpressionGen :: ECTAGen TypedExpression
depthTwoExpressionGen = applicationGen depthOneExpressionGen

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

        it "accepts only one ninth of the independent QuickCheck candidates" $
            ( toInteger (length depthOneExpressions)
                % toInteger (length $ allCandidatesFor atoms)
            )
                `shouldBe` 1 % 9

        it "samples only well-typed depth-two expressions through ECTA" $
            QC.property $
                QC.forAll (ECTAGen.toGen depthTwoExpressionGen) $ \typed ->
                    QC.counterexample (show typed) $ QC.property $ isWellTyped typed

        it "samples well-typed depth-two expressions through nested QuickCheck rejection" $
            QC.property $
                QC.forAll quickCheckDepthTwoGen $ \typed ->
                    QC.counterexample (show typed) $ QC.property $ isWellTyped typed
