{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE QualifiedDo #-}

{- | A small well-typed expression language, shared by the specs and the
sampling benchmark.

Expressions are binary applications over ground-typed literals. Every layer
is grouped by result type, so an application layer matches each function
signature with the child groups of the right types instead of generating
three values and rejecting ill-typed combinations. The handwritten
QuickCheck generators mirror the same exact distribution and serve as the
comparison baseline.
-}
module Data.ECTA.TypedExpressionLanguage (
    -- * Language
    Type (..),
    Function (..),
    BinaryFunctionInstance (..),
    Expression (..),
    TypedExpression (..),
    FunctionSignature,
    allTypes,
    binaryFunctionInstances,
    atoms,
    functionSignature,
    compileApplication,

    -- * Generators
    functionsBySignature,
    atomsByType,
    applicationGen,
    depthByType,
    expressionGenAtDepth,
    upToDepthByType,

    -- * Exact counts
    expressionCount,
    expressionCountUpTo,
    upToDepthCount,

    -- * Handwritten baseline
    handwrittenExpressionOfType,
    handwrittenExpressionGen,
    frequencyInteger,
) where

import qualified Test.QuickCheck as QC

import Data.ECTA.Gen.QuickCheck (ECTAGen, Grouped, Sig ((:*), (:->)))
import qualified Data.ECTA.Gen.QuickCheck as ECTAGen

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
        :* secondArgumentType instance_
        :-> binaryResultType instance_

{- | Function instances grouped by their complete ground signature.

A 'Grouped' does not generate the signature as part of its result. The
projected signature classifies functions into groups; matching key values tell
joins which groups should receive equal internal labels on constrained ECTA
paths. Conceptually, this is a compact map from each signature to the sublanguage
of functions having that signature.
-}
functionsBySignature :: Grouped FunctionSignature BinaryFunctionInstance
functionsBySignature =
    ECTAGen.groupBy functionSignature (ECTAGen.elements binaryFunctionInstances)

{- | Literals grouped by their ground type.

Each projected @Type@ classifies literals into a group. Those keys let later
applications match compatible children and equate their ECTA paths without
enumerating or inspecting every expression.
-}
atomsByType :: Grouped Type TypedExpression
atomsByType = ECTAGen.groupBy expressionType (ECTAGen.elements atoms)

{- | Add one application layer and retain its result type for the next layer.

The qualified do-block builds exactly one 'ECTAGen.apply' join: the first
bind chooses the operation family and the remaining binds choose its
arguments. Each function signature reads as
@leftArgumentType ':*' rightArgumentType ':->' resultType@. The
join matches the two signature keys with the two child result-type groups,
equates their paths, takes their compact Cartesian product, and retains
@resultType@ as the application's key.
The dependency is therefore enforced structurally rather than by generating
three arbitrary values and rejecting ill-typed combinations.

Keeping the result group is what lets the operation compose recursively at the
next depth.
-}
applicationGen :: Grouped Type TypedExpression -> Grouped Type TypedExpression
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
depthByType :: Int -> Grouped Type TypedExpression
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

{- | Expressions of depth at most the bound, grouped by result type.

'ECTAGen.frequencies' merges the atom layer and the application layer group
by group. Weighting the two alternatives by their exact expression counts
makes every expression of every admitted depth equally likely, so the whole
bounded language is uniform.
-}
upToDepthByType :: Int -> Grouped Type TypedExpression
upToDepthByType 0 = atomsByType
upToDepthByType depth =
    ECTAGen.frequencies
        [ (atomCount, atomsByType)
        , (upToDepthCount depth - atomCount, applicationGen $ upToDepthByType $ depth - 1)
        ]
  where
    atomCount = sum $ map (expressionCount 0) allTypes

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

-- | Number of expressions of depth at most the bound with the result type.
expressionCountUpTo :: Int -> Type -> Integer
expressionCountUpTo 0 result = expressionCount 0 result
expressionCountUpTo depth result =
    expressionCount 0 result
        + sum
            [ expressionCountUpTo childDepth (firstArgumentType instance_)
                * expressionCountUpTo childDepth (secondArgumentType instance_)
            | instance_ <- binaryFunctionInstances
            , binaryResultType instance_ == result
            ]
  where
    childDepth = depth - 1

-- | Number of expressions of depth at most the bound across all result types.
upToDepthCount :: Int -> Integer
upToDepthCount depth = sum $ map (expressionCountUpTo depth) allTypes

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
