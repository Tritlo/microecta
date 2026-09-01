{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE QualifiedDo #-}

{- | A small well-typed expression language, shared by the specs and the
sampling benchmark.

Expressions use unary, binary, and ternary applications over integer and
Boolean literals. Every layer is grouped by result type, so an application
matches each operation signature with child groups of the right types instead
of generating values and rejecting ill-typed combinations. The handwritten
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
    UnarySignature,
    BinarySignature,
    ConditionalSignature,
    allTypes,
    binaryFunctionInstances,
    literals,
    unarySignature,
    binarySignature,
    conditionalSignature,
    compileNot,
    compileBinary,
    compileConditional,

    -- * Generators
    unaryFunctionsBySignature,
    binaryFunctionsBySignature,
    conditionalFunctionsBySignature,
    literalsByType,
    unaryLayer,
    binaryLayer,
    conditionalLayer,
    applicationLayer,
    weighted,
    depthByType,
    expressionGenAtDepth,
    upToDepthByType,
    recursiveExpressions,

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
data Type = TInt | TBool
    deriving (Bounded, Enum, Eq, Ord, Show)

-- | Polymorphic and monomorphic binary functions available to expressions.
data Function
    = Equal
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
    | Not !Expression
    | ApplyBinary !Function !Expression !Expression
    | IfExpression !Expression !Expression !Expression
    deriving (Eq, Ord, Show)

-- | An expression paired with its inferred ground type.
data TypedExpression = TypedExpression
    { expressionType :: !Type
    , expression :: !Expression
    }
    deriving (Eq, Ord, Show)

-- | The dependency information needed to apply 'Not'.
type UnarySignature = ECTAGen.Sig '[Type] Type

{- | The dependency information needed to apply one binary function.

The first two types select child result-type groups whose paths are equated; the
third is retained as the completed application's result-type key.
-}
type BinarySignature = ECTAGen.Sig '[Type, Type] Type

-- | The dependency information needed to build an 'IfExpression'.
type ConditionalSignature = ECTAGen.Sig '[Type, Type, Type] Type

-- | All ground types.
allTypes :: [Type]
allTypes = [minBound .. maxBound]

-- | Every valid ground instantiation of the available functions.
binaryFunctionInstances :: [BinaryFunctionInstance]
binaryFunctionInstances =
    [ BinaryFunctionInstance Equal argument argument TBool
    | argument <- allTypes
    ]
        <> [ BinaryFunctionInstance function_ TInt TInt TInt
           | function_ <- [Add, Multiply]
           ]
        <> [ BinaryFunctionInstance function_ TBool TBool TBool
           | function_ <- [Or, And]
           ]

-- | Two literals of each ground type.
literals :: [TypedExpression]
literals =
    [ TypedExpression TInt (IntLiteral 0)
    , TypedExpression TInt (IntLiteral 1)
    , TypedExpression TBool (BoolLiteral False)
    , TypedExpression TBool (BoolLiteral True)
    ]

-- | The complete ground signature of 'Not'.
unarySignature :: UnarySignature
unarySignature = TBool :-> TBool

-- | Extract the complete ground signature of a function instance.
binarySignature :: BinaryFunctionInstance -> BinarySignature
binarySignature instance_ =
    firstArgumentType instance_
        :* secondArgumentType instance_
        :-> binaryResultType instance_

-- | The ground signature of one conditional result type.
conditionalSignature :: Type -> ConditionalSignature
conditionalSignature result =
    TBool :* result :* result :-> result

-- | Build one well-typed unary expression.
compileNot :: TypedExpression -> TypedExpression
compileNot value =
    TypedExpression TBool $ Not $ expression value

-- | Build one well-typed ternary conditional expression.
compileConditional ::
    Type -> TypedExpression -> TypedExpression -> TypedExpression -> TypedExpression
compileConditional result condition ifTrue ifFalse =
    TypedExpression result $
        IfExpression
            (expression condition)
            (expression ifTrue)
            (expression ifFalse)

-- | The unary operation grouped by its ground signature.
unaryFunctionsBySignature ::
    Grouped UnarySignature (TypedExpression -> TypedExpression)
unaryFunctionsBySignature =
    compileNot
        <$ ECTAGen.keyed unarySignature (ECTAGen.elements [()])

{- | Function instances grouped by their complete ground signature.

A 'Grouped' does not generate the signature as part of its result. The
projected signature classifies functions into groups; matching key values tell
joins which groups should receive equal internal labels on constrained ECTA
paths. Conceptually, this is a compact map from each signature to the sublanguage
of functions having that signature.
-}
binaryFunctionsBySignature :: Grouped BinarySignature BinaryFunctionInstance
binaryFunctionsBySignature =
    ECTAGen.groupBy binarySignature (ECTAGen.elements binaryFunctionInstances)

-- | One conditional builder per possible branch and result type.
conditionalFunctionsBySignature ::
    Grouped
        ConditionalSignature
        (TypedExpression -> TypedExpression -> TypedExpression -> TypedExpression)
conditionalFunctionsBySignature =
    compileConditional
        <$> ECTAGen.groupBy conditionalSignature (ECTAGen.elements allTypes)

{- | Literals grouped by their ground type.

Each projected @Type@ classifies literals into a group. Those keys let later
applications match compatible children and equate their ECTA paths without
enumerating or inspecting every expression.
-}
literalsByType :: Grouped Type TypedExpression
literalsByType = ECTAGen.groupBy expressionType (ECTAGen.elements literals)

-- | Add one unary application layer.
unaryLayer :: Grouped Type TypedExpression -> Grouped Type TypedExpression
unaryLayer children = ECTAGen.do
    build <- unaryFunctionsBySignature
    value <- children
    ECTAGen.pure (build value)

-- | Add one binary application layer.
binaryLayer :: Grouped Type TypedExpression -> Grouped Type TypedExpression
binaryLayer children = ECTAGen.do
    operation <- binaryFunctionsBySignature
    left <- children
    right <- children
    ECTAGen.pure (compileBinary operation left right)

-- | Add one ternary conditional layer.
conditionalLayer :: Grouped Type TypedExpression -> Grouped Type TypedExpression
conditionalLayer children = ECTAGen.do
    build <- conditionalFunctionsBySignature
    condition <- children
    ifTrue <- children
    ifFalse <- children
    ECTAGen.pure (build condition ifTrue ifFalse)

{- | Add one application layer and retain its result type for the next layer.

The three qualified do-blocks build one 'ECTAGen.apply' join apiece. Their
signatures carry one, two, or three argument keys. Each join matches those keys
with the corresponding child result-type groups and retains the operation's
result key. Finite branches are weighted by their cardinalities, so every
expression in the combined exact-depth language remains equally likely. A
recursive family uses equal structural alternatives instead.

Keeping the result group is what lets the operation compose recursively at the
next depth.
-}
applicationLayer :: Grouped Type TypedExpression -> Grouped Type TypedExpression
applicationLayer children =
    weighted
        [ unaryLayer children
        , binaryLayer children
        , conditionalLayer children
        ]

{- | Choose among grouped alternatives weighted by their exact cardinalities,
so every member of the combined language is equally likely.

An alternative that contributes nothing is dropped rather than failing the
whole choice: one whose construction is 'ECTAGen.EmptyGenerator', and one
whose groups are all empty, which 'ECTAGen.frequencies' would otherwise
reject as a zero weight. A recursive family has no cardinality to weight by,
so the whole choice becomes 'ECTAGen.oneofGrouped' — the equal structural
alternatives recursion requires anyway. Any other failure belongs to one
alternative and is reported as it is.
-}
weighted :: (Ord key) => [Grouped key a] -> Grouped key a
weighted alternatives = case traverse liveCardinality alternatives of
    Right counts ->
        ECTAGen.frequencies
            [ (count, alternative)
            | (Just count, alternative) <- zip counts alternatives
            ]
    Left ECTAGen.UnboundedGenerator -> ECTAGen.oneofGrouped alternatives
    Left _ -> ECTAGen.oneofGrouped alternatives
  where
    liveCardinality alternative = case ECTAGen.sizes alternative of
        Left ECTAGen.EmptyGenerator -> Right Nothing
        Left err -> Left err
        Right groups
            | total <- sum groups -> Right $ if total > 0 then Just total else Nothing

{- | Exact-depth expressions grouped by result type.

Retaining the result-type classification at every layer is the crucial
difference from an ordinary 'ECTAGen': each completed language can immediately
serve as both typed child inputs to the following application layer, where
matching result-type groups have their paths equated.
-}
depthByType :: Int -> Grouped Type TypedExpression
depthByType 0 = literalsByType
depthByType depth
    | depth > 0 = applicationLayer $ depthByType $ depth - 1
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

'ECTAGen.frequencies' merges the literal layer and the application layer group
by group. Weighting the two alternatives by their exact expression counts
makes every expression of every admitted depth equally likely, so the whole
bounded language is uniform.
-}
upToDepthByType :: Int -> Grouped Type TypedExpression
upToDepthByType 0 = literalsByType
upToDepthByType depth =
    ECTAGen.frequencies
        [ (literalCount, literalsByType)
        , (upToDepthCount depth - literalCount, applicationLayer $ upToDepthByType $ depth - 1)
        ]
  where
    literalCount = sum $ map (expressionCount 0) allTypes

{- | Every well-typed expression, as one recursive family.

The same application forms as 'upToDepthByType', but referring to themselves
instead of to a hand-unrolled tower: no depth bound, no hand-computed weights,
and members counted by size rather than by depth. Both result types share one
recursive automaton whose cycle carries the application layers' equality
constraints.
-}
recursiveExpressions :: Grouped Type TypedExpression
recursiveExpressions = ECTAGen.recurGrouped $ \self ->
    ECTAGen.oneofGrouped [literalsByType, applicationLayer self]

-- | Erase the ground instantiation after constructing a typed expression.
compileBinary ::
    BinaryFunctionInstance -> TypedExpression -> TypedExpression -> TypedExpression
compileBinary instance_ first second =
    TypedExpression
        (binaryResultType instance_)
        (ApplyBinary (binaryFunction instance_) (expression first) (expression second))

-- | Number of exact-depth expressions with the requested result type.
expressionCount :: Int -> Type -> Integer
expressionCount 0 result =
    toInteger $ length $ filter ((== result) . expressionType) literals
expressionCount depth result =
    applicationCount (expressionCount childDepth) result
  where
    childDepth = depth - 1

-- | Number of expressions of depth at most the bound with the result type.
expressionCountUpTo :: Int -> Type -> Integer
expressionCountUpTo 0 result = expressionCount 0 result
expressionCountUpTo depth result =
    expressionCount 0 result
        + applicationCount (expressionCountUpTo childDepth) result
  where
    childDepth = depth - 1

-- | Count every unary, binary, and conditional application for one result.
applicationCount :: (Type -> Integer) -> Type -> Integer
applicationCount childCount result =
    notCount + binaryCount + conditionalCount
  where
    notCount
        | result == TBool = childCount TBool
        | otherwise = 0
    binaryCount =
        sum
            [ childCount (firstArgumentType instance_)
                * childCount (secondArgumentType instance_)
            | instance_ <- binaryFunctionInstances
            , binaryResultType instance_ == result
            ]
    conditionalCount =
        childCount TBool * childCount result * childCount result

-- | Number of expressions of depth at most the bound across all result types.
upToDepthCount :: Int -> Integer
upToDepthCount depth = sum $ map (expressionCountUpTo depth) allTypes

{- | The handwritten generator makes the dependency explicit by accepting the
desired result type and selecting only compatible function instances. Its
weights make every expression of a given exact depth equally likely.
-}
handwrittenExpressionOfType :: Int -> Type -> QC.Gen TypedExpression
handwrittenExpressionOfType 0 result =
    QC.elements $ filter ((== result) . expressionType) literals
handwrittenExpressionOfType depth result =
    frequencyInteger $ notAlternatives <> binaryAlternatives <> conditionalAlternatives
  where
    childDepth = depth - 1
    count = expressionCount childDepth
    notAlternatives =
        [ ( count TBool
          , compileNot <$> handwrittenExpressionOfType childDepth TBool
          )
        | result == TBool
        ]
    binaryAlternatives =
        [ ( count (firstArgumentType instance_)
                * count (secondArgumentType instance_)
          , do
                first <-
                    handwrittenExpressionOfType
                        childDepth
                        (firstArgumentType instance_)
                second <-
                    handwrittenExpressionOfType
                        childDepth
                        (secondArgumentType instance_)
                pure $ compileBinary instance_ first second
          )
        | instance_ <- binaryFunctionInstances
        , binaryResultType instance_ == result
        ]
    conditionalAlternatives =
        [
            ( count TBool * count result * count result
            , do
                condition <- handwrittenExpressionOfType childDepth TBool
                ifTrue <- handwrittenExpressionOfType childDepth result
                ifFalse <- handwrittenExpressionOfType childDepth result
                pure $ compileConditional result condition ifTrue ifFalse
            )
        ]

-- | Generate uniformly from all well-typed expressions at one exact depth.
handwrittenExpressionGen :: Int -> QC.Gen TypedExpression
handwrittenExpressionGen depth =
    frequencyInteger
        [ (expressionCount depth result, handwrittenExpressionOfType depth result)
        | result <- allTypes
        ]

-- | Preserve exact relative weights, using an Integer draw when needed.
frequencyInteger :: [(Integer, QC.Gen a)] -> QC.Gen a
frequencyInteger [] = error "frequencyInteger: empty alternatives"
frequencyInteger alternatives
    | totalWeight <= toInteger (maxBound :: Int) =
        QC.frequency
            [ (fromInteger weight, generator)
            | (weight, generator) <- reduced
            ]
    | otherwise = do
        selected <- QC.chooseInteger (1, totalWeight)
        pick selected reduced
  where
    commonFactor = foldl' gcd 0 $ map fst alternatives
    reduced = [(weight `div` commonFactor, generator) | (weight, generator) <- alternatives]
    totalWeight = sum $ map fst reduced

    pick _ [] = error "frequencyInteger: selected past the alternatives"
    pick selected ((weight, generator) : remaining)
        | selected <= weight = generator
        | otherwise = pick (selected - weight) remaining
