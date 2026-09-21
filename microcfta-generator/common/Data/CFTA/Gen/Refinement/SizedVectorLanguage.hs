{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}

{- | Solver-checked generation of sized-vector pipelines.

This example continues the repository's progression from untyped FTA
expressions and simply typed ECTA expressions to dependent result types. The
length of each vector expression is a refinement carried by its root:

@append xs ys@ has length @length xs + length ys@.
@take k xs@ requires @0 <= k <= length xs@ and has length @k@.
@zipWith (+) xs ys@ requires equal input lengths and preserves that length.

The final generated program indexes a pipeline only after Z3 proves the index
is in bounds. 'runProgram' is deliberately partial; it is total for every
member of 'safeProgramsAtDepth'.
-}
module Data.CFTA.Gen.Refinement.SizedVectorLanguage (
    VectorExpression (..),
    SizedVector (..),
    Program (..),
    solverDeclarationsAtDepth,
    sourceVectors,
    vectorsAtDepth,
    safeProgramsAtDepth,
    evaluateVector,
    vectorLengthIsCorrect,
    runProgram,
    programIsSafe,
) where

import Data.String (fromString)
import qualified Language.Fixpoint.Types as Fixpoint

import Data.CFTA.Gen.Refinement.ExampleSupport (nonNegative)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Refinement (LiquidSymbol (LiquidSymbol), Refinement)
import Data.CFTA.Refinement.Expression (value, variable, (.+.), (.<.), (.<=.), (.==.), (.>=.))
import Data.CFTA.Refinement.Guard (
    Position,
    allOf,
    descendant,
    isSubtypeOf,
    unconstrained,
    withActualFor,
    withActualsFor,
 )

-- | Pure syntax for a small sized-vector pipeline.
data VectorExpression
    = Source !String ![Int]
    | Append !VectorExpression !VectorExpression
    | Take !Int !VectorExpression
    | ZipWithAdd !VectorExpression !VectorExpression
    deriving (Eq, Ord, Show)

-- | A vector expression paired with its proven result-length refinement.
data SizedVector = SizedVector
    { vectorExpression :: !VectorExpression
    , vectorLength :: !Refinement
    }
    deriving (Eq, Show)

-- | A partial indexing operation over a generated pipeline.
data Program = Index !VectorExpression !Int
    deriving (Eq, Ord, Show)

-- | Integer names that occur in the dependent contracts at one depth.
solverDeclarationsAtDepth :: Int -> [(Fixpoint.Symbol, Fixpoint.Sort)]
solverDeclarationsAtDepth requestedDepth =
    [ (Fixpoint.symbol name, Fixpoint.FInt)
    | name <-
        ["v", "n", "m", "k", "i"]
            <> map numberName [-1 .. maximumLength]
    ]
  where
    maximumLength = maximumLengthAtDepth requestedDepth

-- | Three ordinary vector inputs with distinct lengths.
sourceVectors :: LTAGen.LTAGen SizedVector
sourceVectors =
    LTAGen.oneof
        [ sized "empty" []
        , sized "pair" [10, 11]
        , sized "triple" [20, 21, 22]
        ]
  where
    sized name elements =
        let refinement = exact $ length elements
         in LTAGen.refinedNode (fromString name) refinement unconstrained $ LTAGen.do
                _length <- numberLeaf $ length elements
                LTAGen.pure $ SizedVector (Source name elements) refinement

{- | Generate exact-depth vector pipelines.

The surface definition is independent of result lengths. Each constructor
proposes a finite result refinement, and its adjacent liquid guard retains
exactly the result compatible with the selected children.
-}
vectorsAtDepth :: Int -> LTAGen.LTAGen SizedVector
vectorsAtDepth requestedDepth
    | requestedDepth <= 0 = sourceVectors
    | otherwise = vectorLayer depth $ vectorsAtDepth (depth - 1)
  where
    depth = max 0 requestedDepth

-- | Add one dependent vector-operation layer.
vectorLayer :: Int -> LTAGen.LTAGen SizedVector -> LTAGen.LTAGen SizedVector
vectorLayer depth children =
    LTAGen.oneof
        [ appendedVectors maximumLength children
        , takenVectors maximumLength children
        , zippedVectors maximumLength children
        ]
  where
    maximumLength = maximumLengthAtDepth depth

-- | Generate append nodes whose result length is proved to be @n + m@.
appendedVectors :: Int -> LTAGen.LTAGen SizedVector -> LTAGen.LTAGen SizedVector
appendedVectors maximumLength children =
    LTAGen.refinedNodeByRoots "append" resultRefinement validAppend $ LTAGen.do
        result <- possibleLengths maximumLength
        _function <- appendFunction
        left <- children
        right <- children
        LTAGen.pure $
            SizedVector
                (Append (vectorExpression left) (vectorExpression right))
                (numberRefinement result)
  where
    validAppend result function left right =
        withActualsFor
            [ (vectorLengthAt left, appendLeftFormalAt function)
            , (vectorLengthAt right, appendRightFormalAt function)
            ]
            (appendResultAt function `isSubtypeOf` result)

-- | The reusable two-input append contract.
appendFunction :: LTAGen.LTAGen ()
appendFunction = LTAGen.node "append-function" unconstrained $ LTAGen.do
    _leftLength <- LTAGen.leaf () "n" nonNegative
    _rightLength <- LTAGen.leaf () "m" nonNegative
    _resultLength <- LTAGen.leaf () "sum" (value .==. (variable "n" .+. variable "m"))
    LTAGen.pure ()

-- | Generate @take@ nodes with @0 <= k <= n@ and result length @k@.
takenVectors :: Int -> LTAGen.LTAGen SizedVector -> LTAGen.LTAGen SizedVector
takenVectors maximumLength children =
    LTAGen.refinedNodeByRoots "take" resultRefinement validTake $ LTAGen.do
        result <- possibleLengths maximumLength
        _function <- takeFunction
        count <- possibleLengths maximumLength
        input <- children
        LTAGen.pure $
            SizedVector
                (Take (numberValue count) $ vectorExpression input)
                (numberRefinement result)
  where
    validTake result function count input =
        withActualFor count (takeCountFormalAt function) $
            allOf
                [ vectorLengthAt input `isSubtypeOf` function
                , takeResultAt function `isSubtypeOf` result
                ]

-- | A function accepting vectors at least as long as @k@ and returning @k@.
takeFunction :: LTAGen.LTAGen ()
takeFunction =
    LTAGen.refinedNode "take-function" takeInput unconstrained $ LTAGen.do
        _count <- LTAGen.leaf () "k" nonNegative
        _result <- LTAGen.leaf () "take-result" (value .==. variable "k")
        LTAGen.pure ()
  where
    takeInput =
        Fixpoint.pAnd
            [ variable "k" .>=. (0 :: Int)
            , variable "k" .<=. value
            ]

-- | Generate equal-length element-wise additions.
zippedVectors :: Int -> LTAGen.LTAGen SizedVector -> LTAGen.LTAGen SizedVector
zippedVectors maximumLength children =
    LTAGen.refinedNodeByRoots "zip-with-add" resultRefinement validZip $ LTAGen.do
        result <- possibleLengths maximumLength
        _function <- zipFunction
        left <- children
        right <- children
        LTAGen.pure $
            SizedVector
                (ZipWithAdd (vectorExpression left) (vectorExpression right))
                (numberRefinement result)
  where
    validZip result function left right =
        withActualFor (vectorLengthAt left) (zipLeftFormalAt function) $
            allOf
                [ vectorLengthAt right `isSubtypeOf` function
                , zipResultAt function `isSubtypeOf` result
                ]

-- | Retain the selected result annotation without inspecting a vector value.
resultRefinement :: [LiquidSymbol] -> Refinement
resultRefinement (LiquidSymbol _ refinement : _) = refinement
resultRefinement [] = error "resultRefinement: missing result annotation"

-- | A function requiring a second vector of length @n@ and returning @n@.
zipFunction :: LTAGen.LTAGen ()
zipFunction =
    LTAGen.refinedNode "zip-function" (value .==. variable "n") unconstrained $ LTAGen.do
        _leftLength <- LTAGen.leaf () "n" nonNegative
        _result <- LTAGen.leaf () "zip-result" (value .==. variable "n")
        LTAGen.pure ()

-- | Generate safe indexing programs over exact-depth pipelines.
safeProgramsAtDepth :: Int -> LTAGen.LTAGen Program
safeProgramsAtDepth requestedDepth =
    LTAGen.node "index" validIndex $ LTAGen.do
        vector <- vectorsAtDepth depth
        _function <- indexFunction
        index <- candidateIndexes maximumLength
        LTAGen.pure $ Index (vectorExpression vector) (numberValue index)
  where
    depth = max 0 requestedDepth
    maximumLength = maximumLengthAtDepth depth
    validIndex vector function index =
        withActualFor index (indexFormalAt function) $
            vectorLengthAt vector `isSubtypeOf` function

-- | A function accepting vectors whose length is strictly greater than @i@.
indexFunction :: LTAGen.LTAGen ()
indexFunction =
    LTAGen.refinedNode "index-function" indexInput unconstrained $ LTAGen.do
        _index <- LTAGen.leaf () "i" (value .>=. (-1 :: Int))
        LTAGen.pure ()
  where
    indexInput =
        Fixpoint.pAnd
            [ variable "i" .>=. (0 :: Int)
            , variable "i" .<. value
            ]

-- | One exact integer together with its liquid annotation.
data RefinedNumber = RefinedNumber
    { numberValue :: !Int
    , numberRefinement :: !Refinement
    }

-- | Candidate non-negative result lengths.
possibleLengths :: Int -> LTAGen.LTAGen RefinedNumber
possibleLengths maximumLength = numberPool [0 .. max 0 maximumLength]

-- | Candidate indexes include one deliberately invalid negative value.
candidateIndexes :: Int -> LTAGen.LTAGen RefinedNumber
candidateIndexes maximumLength = numberPool [-1 .. max 0 maximumLength]

-- | Refine every integer in a finite pool by its exact value.
numberPool :: [Int] -> LTAGen.LTAGen RefinedNumber
numberPool integers =
    LTAGen.pool
        [ let refinement = exact integer
           in LTAGen.Refined
                (RefinedNumber integer refinement)
                (fromString $ numberName integer)
                refinement
        | integer <- integers
        ]

-- | One exact integer leaf, used as the stable length position of a vector.
numberLeaf :: Int -> LTAGen.LTAGen RefinedNumber
numberLeaf integer =
    let refinement = exact integer
     in LTAGen.leaf
            (RefinedNumber integer refinement)
            (fromString $ numberName integer)
            refinement

-- | Solver name for one concrete integer used in a substitution.
numberName :: Int -> String
numberName integer
    | integer < 0 = "integer-minus-" <> show (negate integer)
    | otherwise = "integer-" <> show integer

-- | Stable result-length child shared by every vector constructor.
vectorLengthAt :: Position -> Position
vectorLengthAt vector = descendant vector [0]

-- | Named positions inside the append contract.
appendLeftFormalAt, appendRightFormalAt, appendResultAt :: Position -> Position
appendLeftFormalAt function = descendant function [0]
appendRightFormalAt function = descendant function [1]
appendResultAt function = descendant function [2]

-- | Named positions inside the take contract.
takeCountFormalAt, takeResultAt :: Position -> Position
takeCountFormalAt function = descendant function [0]
takeResultAt function = descendant function [1]

-- | Named positions inside the zip contract.
zipLeftFormalAt, zipResultAt :: Position -> Position
zipLeftFormalAt function = descendant function [0]
zipResultAt function = descendant function [1]

-- | Named formal index inside the indexing contract.
indexFormalAt :: Position -> Position
indexFormalAt function = descendant function [0]

-- | An exact integer refinement.
exact :: Int -> Refinement
exact integer = value .==. integer

-- | Largest source-vector length before operations are applied.
maximumSourceLength :: Int
maximumSourceLength = 3

-- | Largest result length reachable at one exact operation depth.
maximumLengthAtDepth :: Int -> Int
maximumLengthAtDepth depth = maximumSourceLength * (2 ^ max 0 depth)

-- | Interpret one vector expression.
evaluateVector :: VectorExpression -> [Int]
evaluateVector (Source _ elements) = elements
evaluateVector (Append left right) = evaluateVector left <> evaluateVector right
evaluateVector (Take count input) = take count $ evaluateVector input
evaluateVector (ZipWithAdd left right) = zipWith (+) (evaluateVector left) (evaluateVector right)

-- | Check a result-length annotation against the independent interpreter.
vectorLengthIsCorrect :: SizedVector -> Bool
vectorLengthIsCorrect SizedVector{vectorExpression, vectorLength} =
    vectorLength == exact (length $ evaluateVector vectorExpression)

-- | Execute a deliberately partial indexing program.
runProgram :: Program -> Int
runProgram (Index expression index)
    | index < 0 = error "microlta invariant broken: negative vector index"
    | otherwise =
        case drop index $ evaluateVector expression of
            element : _ -> element
            [] -> error "microlta invariant broken: vector index out of bounds"

-- | Check the generated safety property independently of the refinements.
programIsSafe :: Program -> Bool
programIsSafe (Index expression index) =
    index >= 0 && index < length (evaluateVector expression)
