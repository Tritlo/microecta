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
module Data.LTA.SizedVectorLanguage (
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

import Data.LTA (Refinement)
import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.Guard (
    Position,
    allOf,
    descendant,
    isSubtypeOf,
    unconstrained,
    withActualFor,
    withActualsFor,
 )
import Data.LTA.Refinement ((.+.), (.<.), (.<=.), (.==.), (.>=.))

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
sourceVectors :: LTA.LTAGen SizedVector
sourceVectors =
    oneofOrDie
        "source vectors"
        [ sized "empty" []
        , sized "pair" [10, 11]
        , sized "triple" [20, 21, 22]
        ]
  where
    sized name elements =
        let refinement = exact $ length elements
         in LTA.refinedNode (fromString name) refinement unconstrained $ LTA.do
                _length <- numberLeaf $ length elements
                LTA.pure $ SizedVector (Source name elements) refinement

{- | Generate exact-depth vector pipelines.

The surface definition is independent of result lengths. Each constructor
proposes a finite result refinement, and its adjacent liquid guard retains
exactly the result compatible with the selected children.
-}
vectorsAtDepth :: Int -> LTA.LTAGen SizedVector
vectorsAtDepth requestedDepth
    | requestedDepth <= 0 = sourceVectors
    | otherwise = vectorLayer depth $ vectorsAtDepth (depth - 1)
  where
    depth = max 0 requestedDepth

-- | Add one dependent vector-operation layer.
vectorLayer :: Int -> LTA.LTAGen SizedVector -> LTA.LTAGen SizedVector
vectorLayer depth children =
    oneofOrDie
        "sized vector layer"
        [ appendedVectors maximumLength children
        , takenVectors maximumLength children
        , zippedVectors maximumLength children
        ]
  where
    maximumLength = maximumLengthAtDepth depth

-- | Generate append nodes whose result length is proved to be @n + m@.
appendedVectors :: Int -> LTA.LTAGen SizedVector -> LTA.LTAGen SizedVector
appendedVectors maximumLength children =
    LTA.refinedNodeBy "append" vectorLength validAppend $ LTA.do
        result <- possibleLengths maximumLength
        _function <- appendFunction
        left <- children
        right <- children
        LTA.pure $
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
appendFunction :: LTA.LTAGen ()
appendFunction = LTA.node "append-function" unconstrained $ LTA.do
    _leftLength <- LTA.leaf () "n" nonNegative
    _rightLength <- LTA.leaf () "m" nonNegative
    _resultLength <- LTA.leaf () "sum" (value .==. (variable "n" .+. variable "m"))
    LTA.pure ()

-- | Generate @take@ nodes with @0 <= k <= n@ and result length @k@.
takenVectors :: Int -> LTA.LTAGen SizedVector -> LTA.LTAGen SizedVector
takenVectors maximumLength children =
    LTA.refinedNodeBy "take" vectorLength validTake $ LTA.do
        result <- possibleLengths maximumLength
        _function <- takeFunction
        count <- possibleLengths maximumLength
        input <- children
        LTA.pure $
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
takeFunction :: LTA.LTAGen ()
takeFunction =
    LTA.refinedNode "take-function" takeInput unconstrained $ LTA.do
        _count <- LTA.leaf () "k" nonNegative
        _result <- LTA.leaf () "take-result" (value .==. variable "k")
        LTA.pure ()
  where
    takeInput =
        Fixpoint.pAnd
            [ variable "k" .>=. (0 :: Int)
            , variable "k" .<=. value
            ]

-- | Generate equal-length element-wise additions.
zippedVectors :: Int -> LTA.LTAGen SizedVector -> LTA.LTAGen SizedVector
zippedVectors maximumLength children =
    LTA.refinedNodeBy "zip-with-add" vectorLength validZip $ LTA.do
        result <- possibleLengths maximumLength
        _function <- zipFunction
        left <- children
        right <- children
        LTA.pure $
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

-- | A function requiring a second vector of length @n@ and returning @n@.
zipFunction :: LTA.LTAGen ()
zipFunction =
    LTA.refinedNode "zip-function" (value .==. variable "n") unconstrained $ LTA.do
        _leftLength <- LTA.leaf () "n" nonNegative
        _result <- LTA.leaf () "zip-result" (value .==. variable "n")
        LTA.pure ()

-- | Generate safe indexing programs over exact-depth pipelines.
safeProgramsAtDepth :: Int -> LTA.LTAGen Program
safeProgramsAtDepth requestedDepth =
    LTA.node "index" validIndex $ LTA.do
        vector <- vectorsAtDepth depth
        _function <- indexFunction
        index <- candidateIndexes maximumLength
        LTA.pure $ Index (vectorExpression vector) (numberValue index)
  where
    depth = max 0 requestedDepth
    maximumLength = maximumLengthAtDepth depth
    validIndex vector function index =
        withActualFor index (indexFormalAt function) $
            vectorLengthAt vector `isSubtypeOf` function

-- | A function accepting vectors whose length is strictly greater than @i@.
indexFunction :: LTA.LTAGen ()
indexFunction =
    LTA.refinedNode "index-function" indexInput unconstrained $ LTA.do
        _index <- LTA.leaf () "i" (value .>=. (-1 :: Int))
        LTA.pure ()
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
possibleLengths :: Int -> LTA.LTAGen RefinedNumber
possibleLengths maximumLength = numberPool [0 .. max 0 maximumLength]

-- | Candidate indexes include one deliberately invalid negative value.
candidateIndexes :: Int -> LTA.LTAGen RefinedNumber
candidateIndexes maximumLength = numberPool [-1 .. max 0 maximumLength]

-- | Refine every integer in a finite pool by its exact value.
numberPool :: [Int] -> LTA.LTAGen RefinedNumber
numberPool integers =
    LTA.pool
        [ let refinement = exact integer
           in LTA.refined
                (RefinedNumber integer refinement)
                (fromString $ numberName integer)
                refinement
        | integer <- integers
        ]

-- | One exact integer leaf, used as the stable length position of a vector.
numberLeaf :: Int -> LTA.LTAGen RefinedNumber
numberLeaf integer =
    let refinement = exact integer
     in LTA.leaf
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

-- | Liquid Fixpoint's distinguished value variable.
value :: Fixpoint.Expr
value = variable "v"

-- | Build a Liquid Fixpoint integer variable.
variable :: String -> Fixpoint.Expr
variable = Fixpoint.EVar . Fixpoint.symbol

-- | An exact integer refinement.
exact :: Int -> Refinement
exact integer = value .==. integer

-- | The refinement of a non-negative vector length.
nonNegative :: Refinement
nonNegative = value .>=. (0 :: Int)

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

-- | Select one known non-empty alternative set.
oneofOrDie :: String -> [LTA.LTAGen a] -> LTA.LTAGen a
oneofOrDie context alternatives =
    case LTA.oneof alternatives of
        Left err -> error $ context <> " is unexpectedly empty: " <> show err
        Right generator -> generator
