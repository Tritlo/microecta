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

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Refinement (Formula, LiquidSymbol (LiquidSymbol))
import Data.CFTA.Refinement.Expression (Expr, Refinement, refinementFormula, (.&&), (.<), (.<=), (.==))
import Data.CFTA.Refinement.Guard (contract)

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
    , vectorLength :: !Formula
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
    LTAGen.namedPool
        [ sized "empty" []
        , sized "pair" [10, 11]
        , sized "triple" [20, 21, 22]
        ]
  where
    sized name elements =
        let refinement = exact $ length elements
         in LTAGen.Refined
                (SizedVector (Source name elements) (refinementFormula refinement))
                (fromString name)
                refinement

{- | Generate exact-depth vector pipelines.

The surface definition is independent of result lengths. Each constructor
proposes a finite result refinement as its first child, and its contract
retains exactly the result compatible with the other children. A vector's own
refinement is its exact length, so a contract names the length of a vector
child by the child's term.
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
    LTAGen.refinedNodeByRoots "append" (const . resultRefinement) (contract appendContract) $ LTAGen.do
        result <- possibleLengths maximumLength
        left <- children
        right <- children
        LTAGen.pure $
            SizedVector
                (Append (vectorExpression left) (vectorExpression right))
                (numberRefinement result)

-- | The result length of @append xs ys@ is @n + m@.
appendContract :: Expr -> Expr -> Expr -> Formula
appendContract result n m = result .== n + m

-- | Generate @take@ nodes with @0 <= k <= n@ and result length @k@.
takenVectors :: Int -> LTAGen.LTAGen SizedVector -> LTAGen.LTAGen SizedVector
takenVectors maximumLength children =
    LTAGen.refinedNodeByRoots "take" (const . resultRefinement) (contract takeContract) $ LTAGen.do
        result <- possibleLengths maximumLength
        count <- possibleLengths maximumLength
        input <- children
        LTAGen.pure $
            SizedVector
                (Take (numberValue count) $ vectorExpression input)
                (numberRefinement result)

-- | @take k xs@ needs @0 <= k <= n@ and has length @k@.
takeContract :: Expr -> Expr -> Expr -> Formula
takeContract result k n = 0 .<= k .&& k .<= n .&& result .== k

-- | Generate equal-length element-wise additions.
zippedVectors :: Int -> LTAGen.LTAGen SizedVector -> LTAGen.LTAGen SizedVector
zippedVectors maximumLength children =
    LTAGen.refinedNodeByRoots "zip-with-add" (const . resultRefinement) (contract zipContract) $ LTAGen.do
        result <- possibleLengths maximumLength
        left <- children
        right <- children
        LTAGen.pure $
            SizedVector
                (ZipWithAdd (vectorExpression left) (vectorExpression right))
                (numberRefinement result)

-- | @zipWith (+) xs ys@ needs @m == n@ and has length @n@.
zipContract :: Expr -> Expr -> Expr -> Formula
zipContract result n m = m .== n .&& result .== n

-- | Retain the selected result annotation without inspecting a vector value.
resultRefinement :: [LiquidSymbol] -> Formula
resultRefinement (LiquidSymbol _ refinement : _) = refinement
resultRefinement [] = error "resultRefinement: missing result annotation"

-- | Generate safe indexing programs over exact-depth pipelines.
safeProgramsAtDepth :: Int -> LTAGen.LTAGen Program
safeProgramsAtDepth requestedDepth =
    LTAGen.guarded "index" inBounds $ LTAGen.do
        vector <- vectorsAtDepth depth
        index <- candidateIndexes maximumLength
        LTAGen.pure $ Index (vectorExpression vector) (numberValue index)
  where
    depth = max 0 requestedDepth
    maximumLength = maximumLengthAtDepth depth

-- | Indexing a vector of length @n@ at @i@ needs @0 <= i < n@.
inBounds :: Expr -> Expr -> Formula
inBounds n i = 0 .<= i .&& i .< n

-- | One exact integer together with its liquid annotation.
data RefinedNumber = RefinedNumber
    { numberValue :: !Int
    , numberRefinement :: !Formula
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
    LTAGen.namedPool
        [ let refinement = exact integer
           in LTAGen.Refined
                (RefinedNumber integer (refinementFormula refinement))
                (fromString $ numberName integer)
                refinement
        | integer <- integers
        ]

-- | Solver name for one concrete integer used in a substitution.
numberName :: Int -> String
numberName integer
    | integer < 0 = "integer-minus-" <> show (negate integer)
    | otherwise = "integer-" <> show integer

-- | An exact integer refinement.
exact :: Int -> Refinement
exact integer v = v .== fromIntegral integer

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
    vectorLength == refinementFormula (exact (length $ evaluateVector vectorExpression))

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
