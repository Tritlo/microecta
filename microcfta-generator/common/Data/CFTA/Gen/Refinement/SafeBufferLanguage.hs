{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}

{- | A small buffer-program language whose generated programs are safe by
construction.

The interesting constraints are not finite tags. Buffer lengths and indexes
are symbolic integers in a Liquid environment. A contract makes Z3 prove that
an index is in bounds and that an append result length is the sum of its
operand lengths. A condition on a drawn buffer carries those result
refinements into a later non-empty precondition.

That is the practical QuickCheck payoff: the deliberately partial
'runProgram' is total for every member of 'safePrograms', without a
@suchThat@ loop or a precondition in the property.
-}
module Data.CFTA.Gen.Refinement.SafeBufferLanguage (
    BufferExpression (..),
    RefinedBuffer (..),
    Program (..),
    variable,
    solverDeclarations,
    solverAssumptions,
    sourceBuffers,
    appendedBuffers,
    safeReads,
    safeHeads,
    safePrograms,
    evaluateBuffer,
    runProgram,
    programIsSafe,
) where

import Data.String (fromString)
import qualified Language.Fixpoint.Types as Fixpoint

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Refinement (Formula, LiquidSymbol (LiquidSymbol))
import Data.CFTA.Refinement.Expression (Expr, Refinement, refinementFormula, variable, (.&&), (.<), (.<=), (.==), (.>=))
import Data.CFTA.Refinement.Guard (contract)

-- | Buffer expressions understood by the example interpreter.
data BufferExpression
    = Source !String ![Int]
    | Append !BufferExpression !BufferExpression
    deriving (Eq, Ord, Show)

-- | A buffer expression paired with its proven length refinement.
data RefinedBuffer = RefinedBuffer
    { bufferExpression :: !BufferExpression
    , bufferLength :: !Formula
    }
    deriving (Eq, Show)

-- | Partial buffer operations that become safe after LTA compilation.
data Program
    = ReadAt !BufferExpression !Int
    | ReadHead !BufferExpression
    deriving (Eq, Ord, Show)

-- | Integer names used by guards and their ambient typing environment.
solverDeclarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
solverDeclarations =
    [ (Fixpoint.symbol name, Fixpoint.FInt)
    | name <- "v" : "n" : "m" : map fst namedIntegers
    ]

-- | Facts a Liquid typing environment knows about the named inputs.
solverAssumptions :: [Formula]
solverAssumptions =
    [ variable name .== fromIntegral integer
    | (name, integer) <- namedIntegers
    ]

namedIntegers :: [(String, Int)]
namedIntegers =
    [ ("emptyLength", 0)
    , ("singletonLength", 1)
    , ("tripleLength", 3)
    , ("minusOne", -1)
    , ("indexZero", 0)
    , ("indexOne", 1)
    , ("indexTwo", 2)
    , ("indexThree", 3)
    ]

-- | Three concrete buffers whose lengths enter the solver symbolically.
sourceBuffers :: LTAGen.LTAGen RefinedBuffer
sourceBuffers =
    LTAGen.namedPool
        [ source "empty" "emptyLength" []
        , source "singleton" "singletonLength" [10]
        , source "triple" "tripleLength" [20, 21, 22]
        ]
  where
    source name lengthName contents =
        let refinement v = v .== variable lengthName
            buffer = RefinedBuffer (Source name contents) (refinementFormula refinement)
         in LTAGen.Refined buffer (fromString lengthName) refinement

-- | Index candidates deliberately include negative and upper-bound failures.
indexes :: LTAGen.LTAGen (String, Int)
indexes =
    LTAGen.namedPool
        [ index "minusOne" (-1)
        , index "indexZero" 0
        , index "indexOne" 1
        , index "indexTwo" 2
        , index "indexThree" 3
        ]
  where
    index name integer =
        LTAGen.Refined (name, integer) (fromString name) (\v -> v .== variable name)

-- | Programs whose symbolic index is proved in bounds for the chosen buffer.
safeReads :: LTAGen.LTAGen Program
safeReads = LTAGen.guarded "read-at" inBounds $ LTAGen.do
    buffer <- sourceBuffers
    ~(_indexName, index) <- indexes
    LTAGen.pure $ ReadAt (bufferExpression buffer) index

-- | A read at index @i@ from a buffer of length @n@ needs @0 <= i < n@.
inBounds :: Expr -> Expr -> Formula
inBounds n i = 0 .<= i .&& i .< n

-- | The refinement required by a safe head operation.
positive :: Refinement
positive v = v .>= 1

-- | Every ordered append of the source buffers, with its result length proved.
appendedBuffers :: LTAGen.LTAGen RefinedBuffer
appendedBuffers =
    LTAGen.refinedNodeByRoots "append" (const . resultRefinement) (contract sumOfLengths) $ LTAGen.do
        result <- possibleLengths
        left <- sourceBuffers
        right <- sourceBuffers
        LTAGen.pure $
            RefinedBuffer
                (Append (bufferExpression left) (bufferExpression right))
                (resultLength result)
  where
    resultRefinement (LiquidSymbol _ refinement : _) = refinement
    resultRefinement [] = error "appendedBuffers: missing result annotation"

-- | The chosen result length is the sum of the operand lengths.
sumOfLengths :: Expr -> Expr -> Expr -> Formula
sumOfLengths result n m = result .== n + m

-- | One candidate result-length refinement for append.
newtype LengthResult = LengthResult
    { resultLength :: Formula
    }

-- | Every result length reachable from the finite source-buffer universe.
possibleLengths :: LTAGen.LTAGen LengthResult
possibleLengths =
    LTAGen.namedPool
        [ result length_
        | length_ <- [0, 1, 2, 3, 4, 6] :: [Int]
        ]
  where
    result length_ =
        let refinement v = v .== fromIntegral length_
         in LTAGen.Refined
                (LengthResult (refinementFormula refinement))
                (fromString $ "length-" <> show length_)
                refinement

-- | Safe head reads over both source and solver-checked appended buffers.
safeHeads :: LTAGen.LTAGen Program
safeHeads = LTAGen.node "head" $ LTAGen.do
    buffer <- allBuffers `LTAGen.satisfying` positive
    LTAGen.pure $ ReadHead $ bufferExpression buffer

-- | Source and solver-checked appended buffers available to later operations.
allBuffers :: LTAGen.LTAGen RefinedBuffer
allBuffers = LTAGen.oneof [sourceBuffers, appendedBuffers]

-- | The complete safe program language used by the QuickCheck example.
safePrograms :: LTAGen.LTAGen Program
safePrograms = LTAGen.oneof [safeReads, safeHeads]

-- | Interpret a buffer expression.
evaluateBuffer :: BufferExpression -> [Int]
evaluateBuffer (Source _ contents) = contents
evaluateBuffer (Append left right) = evaluateBuffer left <> evaluateBuffer right

{- | Execute a deliberately partial buffer program.

The function uses 'head' and list indexing directly. It is safe for values
produced by the compiled 'safePrograms' language; that is what the specs prove.
-}
runProgram :: Program -> Int
runProgram (ReadAt buffer index)
    | index < 0 = error "microlta invariant broken: negative buffer index"
    | otherwise =
        case drop index $ evaluateBuffer buffer of
            element : _ -> element
            [] -> error "microlta invariant broken: buffer index out of bounds"
runProgram (ReadHead buffer) =
    case evaluateBuffer buffer of
        element : _ -> element
        [] -> error "microlta invariant broken: head of an empty buffer"

-- | Independent executable safety check used by the properties.
programIsSafe :: Program -> Bool
programIsSafe (ReadAt buffer index) =
    index >= 0 && index < length (evaluateBuffer buffer)
programIsSafe (ReadHead buffer) =
    not $ null $ evaluateBuffer buffer
