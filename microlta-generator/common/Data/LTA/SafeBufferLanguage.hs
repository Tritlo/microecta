{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}

{- | A small buffer-program language whose generated programs are safe by
construction.

The interesting constraints are not finite tags. Buffer lengths and indexes
are symbolic integers in a Liquid environment. The LTA uses Z3 to prove an
index is in bounds, to compute append result lengths by actual-for-formal
substitution, and to carry those result refinements into later operations.

That is the practical QuickCheck payoff: the deliberately partial
'runProgram' is total for every member of 'safePrograms', without a
@suchThat@ loop or a precondition in the property.
-}
module Data.LTA.SafeBufferLanguage (
    BufferExpression (..),
    RefinedBuffer (..),
    Program (..),
    value,
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

import Data.LTA (LiquidConstraint, Refinement)
import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.Guard (
    Position,
    descendant,
    isSubtypeOf,
    requires,
    unconstrained,
    withActualFor,
    withActualsFor,
 )
import Data.LTA.Refinement ((.+.), (.<.), (.==.), (.>=.))

-- | Buffer expressions understood by the example interpreter.
data BufferExpression
    = Source !String ![Int]
    | Append !BufferExpression !BufferExpression
    deriving (Eq, Ord, Show)

-- | A buffer expression paired with its proven length refinement.
data RefinedBuffer = RefinedBuffer
    { bufferExpression :: !BufferExpression
    , bufferLength :: !Refinement
    }
    deriving (Eq, Show)

-- | Partial buffer operations that become safe after LTA compilation.
data Program
    = ReadAt !BufferExpression !Int
    | ReadHead !BufferExpression
    deriving (Eq, Ord, Show)

-- | Liquid Fixpoint's distinguished value variable.
value :: Fixpoint.Expr
value = variable "v"

-- | Build a Liquid Fixpoint integer variable.
variable :: String -> Fixpoint.Expr
variable = Fixpoint.EVar . Fixpoint.symbol

-- | Integer names used by guards and their ambient typing environment.
solverDeclarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
solverDeclarations =
    [ (Fixpoint.symbol name, Fixpoint.FInt)
    | name <- "v" : "n" : "m" : map fst namedIntegers
    ]

-- | Facts a Liquid typing environment knows about the named inputs.
solverAssumptions :: [Refinement]
solverAssumptions =
    [ variable name .==. integer
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
sourceBuffers :: LTA.LTAGen RefinedBuffer
sourceBuffers =
    LTA.pool
        [ source "empty" "emptyLength" []
        , source "singleton" "singletonLength" [10]
        , source "triple" "tripleLength" [20, 21, 22]
        ]
  where
    source name lengthName contents =
        let refinement = value .==. variable lengthName
            buffer = RefinedBuffer (Source name contents) refinement
         in LTA.refined buffer (fromString lengthName) refinement

-- | Index candidates deliberately include negative and upper-bound failures.
indexes :: LTA.LTAGen (String, Int)
indexes =
    LTA.pool
        [ index "minusOne" (-1)
        , index "indexZero" 0
        , index "indexOne" 1
        , index "indexTwo" 2
        , index "indexThree" 3
        ]
  where
    index name integer =
        LTA.refined (name, integer) (fromString name) (value .==. variable name)

-- | Programs whose symbolic index is proved in bounds for the chosen buffer.
safeReads :: LTA.LTAGen Program
safeReads = LTA.node "read-at" validRead $ LTA.do
    buffer <- sourceBuffers
    _function <- readFunction
    ~(_indexName, index) <- indexes
    LTA.pure $ ReadAt (bufferExpression buffer) index

-- | Substitute the selected buffer length into the function precondition.
validRead :: Position -> Position -> Position -> LiquidConstraint
validRead buffer function index =
    withActualFor buffer (descendant function [0]) $
        index `isSubtypeOf` descendant function [1]

-- | A dependent read operation with formal length and valid-index positions.
readFunction :: LTA.LTAGen ()
readFunction = LTA.node "read-function" unconstrained $ LTA.do
    _lengthFormal <- LTA.leaf () "n" nonNegative
    _validIndex <- LTA.leaf () "valid-index" indexWithinLength
    LTA.pure ()

-- | The refinement of a valid buffer length.
nonNegative :: Refinement
nonNegative = value .>=. (0 :: Int)

-- | The refinement required by a safe head operation.
positive :: Refinement
positive = value .>=. (1 :: Int)

-- | A dependent index range using the formal buffer length @n@.
indexWithinLength :: Refinement
indexWithinLength =
    Fixpoint.pAnd
        [ value .>=. (0 :: Int)
        , value .<. variable "n"
        ]

-- | Every ordered append of the source buffers, with its result length proved.
appendedBuffers :: LTA.LTAGen RefinedBuffer
appendedBuffers =
    LTA.refinedNodeBy "append" bufferLength validAppend $ LTA.do
        result <- possibleLengths
        _function <- appendFunction
        left <- sourceBuffers
        right <- sourceBuffers
        LTA.pure $
            RefinedBuffer
                (Append (bufferExpression left) (bufferExpression right))
                (resultLength result)

-- | One candidate result-length refinement for append.
data LengthResult = LengthResult
    { resultLength :: !Refinement
    }

-- | Every result length reachable from the finite source-buffer universe.
possibleLengths :: LTA.LTAGen LengthResult
possibleLengths =
    LTA.pool
        [ result length_
        | length_ <- [0, 1, 2, 3, 4, 6] :: [Int]
        ]
  where
    result length_ =
        let refinement = value .==. length_
         in LTA.refined
                (LengthResult refinement)
                (fromString $ "length-" <> show length_)
                refinement

-- | A two-argument dependent append operation whose output length is @n + m@.
appendFunction :: LTA.LTAGen ()
appendFunction = LTA.node "append-function" unconstrained $ LTA.do
    _leftFormal <- LTA.leaf () "n" nonNegative
    _rightFormal <- LTA.leaf () "m" nonNegative
    _output <- LTA.leaf () "sum-length" (value .==. (variable "n" .+. variable "m"))
    LTA.pure ()

-- | Substitute both selected operand lengths into append's result refinement.
validAppend :: Position -> Position -> Position -> Position -> LiquidConstraint
validAppend result function left right =
    withActualsFor
        [ (left, descendant function [0])
        , (right, descendant function [1])
        ]
        (descendant function [2] `isSubtypeOf` result)

-- | Safe head reads over both source and solver-checked appended buffers.
safeHeads :: LTA.LTAGen Program
safeHeads = LTA.node "head" hasElement $ LTA.do
    buffer <- allBuffers
    LTA.pure $ ReadHead $ bufferExpression buffer

-- | Require the chosen buffer to prove that a head element exists.
hasElement :: Position -> LiquidConstraint
hasElement buffer = buffer `requires` positive

-- | Source and solver-checked appended buffers available to later operations.
allBuffers :: LTA.LTAGen RefinedBuffer
allBuffers =
    case LTA.oneof [sourceBuffers, appendedBuffers] of
        Left err -> error $ "safe buffer example is unexpectedly empty: " <> show err
        Right buffers -> buffers

-- | The complete safe program language used by the QuickCheck example.
safePrograms :: LTA.LTAGen Program
safePrograms =
    case LTA.oneof [safeReads, safeHeads] of
        Left err -> error $ "safe program example is unexpectedly empty: " <> show err
        Right programs -> programs

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
