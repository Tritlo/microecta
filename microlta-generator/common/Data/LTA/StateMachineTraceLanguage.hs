{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}

{- | Solver-checked generation of typed stack-machine traces.

This is the liquid-tree analogue of the symbolic trace generation described in
<https://well-typed.com/blog/2019/01/qsm-in-depth/ the quickcheck-state-machine tutorial>.
The complete trace is generated before it is executed, but every command is
checked against the abstract stack established by the preceding prefix.

The stack shape is the state-machine type. Its compact integer encoding makes
the dependent transition contracts visible to Liquid Fixpoint:

@Push TInt@ maps @Stack s@ to @Stack (TInt ': s)@.
@Add@ maps @Stack (TInt ': TInt ': s)@ to @Stack (TInt ': s)@.
@Equal@ maps @Stack (a ': a ': s)@ to @Stack (TBool ': s)@.
@Pop@ maps @Stack (a ': s)@ to @Stack s@ and returns @a@.

The result refinement of every trace node is its output stack. Extending the
trace therefore feeds the previous output space directly into the next
command's input space. Z3 removes ill-typed prefixes before QuickCheck samples
or shrinks the compiled language.
-}
module Data.LTA.StateMachineTraceLanguage (
    ValueType (..),
    Value (..),
    StackState (..),
    Command (..),
    Response (..),
    ActualResponse (..),
    Event (..),
    Trace (..),
    maximumStackDepth,
    encodeState,
    value,
    variable,
    stateRefinement,
    solverDeclarations,
    solverAssumptions,
    initialTrace,
    tracesOfLength,
    tracesUpTo,
    naiveTraceGen,
    handwrittenTraceGen,
    traceCount,
    modelStep,
    replayTrace,
    executeTrace,
    traceIsValid,
) where

import Control.Monad (foldM, guard)
import Data.String (fromString)
import qualified Language.Fixpoint.Types as Fixpoint
import qualified Test.QuickCheck as QC

import Data.LTA (Guard, Refinement, Symbol)
import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.Guard (
    Position,
    allOf,
    descendant,
    isSubtypeOf,
    root,
    unconstrained,
    withActualFor,
 )
import Data.LTA.Refinement ((.*.), (.+.), (.-.), (.<=.), (.==.), (.>=.))

-- | Ground value types shared with the typed-expression example.
data ValueType = TInt | TBool
    deriving (Bounded, Enum, Eq, Ord, Show)

-- | Concrete values understood by the tiny stack-machine interpreter.
data Value
    = IntValue !Int
    | BoolValue !Bool
    deriving (Eq, Ord, Show)

-- | The abstract QSM model: stack types, with the top at the head.
newtype StackState = StackState {stackTypes :: [ValueType]}
    deriving (Eq, Ord, Show)

-- | Commands accepted by the typed stack machine.
data Command
    = Push !Value
    | Add
    | And
    | Equal
    | Not
    | Pop
    deriving (Eq, Ord, Show)

-- | The response space predicted by the abstract model.
data Response
    = Accepted
    | Popped !ValueType
    deriving (Eq, Ord, Show)

-- | Concrete responses returned by the executable stack machine.
data ActualResponse
    = Completed
    | Returned !Value
    deriving (Eq, Ord, Show)

-- | One fully predicted state-machine event.
data Event = Event
    { eventBefore :: !StackState
    , eventCommand :: !Command
    , eventResponse :: !Response
    , eventAfter :: !StackState
    }
    deriving (Eq, Ord, Show)

-- | A symbolic trace and the model state established by its final event.
data Trace = Trace
    { traceEvents :: ![Event]
    , traceFinalState :: !StackState
    }
    deriving (Eq, Ord, Show)

-- | The finite generation boundary; the transition formulae are not unrolled.
maximumStackDepth :: Int
maximumStackDepth = 3

-- | Encode a type stack as a binary cons-list with the top in the low bits.
encodeState :: StackState -> Int
encodeState (StackState types) = foldr encodeType 0 types
  where
    encodeType type_ rest = 2 * rest + typeTag type_

-- | Liquid Fixpoint's distinguished value variable.
value :: Fixpoint.Expr
value = variable "v"

-- | Build a Liquid Fixpoint integer variable.
variable :: String -> Fixpoint.Expr
variable = Fixpoint.EVar . Fixpoint.symbol

-- | Give one stack state an exact symbolic refinement.
stateRefinement :: StackState -> Refinement
stateRefinement state = value .==. variable (stateName state)

-- | Integer symbols that can occur in a stack-machine solver query.
solverDeclarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
solverDeclarations =
    [ (Fixpoint.symbol name, Fixpoint.FInt)
    | name <- ["v", "model", "start", "step"] <> map stateName stackStates
    ]

-- | Facts assigning each finite stack shape its compact integer encoding.
solverAssumptions :: [Refinement]
solverAssumptions =
    [ variable (stateName state) .==. encodeState state
    | state <- stackStates
    ]

-- | The empty trace starts with an empty operand stack.
initialTrace :: LTA.LTAGen Trace
initialTrace =
    LTA.refinedNode "start" (stateRefinement emptyState) unconstrained $
        LTA.pure (Trace [] emptyState)

-- | Generate traces with exactly the requested number of commands.
tracesOfLength :: Int -> LTA.LTAGen Trace
tracesOfLength length_
    | length_ <= 0 = initialTrace
    | otherwise = extendTrace $ tracesOfLength (length_ - 1)

-- | Generate every trace up to a maximum length, shortest first for shrinking.
tracesUpTo :: Int -> Either LTA.GeneratorError (LTA.LTAGen Trace)
tracesUpTo maximumLength =
    LTA.oneof [tracesOfLength length_ | length_ <- [0 .. maximumLength]]

{- | Generate an untyped command sequence and reject the complete sequence
unless the model accepts every transition.

The raw sequence generator is uniform, so conditioning it on validity leaves a
uniform distribution over all valid traces of the requested length.
-}
naiveTraceGen :: Int -> QC.Gen Trace
naiveTraceGen length_ =
    QC.suchThatMap
        (QC.vectorOf (max 0 length_) $ QC.elements commandValues)
        traceFromCommands

{- | Generate only valid commands while tracking the abstract stack state.

Each command is weighted by the number of valid suffixes following its output
state. The resulting handwritten generator is therefore uniform over complete
traces, not merely uniform at each individual transition.
-}
handwrittenTraceGen :: Int -> QC.Gen Trace
handwrittenTraceGen length_ = generateFrom (max 0 length_) emptyState
  where
    generateFrom 0 state = pure $ Trace [] state
    generateFrom remaining before =
        frequencyInteger
            [ ( traceCount (remaining - 1) after
              , do
                    suffix <- generateFrom (remaining - 1) after
                    pure $
                        suffix
                            { traceEvents =
                                Event before command response after : traceEvents suffix
                            }
              )
            | command <- commandValues
            , Just (response, after) <- [modelStep before command]
            ]

-- | Count valid command traces of one remaining length from an abstract state.
traceCount :: Int -> StackState -> Integer
traceCount remaining before
    | remaining <= 0 = 1
    | otherwise =
        sum
            [ traceCount (remaining - 1) after
            | command <- commandValues
            , Just (_, after) <- [modelStep before command]
            ]

-- | Replay an untyped command sequence into a fully predicted trace.
traceFromCommands :: [Command] -> Maybe Trace
traceFromCommands commands = do
    (events, finalState) <- foldM appendCommand ([], emptyState) commands
    pure $ Trace (reverse events) finalState
  where
    appendCommand (events, before) command = do
        (response, after) <- modelStep before command
        pure (Event before command response after : events, after)

-- | Every distinct raw command value in the example alphabet.
commandValues :: [Command]
commandValues = map Push literalValues <> [Add, And, Equal, Not, Pop]

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

{- | Advance the pure abstract model when a command's stack type permits it.

This function is deliberately independent of the LTA guard. The specs replay
all accepted witnesses through it so a mistake in the liquid encoding cannot
silently bless an invalid trace.
-}
modelStep :: StackState -> Command -> Maybe (Response, StackState)
modelStep (StackState stack) (Push pushed)
    | length stack < maximumStackDepth =
        Just (Accepted, StackState $ valueType pushed : stack)
    | otherwise = Nothing
modelStep (StackState (TInt : TInt : rest)) Add =
    Just (Accepted, StackState $ TInt : rest)
modelStep (StackState (TBool : TBool : rest)) And =
    Just (Accepted, StackState $ TBool : rest)
modelStep (StackState (left : right : rest)) Equal
    | left == right = Just (Accepted, StackState $ TBool : rest)
modelStep state@(StackState (TBool : _)) Not = Just (Accepted, state)
modelStep (StackState (top : rest)) Pop = Just (Popped top, StackState rest)
modelStep _ _ = Nothing

-- | Replay a predicted trace through the independent abstract transition model.
replayTrace :: Trace -> Maybe StackState
replayTrace Trace{traceEvents} = foldM replay emptyState traceEvents
  where
    replay current Event{eventBefore, eventCommand, eventResponse, eventAfter} = do
        guard $ current == eventBefore
        (actualResponse, actualAfter) <- modelStep current eventCommand
        guard $ actualResponse == eventResponse
        guard $ actualAfter == eventAfter
        pure actualAfter

{- | Execute a generated trace against a separate concrete stack machine.

The LTA only sees abstract stack types. This interpreter sees integer and
Boolean values and checks that its concrete responses have the shapes predicted
by the generated trace.
-}
executeTrace :: Trace -> Maybe [ActualResponse]
executeTrace Trace{traceEvents, traceFinalState} = do
    (responses, finalStack) <- foldM execute ([], []) traceEvents
    guard $ StackState (map valueType finalStack) == traceFinalState
    pure $ reverse responses
  where
    execute (responses, stack) Event{eventBefore, eventCommand, eventResponse, eventAfter} = do
        guard $ StackState (map valueType stack) == eventBefore
        (actualResponse, nextStack) <- executeCommand stack eventCommand
        guard $ responseType actualResponse == eventResponse
        guard $ StackState (map valueType nextStack) == eventAfter
        pure (actualResponse : responses, nextStack)

-- | Whether both the abstract and concrete machines accept a predicted trace.
traceIsValid :: Trace -> Bool
traceIsValid trace =
    replayTrace trace == Just (traceFinalState trace)
        && case executeTrace trace of
            Just _ -> True
            Nothing -> False

-- | Add one solver-checked transition to an existing trace language.
extendTrace :: LTA.LTAGen Trace -> LTA.LTAGen Trace
extendTrace previousTraces =
    LTA.refinedNodeBy "step" (stateRefinement . traceFinalState) validStep $ LTA.do
        previous <- previousTraces
        command <- commandContracts
        LTA.pure $ predictStep previous command

{- | Check one dependent state transition.

The previous trace root is both the selected input state and the actual value
substituted for the command's formal @model@. The command's post-state formula
must then imply the new trace root. No numeric child indices leak into the
constructor call.
-}
validStep :: Position -> Position -> Guard
validStep previous command =
    allOf
        [ previous `isSubtypeOf` command
        , withActualFor previous (descendant command [0]) $
            descendant command [1] `isSubtypeOf` root
        ]

{- | Construct the predicted Haskell event for one raw generator candidate.

Invalid candidates still need an ordinary value while the applicative product
is assembled. Their placeholder event is unobservable: 'validStep' rejects the
candidate before it enters the compiled language.
-}
predictStep :: Trace -> Command -> Trace
predictStep previous command =
    let before = traceFinalState previous
        (response, after) = case modelStep before command of
            Just prediction -> prediction
            Nothing -> (Accepted, before)
     in Trace
            (traceEvents previous <> [Event before command response after])
            after

{- | Dependent command contracts over the formal input state @model@.

Each command root is its admissible input-state space. Child zero names the
formal input; child one is the output-state refinement. The command alternatives
are schemas, not one transition per concrete pair of stack states.
-}
commandContracts :: LTA.LTAGen Command
commandContracts =
    oneofOrDie
        "typed stack-machine command contracts"
        ( map pushContract literalValues
            <> [ popContract TInt
               , popContract TBool
               , contract "add" Add (stacksStartingWith [TInt, TInt]) popIntOutput
               , contract "and" And (stacksStartingWith [TBool, TBool]) popBoolOutput
               , contract "equal-int" Equal (stacksStartingWith [TInt, TInt]) equalIntOutput
               , contract "equal-bool" Equal (stacksStartingWith [TBool, TBool]) equalBoolOutput
               , contract "not" Not (stacksStartingWith [TBool]) unchangedOutput
               ]
        )

-- | Build the dependent transition contract for one pushed literal.
pushContract :: Value -> LTA.LTAGen Command
pushContract pushed =
    contract
        (fromString $ "push-" <> valueName pushed)
        (Push pushed)
        stacksWithRoom
        (value .==. ((2 :: Int) .*. variable "model" .+. typeTag (valueType pushed)))

-- | Build one of the two typed pop transition contracts.
popContract :: ValueType -> LTA.LTAGen Command
popContract type_ =
    contract
        (fromString $ "pop-" <> typeName type_)
        Pop
        (stacksStartingWith [type_])
        (popOutput type_)

-- | Output relation for removing one leading stack-type tag.
popOutput :: ValueType -> Refinement
popOutput TInt = popIntOutput
popOutput TBool = popBoolOutput

-- | Build one input-space/formal-state/post-state command schema.
contract :: Symbol -> Command -> Refinement -> Refinement -> LTA.LTAGen Command
contract symbol command inputSpace postState =
    LTA.refinedNode symbol inputSpace unconstrained $ LTA.do
        _formalState <- LTA.leaf () "model" stateRange
        _postState <- LTA.leaf () "post-state" postState
        LTA.pure command

-- | States in which another value can be pushed.
stacksWithRoom :: Refinement
stacksWithRoom = oneOfStates ((< maximumStackDepth) . length . stackTypes)

-- | States whose top prefix has the requested sequence of types.
stacksStartingWith :: [ValueType] -> Refinement
stacksStartingWith prefix = oneOfStates (prefix `isPrefixOf`)
  where
    isPrefixOf expected state = expected == take (length expected) (stackTypes state)

-- | Describe a non-empty subset of the bounded abstract state space.
oneOfStates :: (StackState -> Bool) -> Refinement
oneOfStates predicate =
    Fixpoint.pOr
        [ value .==. encodeState state
        | state <- stackStates
        , predicate state
        ]

-- | The bounded range accepted at the command's formal state position.
stateRange :: Refinement
stateRange =
    Fixpoint.pAnd
        [ value .>=. (0 :: Int)
        , value .<=. maximumEncodedState
        ]

-- | @Add@ and @Pop Int@ both remove one leading integer tag.
popIntOutput :: Refinement
popIntOutput = variable "model" .==. ((2 :: Int) .*. value .+. (1 :: Int))

-- | @And@ and @Pop Bool@ both remove one leading Boolean tag.
popBoolOutput :: Refinement
popBoolOutput = variable "model" .==. ((2 :: Int) .*. value .+. (2 :: Int))

-- | Replacing two integers with a Boolean relates input to output by this law.
equalIntOutput :: Refinement
equalIntOutput = variable "model" .==. ((2 :: Int) .*. value .-. (1 :: Int))

-- | Replacing two Booleans with one Boolean relates input and output by this law.
equalBoolOutput :: Refinement
equalBoolOutput = variable "model" .==. ((2 :: Int) .*. value .+. (2 :: Int))

-- | Operations such as Boolean negation preserve the complete stack type.
unchangedOutput :: Refinement
unchangedOutput = value .==. variable "model"

-- | Every stack type inside the finite generation boundary.
stackStates :: [StackState]
stackStates =
    [ StackState types
    | depth <- [0 .. maximumStackDepth]
    , types <- typeLists depth
    ]
  where
    typeLists 0 = [[]]
    typeLists depth = (:) <$> [TInt, TBool] <*> typeLists (depth - 1)

-- | The empty abstract stack.
emptyState :: StackState
emptyState = StackState []

-- | Largest state code inside 'maximumStackDepth'.
maximumEncodedState :: Int
maximumEncodedState = maximum $ map encodeState stackStates

-- | The solver and LTA symbol name for one stack state.
stateName :: StackState -> String
stateName state = "stack" <> show (encodeState state)

-- | Ground literals shared conceptually with the FTA and ECTA examples.
literalValues :: [Value]
literalValues =
    [ IntValue 0
    , IntValue 1
    , BoolValue False
    , BoolValue True
    ]

-- | The type of a concrete stack-machine value.
valueType :: Value -> ValueType
valueType (IntValue _) = TInt
valueType (BoolValue _) = TBool

-- | Small stable suffix used in public constructor labels.
valueName :: Value -> String
valueName (IntValue integer) = "int-" <> show integer
valueName (BoolValue boolean) = "bool-" <> show boolean

-- | Numeric tag used by the binary type-stack encoding.
typeTag :: ValueType -> Int
typeTag TInt = 1
typeTag TBool = 2

-- | Human-readable type name used by constructor labels.
typeName :: ValueType -> String
typeName TInt = "int"
typeName TBool = "bool"

-- | Execute one command against the concrete stack-machine implementation.
executeCommand :: [Value] -> Command -> Maybe (ActualResponse, [Value])
executeCommand stack (Push pushed)
    | length stack < maximumStackDepth = Just (Completed, pushed : stack)
    | otherwise = Nothing
executeCommand (IntValue right : IntValue left : rest) Add =
    Just (Completed, IntValue (left + right) : rest)
executeCommand (BoolValue right : BoolValue left : rest) And =
    Just (Completed, BoolValue (left && right) : rest)
executeCommand (left : right : rest) Equal
    | valueType left == valueType right =
        Just (Completed, BoolValue (left == right) : rest)
executeCommand (BoolValue boolean : rest) Not =
    Just (Completed, BoolValue (not boolean) : rest)
executeCommand (top : rest) Pop = Just (Returned top, rest)
executeCommand _ _ = Nothing

-- | Forget a concrete response value while retaining its QSM response space.
responseType :: ActualResponse -> Response
responseType Completed = Accepted
responseType (Returned returned) = Popped $ valueType returned

-- | Select one known non-empty alternative set.
oneofOrDie :: String -> [LTA.LTAGen a] -> LTA.LTAGen a
oneofOrDie context alternatives =
    case LTA.oneof alternatives of
        Left err -> error $ context <> " is unexpectedly empty: " <> show err
        Right generator -> generator
