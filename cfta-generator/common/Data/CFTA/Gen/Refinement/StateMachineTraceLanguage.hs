{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
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

The step keeps the paper's positional guards. Each command is generated data
that carries its own input and output stack types as refinements, so a step
relates refinements, not values: the prefix's output type must be a subtype
of the command's input type. A contract relates values, and fits a fixed
operation instead, as in the sized-vector language.
-}
module Data.CFTA.Gen.Refinement.StateMachineTraceLanguage (
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
    variable,
    stateRefinement,
    solverAssumptions,
    tracesOfLength,
    traceAutomaton,
    compileTracesOfLength,
    compileTraceAutomaton,
    tracesUpTo,
    naiveTraceGen,
    qsmTraceGen,
    qsmTraceShrinks,
    handwrittenTraceGen,
    rankedTraceGen,
    traceCount,
    modelStep,
    replayTrace,
    executeTrace,
    traceIsValid,
) where

import Control.Monad (foldM, guard)
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe)
import Data.String (fromString)
import qualified Test.QuickCheck as QC

import Data.CFTA.Formula (conjunction, disjunction)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Gen.TypedExpressionLanguage (frequencyInteger)
import Data.CFTA.Refinement (
    Automaton,
    AutomatonError,
    Constraint,
    Entailment,
    Formula,
    Node (Node),
    Symbol (..),
    noConstraint,
    validate,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (refinementFormula, variable, (.<=), (.==), (.>=))
import Data.CFTA.Refinement.Guard (
    Path,
    allOf,
    argument,
    descendant,
    isSubtypeOf,
    root,
    withActualFor,
 )
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

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

{- | The largest stack depth. The trace languages contain only stacks up to
this depth.
-}
maximumStackDepth :: Int
maximumStackDepth = 3

-- | Encode a type stack as a binary cons-list with the top in the low bits.
encodeState :: StackState -> Int
encodeState (StackState types) = foldr encodeType 0 types
  where
    encodeType type_ rest = 2 * rest + typeTag type_

-- | Give one stack state an exact symbolic refinement.
stateRefinement :: StackState -> Formula
stateRefinement state = refinementFormula (.== variable (stateName state))

-- | Facts assigning each finite stack shape its compact integer encoding.
solverAssumptions :: [Formula]
solverAssumptions =
    [ variable (stateName state) .== fromIntegral (encodeState state)
    | state <- stackStates
    ]

-- | Internal difference-list form used while composing trace generators.
data TracePrefix = TracePrefix
    { prefixEvents :: [Event] -> [Event]
    , prefixFinalState :: !StackState
    }

-- | Empty trace prefix before the public value is decoded.
initialTracePrefix :: LTAGen.LTAGen TracePrefix
initialTracePrefix =
    LTAGen.refinedNode "start" (const $ stateRefinement emptyState) noConstraint start
  where
    start = LTAGen.pure (TracePrefix id emptyState) :: LTAGen.LTAGen TracePrefix

{- | Generate the traces of exactly the given number of commands with the
generator combinators.

The benchmark cell @lta-do@ measures this generator. 'compileTracesOfLength'
keeps its applicative recipe and groups the prefixes by the refinement of
their output state, so it does not enumerate the product of prefixes and
commands.
-}
tracesOfLength :: Int -> LTAGen.LTAGen Trace
tracesOfLength = fmap finishTracePrefix . tracePrefixesOfLength

-- | Build exact-length prefixes without repeatedly appending event lists.
tracePrefixesOfLength :: Int -> LTAGen.LTAGen TracePrefix
tracePrefixesOfLength length_
    | length_ <= 0 = initialTracePrefix
    | otherwise = extendTrace $ tracePrefixesOfLength (length_ - 1)

-- | Decode the internal difference-list representation once at the root.
finishTracePrefix :: TracePrefix -> Trace
finishTracePrefix TracePrefix{prefixEvents, prefixFinalState} =
    Trace (prefixEvents []) prefixFinalState

{- | Build the unpruned LTA for one exact trace length.

Nodes are shared by @(prefix length, output stack)@ through a lazy map. Each
candidate @step@ transition combines one preceding node, one reusable liquid
command schema, and one possible output state. The liquid guard, not the
Haskell model, decides which transitions survive. The graph grows linearly
with trace length.
-}
traceAutomaton :: Int -> Either AutomatonError Automaton
traceAutomaton requestedLength = validate rootNode >> pure rootNode
  where
    traceLength = max 0 requestedLength
    rootNode
        | traceLength == 0 = Node [start]
        | otherwise = Node $ concatMap (stepTransitions traceLength) stackStates
    start = Transition "start" (stateRefinement emptyState) [] noConstraint
    nodes =
        LazyMap.fromList $
            [ ( TraceNode prefixLength output
              , Node $
                    if prefixLength == 0
                        then [start | output == emptyState]
                        else stepTransitions prefixLength output
              )
            | prefixLength <- [0 .. traceLength - 1]
            , output <- stackStates
            ]
                <> [ (CommandNode contractRank, Node [contractTransition contractRank contract])
                   | (contractRank, contract) <- zip [0 ..] commandContractValues
                   ]
                <> [(FormalNode, Node [Transition "model" stateRange [] noConstraint])]
                <> [ ( PostNode contractRank
                     , Node [Transition "post-state" (contractPostState contract) [] noConstraint]
                     )
                   | (contractRank, contract) <- zip [0 ..] commandContractValues
                   ]

    stepTransitions prefixLength output =
        [ Transition
            "step"
            (stateRefinement output)
            [ nodes LazyMap.! TraceNode (prefixLength - 1) input
            , nodes LazyMap.! CommandNode contractRank
            ]
            (validStep (argument 0) (argument 1))
        | input <- stackStates
        , (contractRank, _) <- zip [0 ..] commandContractValues
        ]

    contractTransition contractRank contract =
        Transition
            (contractSymbol contract)
            (contractInputSpace contract)
            [nodes LazyMap.! FormalNode, nodes LazyMap.! PostNode contractRank]
            noConstraint

-- | The shared nodes of the exact-length trace LTA.
data TraceNodeKey
    = TraceNode !Int !StackState
    | CommandNode !Int
    | FormalNode
    | PostNode !Int
    deriving (Eq, Ord)

{- | Compile 'tracesOfLength' for one length.

Z3 decides each step once for each tuple of a prefix group and a command
group that has members. The compiled generator counts and unranks the
traces. Compilation does not visit complete traces.
-}
compileTracesOfLength ::
    Entailment ->
    Int ->
    IO (Either LTAGen.GenError (LTAGen.LTAGen Trace))
compileTracesOfLength entailment traceLength =
    LTAGen.compileWith entailment $ tracesOfLength traceLength

-- | Compile the finite-state trace LTA and decode its accepted terms.
compileTraceAutomaton ::
    Entailment ->
    Int ->
    IO (Either LTAGen.GenError (LTAGen.LTAGen Trace))
compileTraceAutomaton entailment traceLength =
    case traceAutomaton traceLength of
        Left err -> pure $ Left $ LTAGen.InvalidSupport err
        Right automaton ->
            LTAGen.compileWith entailment $ decodeTrace <$> LTAGen.fromAutomaton automaton
  where
    decodeTrace term =
        case traceFromLiquidTerm term of
            Just trace -> trace
            Nothing -> error "compileTraceAutomaton: invalid trace term"

-- | Constructor labels for the reusable command schemas.
commandSymbols :: [(Symbol, Command)]
commandSymbols =
    [ (contractSymbol contract, contractCommand contract)
    | contract <- commandContractValues
    ]

-- | Generate every trace up to a maximum length, shortest first for shrinking.
tracesUpTo :: Int -> LTAGen.LTAGen Trace
tracesUpTo maximumLength =
    LTAGen.oneof [tracesOfLength length_ | length_ <- [0 .. maximumLength]]

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

{- | Generate a valid trace in the usual state-machine-testing style.

The next command is chosen uniformly from those admitted by the current model,
then the model is advanced before generating the suffix. This is deliberately
not uniform over complete traces: prefixes with fewer later continuations get
more probability than they do in the exact-uniform generators. Its advantage
is that it needs neither rejection nor suffix counts.
-}
qsmTraceGen :: Int -> QC.Gen Trace
qsmTraceGen length_ = generateFrom (max 0 length_) emptyState
  where
    generateFrom 0 state = pure $ Trace [] state
    generateFrom remaining before = do
        (command, response, after) <-
            QC.elements
                [ (command, response, after)
                | command <- commandValues
                , Just (response, after) <- [modelStep before command]
                ]
        suffix <- generateFrom (remaining - 1) after
        pure $
            suffix
                { traceEvents =
                    Event before command response after : traceEvents suffix
                }

{- | Dependency-aware deletion candidates for a QSM-style failing trace.

QuickCheck-state-machine generates a complete trace before execution. On a
failure it removes commands, replays the remaining sequence from the initial
model, and retains only candidates whose preconditions still hold. This small
version has no command-local shrinker, so it isolates that structural step.
-}
qsmTraceShrinks :: Trace -> [Trace]
qsmTraceShrinks =
    mapMaybe traceFromCommands
        . QC.shrinkList (const [])
        . map eventCommand
        . traceEvents

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

{- | Uniform generation by hand, through one rank for the whole trace.

This baseline counts and unranks as the compiled LTA generator does, but it
builds the 'Trace' directly, without a liquid witness. It puts the counting
algorithm of the library into application code, so it is harder to read than
'handwrittenTraceGen'.
-}
rankedTraceGen :: Int -> QC.Gen Trace
rankedTraceGen requestedLength = do
    rank <- QC.chooseInteger (0, traceCount length_ emptyState - 1)
    pure $ decode length_ emptyState rank
  where
    length_ = max 0 requestedLength

    decode 0 state _ = Trace [] state
    decode remaining before rank =
        case select rank alternatives of
            Just (command, response, after, suffixRank) ->
                let suffix = decode (remaining - 1) after suffixRank
                 in suffix
                        { traceEvents =
                            Event before command response after : traceEvents suffix
                        }
            Nothing -> error "rankedTraceGen: rank outside the counted trace language"
      where
        alternatives =
            [ ( command
              , response
              , after
              , traceCount (remaining - 1) after
              )
            | command <- commandValues
            , Just (response, after) <- [modelStep before command]
            ]

    select _ [] = Nothing
    select rank ((command, response, after, count) : rest)
        | rank < count = Just (command, response, after, rank)
        | otherwise = select (rank - count) rest

-- | Count valid command traces of one remaining length from an abstract state.
traceCount :: Int -> StackState -> Integer
traceCount remaining before
    | remaining <= 0 = 1
    | otherwise = Map.findWithDefault 0 before $ traceCountTables !! remaining

-- | Dynamic-programming tables shared by counting and bespoke generation.
traceCountTables :: [Map.Map StackState Integer]
traceCountTables = iterate nextCounts initialCounts
  where
    initialCounts = Map.fromList [(state, 1) | state <- stackStates]
    nextCounts counts =
        Map.fromList
            [ ( state
              , sum
                    [ Map.findWithDefault 0 after counts
                    | command <- commandValues
                    , Just (_, after) <- [modelStep state command]
                    ]
              )
            | state <- stackStates
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

-- | Decode one accepted liquid witness into the ordinary QSM trace value.
traceFromLiquidTerm :: Term Symbol -> Maybe Trace
traceFromLiquidTerm (Term.Node (RefinedSymbol "start" liquidRefinement) [])
    | liquidRefinement == stateRefinement emptyState = Just initialTraceValue
traceFromLiquidTerm (Term.Node (RefinedSymbol "step" liquidRefinement) [previousTerm, commandTerm]) = do
    previous <- traceFromLiquidTerm previousTerm
    command <- commandFromLiquidTerm commandTerm
    let before = traceFinalState previous
    (response, after) <- modelStep before command
    guard $ liquidRefinement == stateRefinement after
    pure $
        Trace
            (traceEvents previous <> [Event before command response after])
            after
traceFromLiquidTerm _ = Nothing

-- | Recover the command represented by one reusable liquid schema.
commandFromLiquidTerm :: Term Symbol -> Maybe Command
commandFromLiquidTerm (Term.Node (RefinedSymbol liquidSymbol _) [_, _]) =
    lookup
        liquidSymbol
        [ (contractSymbol contract, contractCommand contract)
        | contract <- commandContractValues
        ]
commandFromLiquidTerm _ = Nothing

-- | Concrete value represented by the nullary initial transition.
initialTraceValue :: Trace
initialTraceValue = Trace [] emptyState

-- | Every distinct raw command value in the example alphabet.
commandValues :: [Command]
commandValues = map Push literalValues <> [Add, And, Equal, Not, Pop]

{- | Advance the pure abstract model when a command's stack type permits it.

This function is deliberately independent of the LTA guard. The specs replay
all accepted witnesses through it so a mistake in the liquid encoding cannot
silently accept an invalid trace.
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

The LTA has only abstract stack types. This interpreter has integer and
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
extendTrace :: LTAGen.LTAGen TracePrefix -> LTAGen.LTAGen TracePrefix
extendTrace previousTraces =
    LTAGen.refinedNodeByRoots
        "step"
        (const . stepRefinementFromRoots)
        validStep
        $ LTAGen.do
            previous <- previousTraces
            command <- commandContracts
            LTAGen.pure $ predictPrefixStep previous command

-- | Compute the next state tag from the two direct child relation groups.
stepRefinementFromRoots :: [Symbol] -> Formula
stepRefinementFromRoots [RefinedSymbol _ previous, RefinedSymbol command _] =
    case (stateForRefinement previous, lookup command commandSymbols) of
        (Just before, Just selectedCommand) ->
            case modelStep before selectedCommand of
                Just (_, after) -> stateRefinement after
                Nothing -> stateRefinement before
        _ -> error "stepRefinementFromRoots: malformed trace relation group"
stepRefinementFromRoots _ =
    error "stepRefinementFromRoots: a step must have previous-trace and command children"

-- | Recover the finite stack state represented by one exact root refinement.
stateForRefinement :: Formula -> Maybe StackState
stateForRefinement refinement =
    lookup refinement [(stateRefinement state, state) | state <- stackStates]

{- | Check one dependent state transition.

The previous trace root is both the selected input state and the actual value
substituted for the command's formal @model@. The command's post-state formula
must then imply the new trace root. The guard takes the two child paths as
arguments, so 'refinedNodeByRoots' and a 'Transition' can both use it.
-}
validStep :: Path -> Path -> Constraint
validStep previous command =
    allOf
        [ previous `isSubtypeOf` command
        , withActualFor previous (descendant command [0]) $
            descendant command [1] `isSubtypeOf` root
        ]

-- | Extend a trace prefix in O(1), using a placeholder for rejected candidates.
predictPrefixStep :: TracePrefix -> Command -> TracePrefix
predictPrefixStep previous command =
    let before = prefixFinalState previous
        (response, after) = fromMaybe (Accepted, before) (modelStep before command)
     in TracePrefix
            (prefixEvents previous . (Event before command response after :))
            after

{- | Dependent command contracts over the formal input state @model@.

Each command root is its admissible input-state space. Child zero names the
formal input; child one is the output-state refinement. The command alternatives
are schemas, not one transition per concrete pair of stack states.
-}
commandContracts :: LTAGen.LTAGen Command
commandContracts =
    LTAGen.oneof (map contractGenerator commandContractValues)

-- | One reusable liquid input/output schema for a stack-machine command.
data CommandContract = CommandContract
    { contractSymbol :: !Symbol
    , contractCommand :: !Command
    , contractInputSpace :: !Formula
    , contractPostState :: !Formula
    }

-- | The eleven schemas from which every trace layer is constructed.
commandContractValues :: [CommandContract]
commandContractValues =
    map pushContract literalValues
        <> [ popContract TInt
           , popContract TBool
           , CommandContract "add" Add (stacksStartingWith [TInt, TInt]) popIntOutput
           , CommandContract "and" And (stacksStartingWith [TBool, TBool]) popBoolOutput
           , CommandContract "equal-int" Equal (stacksStartingWith [TInt, TInt]) equalIntOutput
           , CommandContract "equal-bool" Equal (stacksStartingWith [TBool, TBool]) equalBoolOutput
           , CommandContract "not" Not (stacksStartingWith [TBool]) unchangedOutput
           ]

-- | Build the dependent transition contract for one pushed literal.
pushContract :: Value -> CommandContract
pushContract pushed =
    CommandContract
        (fromString $ "push-" <> valueName pushed)
        (Push pushed)
        stacksWithRoom
        (refinementFormula (.== 2 * variable "model" + fromIntegral (typeTag (valueType pushed))))

-- | Build one of the two typed pop transition contracts.
popContract :: ValueType -> CommandContract
popContract type_ =
    CommandContract
        (fromString $ "pop-" <> typeName type_)
        Pop
        (stacksStartingWith [type_])
        (popOutput type_)

-- | Output relation for removing one leading stack-type tag.
popOutput :: ValueType -> Formula
popOutput TInt = popIntOutput
popOutput TBool = popBoolOutput

-- | Present one command schema through the compositional generator DSL.
contractGenerator :: CommandContract -> LTAGen.LTAGen Command
contractGenerator CommandContract{contractSymbol, contractCommand, contractInputSpace, contractPostState} =
    LTAGen.refinedNode contractSymbol (const contractInputSpace) noConstraint $ LTAGen.do
        _formalState <- LTAGen.leaf () "model" (const stateRange)
        _postState <- LTAGen.leaf () "post-state" (const contractPostState)
        LTAGen.pure contractCommand

-- | States in which another value can be pushed.
stacksWithRoom :: Formula
stacksWithRoom = oneOfStates ((< maximumStackDepth) . length . stackTypes)

-- | States whose top prefix has the requested sequence of types.
stacksStartingWith :: [ValueType] -> Formula
stacksStartingWith prefix = oneOfStates (prefix `isPrefixOf`)
  where
    isPrefixOf expected state = expected == take (length expected) (stackTypes state)

-- | Describe a non-empty subset of the bounded abstract state space.
oneOfStates :: (StackState -> Bool) -> Formula
oneOfStates predicate =
    disjunction
        [ refinementFormula (.== fromIntegral (encodeState state))
        | state <- stackStates
        , predicate state
        ]

-- | The bounded range accepted at the command's formal state position.
stateRange :: Formula
stateRange =
    conjunction
        [ refinementFormula (.>= 0)
        , refinementFormula (.<= fromIntegral maximumEncodedState)
        ]

-- | @Add@ and @Pop Int@ both remove one leading integer tag.
popIntOutput :: Formula
popIntOutput = refinementFormula (\v -> variable "model" .== 2 * v + 1)

-- | @And@ and @Pop Bool@ both remove one leading Boolean tag.
popBoolOutput :: Formula
popBoolOutput = refinementFormula (\v -> variable "model" .== 2 * v + 2)

-- | Replacing two integers with a Boolean relates input to output by this law.
equalIntOutput :: Formula
equalIntOutput = refinementFormula (\v -> variable "model" .== 2 * v - 1)

-- | Replacing two Booleans with one Boolean relates input and output by this law.
equalBoolOutput :: Formula
equalBoolOutput = refinementFormula (\v -> variable "model" .== 2 * v + 2)

-- | Operations such as Boolean negation preserve the complete stack type.
unchangedOutput :: Formula
unchangedOutput = refinementFormula (.== variable "model")

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
