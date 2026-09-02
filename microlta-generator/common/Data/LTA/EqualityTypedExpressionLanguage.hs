{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

{- | The ECTA flagship typed-expression language represented as an LTA.

Ground types become equality refinements over Liquid Fixpoint's distinguished
value variable. Candidate application transitions contain every ground child
state; guards require the children to imply the operation's expected input
types. Pruning with Z3 therefore performs the same compatibility check as the
ECTA's path equalities, while the accepted expression language stays identical.
-}
module Data.LTA.EqualityTypedExpressionLanguage (
    typeEquality,
    solverDeclarations,
    equalityExpressionAutomaton,
    compileEqualityExpressionsAtDepth,
) where

import qualified Language.Fixpoint.Types as Fixpoint

import Data.ECTA.TypedExpressionLanguage (
    BinaryFunctionInstance (..),
    Expression (..),
    Function (..),
    Type (..),
    TypedExpression (..),
    allTypes,
    binaryFunctionInstances,
 )
import Data.LTA (
    Automaton,
    AutomatonError,
    Entailment,
    Guard (Top),
    LiquidTerm (..),
    Refinement,
    State (State),
    Symbol,
    Transition,
    mkAutomaton,
    pattern Transition,
 )
import qualified Data.LTA.Gen as LTA
import Data.LTA.Guard (allOf, argument, requires)
import Data.LTA.Refinement ((.==.))

-- | Encode one ground type as an exact integer equality refinement.
typeEquality :: Type -> Refinement
typeEquality type_ = value .==. typeTag type_

-- | Free integer symbols used by the equality refinements.
solverDeclarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
solverDeclarations = [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)]

-- | Build the exact-depth typed-expression language as a guarded LTA.
equalityExpressionAutomaton :: Int -> Either AutomatonError Automaton
equalityExpressionAutomaton requestedDepth =
    mkAutomaton initialState $ rootRow : childRows
  where
    depth = max 0 requestedDepth
    initialState = State 0
    rootRow =
        ( initialState
        , concatMap (expressionTransitions depth) allTypes
        )
    childRows =
        [ (expressionState childDepth result, expressionTransitions childDepth result)
        | childDepth <- [0 .. depth - 1]
        , result <- allTypes
        ]

-- | Compile and decode one exact-depth equality-refined expression language.
compileEqualityExpressionsAtDepth ::
    Entailment ->
    Int ->
    IO (Either LTA.GeneratorError (LTA.Compiled TypedExpression))
compileEqualityExpressionsAtDepth entailment depth =
    case equalityExpressionAutomaton depth of
        Left err -> pure $ Left $ LTA.InvalidSupport err
        Right automaton ->
            fmap (fmap $ LTA.mapCompiled decodeExpression) $
                LTA.compileAutomaton entailment automaton
  where
    decodeExpression term =
        case expressionFromLiquidTerm term of
            Just expression -> expression
            Nothing ->
                error
                    "compileEqualityExpressionsAtDepth: pruned LTA produced an invalid expression"

-- | Candidate transitions for one exact depth and result-type state.
expressionTransitions :: Int -> Type -> [Transition]
expressionTransitions 0 result = literalTransitions result
expressionTransitions depth result =
    unaryTransitions childDepth result
        <> binaryTransitions childDepth result
        <> conditionalTransitions childDepth result
  where
    childDepth = depth - 1

-- | The two literal leaves inhabiting each ground type.
literalTransitions :: Type -> [Transition]
literalTransitions TInt =
    [ Transition "int-0" (typeEquality TInt) [] Top
    , Transition "int-1" (typeEquality TInt) [] Top
    ]
literalTransitions TBool =
    [ Transition "bool-false" (typeEquality TBool) [] Top
    , Transition "bool-true" (typeEquality TBool) [] Top
    ]

-- | Every actual child type; the liquid guard keeps only Boolean arguments.
unaryTransitions :: Int -> Type -> [Transition]
unaryTransitions childDepth result =
    [ Transition
        "not"
        (typeEquality TBool)
        [expressionState childDepth actual]
        (argument 0 `requires` typeEquality TBool)
    | result == TBool
    , actual <- allTypes
    ]

-- | Every actual child-type pair checked against each ground function instance.
binaryTransitions :: Int -> Type -> [Transition]
binaryTransitions childDepth result =
    [ Transition
        (functionSymbol $ binaryFunction instance_)
        (typeEquality result)
        [ expressionState childDepth actualFirst
        , expressionState childDepth actualSecond
        ]
        ( allOf
            [ argument 0 `requires` typeEquality (firstArgumentType instance_)
            , argument 1 `requires` typeEquality (secondArgumentType instance_)
            ]
        )
    | instance_ <- binaryFunctionInstances
    , binaryResultType instance_ == result
    , actualFirst <- allTypes
    , actualSecond <- allTypes
    ]

-- | Every actual child-type triple checked against the conditional signature.
conditionalTransitions :: Int -> Type -> [Transition]
conditionalTransitions childDepth result =
    [ Transition
        "if"
        (typeEquality result)
        [ expressionState childDepth actualCondition
        , expressionState childDepth actualTrue
        , expressionState childDepth actualFalse
        ]
        ( allOf
            [ argument 0 `requires` typeEquality TBool
            , argument 1 `requires` typeEquality result
            , argument 2 `requires` typeEquality result
            ]
        )
    | actualCondition <- allTypes
    , actualTrue <- allTypes
    , actualFalse <- allTypes
    ]

-- | Stable state identity for one exact-depth, ground-type sublanguage.
expressionState :: Int -> Type -> State
expressionState depth result = State $ 1 + 2 * depth + fromEnum result

-- | Liquid Fixpoint's distinguished value variable.
value :: Fixpoint.Expr
value = Fixpoint.EVar $ Fixpoint.symbol ("v" :: String)

-- | Stable integer tag for a ground type.
typeTag :: Type -> Int
typeTag TInt = 0
typeTag TBool = 1

-- | Symbol representing one binary function constructor.
functionSymbol :: Function -> Symbol
functionSymbol Equal = "equal"
functionSymbol Add = "add"
functionSymbol Multiply = "multiply"
functionSymbol Or = "or"
functionSymbol And = "and"

-- | Decode one accepted liquid witness to the canonical expression value.
expressionFromLiquidTerm :: LiquidTerm -> Maybe TypedExpression
expressionFromLiquidTerm LiquidTerm{liquidSymbol = "int-0", liquidChildren = []} =
    Just $ TypedExpression TInt $ IntLiteral 0
expressionFromLiquidTerm LiquidTerm{liquidSymbol = "int-1", liquidChildren = []} =
    Just $ TypedExpression TInt $ IntLiteral 1
expressionFromLiquidTerm LiquidTerm{liquidSymbol = "bool-false", liquidChildren = []} =
    Just $ TypedExpression TBool $ BoolLiteral False
expressionFromLiquidTerm LiquidTerm{liquidSymbol = "bool-true", liquidChildren = []} =
    Just $ TypedExpression TBool $ BoolLiteral True
expressionFromLiquidTerm LiquidTerm{liquidSymbol = "not", liquidChildren = [operand]} = do
    decoded <- expressionFromLiquidTerm operand
    pure $ TypedExpression TBool $ Not $ expression decoded
expressionFromLiquidTerm LiquidTerm{liquidSymbol, liquidRefinement, liquidChildren = [first, second]}
    | Just function_ <- functionFromSymbol liquidSymbol = do
        result <- typeFromRefinement liquidRefinement
        decodedFirst <- expressionFromLiquidTerm first
        decodedSecond <- expressionFromLiquidTerm second
        pure $
            TypedExpression result $
                ApplyBinary function_ (expression decodedFirst) (expression decodedSecond)
expressionFromLiquidTerm LiquidTerm{liquidSymbol = "if", liquidRefinement, liquidChildren = [condition, ifTrue, ifFalse]} = do
    result <- typeFromRefinement liquidRefinement
    decodedCondition <- expressionFromLiquidTerm condition
    decodedTrue <- expressionFromLiquidTerm ifTrue
    decodedFalse <- expressionFromLiquidTerm ifFalse
    pure $
        TypedExpression result $
            IfExpression
                (expression decodedCondition)
                (expression decodedTrue)
                (expression decodedFalse)
expressionFromLiquidTerm _ = Nothing

-- | Recover a binary function from its liquid constructor symbol.
functionFromSymbol :: Symbol -> Maybe Function
functionFromSymbol "equal" = Just Equal
functionFromSymbol "add" = Just Add
functionFromSymbol "multiply" = Just Multiply
functionFromSymbol "or" = Just Or
functionFromSymbol "and" = Just And
functionFromSymbol _ = Nothing

-- | Recover the ground result type encoded by a refinement.
typeFromRefinement :: Refinement -> Maybe Type
typeFromRefinement refinement
    | refinement == typeEquality TInt = Just TInt
    | refinement == typeEquality TBool = Just TBool
    | otherwise = Nothing
