{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

{- | The ECTA flagship typed-expression language represented as an LTA.

Ground types become equality refinements over Liquid Fixpoint's distinguished
value variable. Candidate application transitions contain every ground child
state; guards require the children to imply the operation's expected input
types. Pruning with Z3 therefore performs the same compatibility check as the
ECTA's path equalities, while the accepted expression language stays identical.
-}
module Data.CFTA.Gen.Refinement.EqualityTypedExpressionLanguage (
    typeEquality,
    solverDeclarations,
    equalityExpressionAutomaton,
    compileEqualityExpressionsAtDepth,
) where

import qualified Data.Map.Lazy as LazyMap
import qualified Data.Tree as Tree
import qualified Language.Fixpoint.Types as Fixpoint

import qualified Data.CFTA.Gen.Refinement as LTA
import Data.CFTA.Gen.TypedExpressionLanguage (
    BinaryFunctionInstance (..),
    Expression (..),
    Function (..),
    Type (..),
    TypedExpression (..),
    allTypes,
    binaryFunctionInstances,
 )
import Data.CFTA.Refinement (
    Automaton,
    AutomatonError,
    Entailment,
    LiquidSymbol (..),
    Node (Node),
    Refinement,
    Symbol,
    Transition,
    unconstrainedConstraint,
    validate,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (value, (.==.))
import Data.CFTA.Refinement.Guard (allOf, argument, requires)

-- | Encode one ground type as an exact integer equality refinement.
typeEquality :: Type -> Refinement
typeEquality type_ = value .==. typeTag type_

-- | Free integer symbols used by the equality refinements.
solverDeclarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
solverDeclarations = [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)]

{- | Build the exact-depth typed-expression language as a guarded LTA.

The nodes of each exact depth and ground type are shared through a lazy map,
so the graph grows linearly with the depth.
-}
equalityExpressionAutomaton :: Int -> Either AutomatonError Automaton
equalityExpressionAutomaton requestedDepth = validate root >> pure root
  where
    depth = max 0 requestedDepth
    root = Node $ concatMap (expressionTransitions expressionNode depth) allTypes
    nodes =
        LazyMap.fromList
            [ ((childDepth, result), Node $ expressionTransitions expressionNode childDepth result)
            | childDepth <- [0 .. depth - 1]
            , result <- allTypes
            ]
    expressionNode childDepth result = nodes LazyMap.! (childDepth, result)

-- | Compile and decode one exact-depth equality-refined expression language.
compileEqualityExpressionsAtDepth ::
    Entailment ->
    Int ->
    IO (Either LTA.GenError (LTA.LTAGen TypedExpression))
compileEqualityExpressionsAtDepth entailment depth =
    case equalityExpressionAutomaton depth of
        Left err -> pure $ Left $ LTA.InvalidSupport err
        Right automaton ->
            LTA.compile entailment $ decodeExpression <$> LTA.fromAutomaton automaton
  where
    decodeExpression term =
        case expressionFromLiquidTerm term of
            Just expression -> expression
            Nothing ->
                error
                    "compileEqualityExpressionsAtDepth: pruned LTA produced an invalid expression"

-- | The node of one exact depth and ground type.
type ExpressionNode = Int -> Type -> Automaton

-- | Candidate transitions for one exact depth and result type.
expressionTransitions :: ExpressionNode -> Int -> Type -> [Transition]
expressionTransitions _ 0 result = literalTransitions result
expressionTransitions expressionNode depth result =
    unaryTransitions expressionNode childDepth result
        <> binaryTransitions expressionNode childDepth result
        <> conditionalTransitions expressionNode childDepth result
  where
    childDepth = depth - 1

-- | The two literal leaves inhabiting each ground type.
literalTransitions :: Type -> [Transition]
literalTransitions TInt =
    [ Transition "int-0" (typeEquality TInt) [] unconstrainedConstraint
    , Transition "int-1" (typeEquality TInt) [] unconstrainedConstraint
    ]
literalTransitions TBool =
    [ Transition "bool-false" (typeEquality TBool) [] unconstrainedConstraint
    , Transition "bool-true" (typeEquality TBool) [] unconstrainedConstraint
    ]

-- | Every actual child type; the liquid guard keeps only Boolean arguments.
unaryTransitions :: ExpressionNode -> Int -> Type -> [Transition]
unaryTransitions expressionNode childDepth result =
    [ Transition
        "not"
        (typeEquality TBool)
        [expressionNode childDepth actual]
        (argument 0 `requires` typeEquality TBool)
    | result == TBool
    , actual <- allTypes
    ]

-- | Every actual child-type pair checked against each ground function instance.
binaryTransitions :: ExpressionNode -> Int -> Type -> [Transition]
binaryTransitions expressionNode childDepth result =
    [ Transition
        (functionSymbol $ binaryFunction instance_)
        (typeEquality result)
        [ expressionNode childDepth actualFirst
        , expressionNode childDepth actualSecond
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
conditionalTransitions :: ExpressionNode -> Int -> Type -> [Transition]
conditionalTransitions expressionNode childDepth result =
    [ Transition
        "if"
        (typeEquality result)
        [ expressionNode childDepth actualCondition
        , expressionNode childDepth actualTrue
        , expressionNode childDepth actualFalse
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
expressionFromLiquidTerm :: Tree.Tree LiquidSymbol -> Maybe TypedExpression
expressionFromLiquidTerm (Tree.Node (LiquidSymbol "int-0" _) []) =
    Just $ TypedExpression TInt $ IntLiteral 0
expressionFromLiquidTerm (Tree.Node (LiquidSymbol "int-1" _) []) =
    Just $ TypedExpression TInt $ IntLiteral 1
expressionFromLiquidTerm (Tree.Node (LiquidSymbol "bool-false" _) []) =
    Just $ TypedExpression TBool $ BoolLiteral False
expressionFromLiquidTerm (Tree.Node (LiquidSymbol "bool-true" _) []) =
    Just $ TypedExpression TBool $ BoolLiteral True
expressionFromLiquidTerm (Tree.Node (LiquidSymbol "not" _) [operand]) = do
    decoded <- expressionFromLiquidTerm operand
    pure $ TypedExpression TBool $ Not $ expression decoded
expressionFromLiquidTerm (Tree.Node (LiquidSymbol liquidSymbol liquidRefinement) [first, second])
    | Just function_ <- functionFromSymbol liquidSymbol = do
        result <- typeFromRefinement liquidRefinement
        decodedFirst <- expressionFromLiquidTerm first
        decodedSecond <- expressionFromLiquidTerm second
        pure
            $ TypedExpression result
            $ ApplyBinary function_ (expression decodedFirst) (expression decodedSecond)
expressionFromLiquidTerm (Tree.Node (LiquidSymbol "if" liquidRefinement) [condition, ifTrue, ifFalse]) = do
    result <- typeFromRefinement liquidRefinement
    decodedCondition <- expressionFromLiquidTerm condition
    decodedTrue <- expressionFromLiquidTerm ifTrue
    decodedFalse <- expressionFromLiquidTerm ifFalse
    pure
        $ TypedExpression result
        $ IfExpression
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
