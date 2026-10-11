{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE QualifiedDo #-}

{- | Untyped integer expressions: the FTA example of the three example
languages.

Every expression is an integer, so the language has one sort. An FTA describes
the shape of the constructors and relates no annotations on different paths.
The ECTA example, "Data.CFTA.Gen.TypedExpressionLanguage", adds integer and
Boolean result types. The LTA example,
"Data.CFTA.Gen.Refinement.StateMachineTraceLanguage", carries these types
through the transitions of a state machine.
-}
module Data.CFTA.Gen.UntypedExpressionLanguage (
    Expression (..),
    literals,
    binaryLayer,
    expressionsAtDepth,
    expressionCount,
    evaluate,
    naiveExpressionGen,
    handwrittenExpressionGen,
) where

import qualified Test.QuickCheck as QC

import qualified Data.CFTA as Automaton
import Data.CFTA.Constraint (noConstraint)
import qualified Data.CFTA.Gen.QuickCheck as FTAGen
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | Integer expressions with no explicit type annotation.
data Expression
    = Literal !Int
    | Add !Expression !Expression
    | Multiply !Expression !Expression
    deriving (Eq, Ord, Show)

-- | The two ground terms shared with the later examples.
literals :: FTAGen.FTAGen String Expression
literals =
    FTAGen.oneof
        [ FTAGen.leaf (Literal 0) "zero"
        , FTAGen.leaf (Literal 1) "one"
        ]

-- | Add one ordinary binary-constructor layer.
binaryLayer :: FTAGen.FTAGen String Expression -> FTAGen.FTAGen String Expression
binaryLayer children =
    FTAGen.oneof
        [ FTAGen.node "add" $ FTAGen.do
            left <- children
            right <- children
            FTAGen.pure $ Add left right
        , FTAGen.node "multiply" $ FTAGen.do
            left <- children
            right <- children
            FTAGen.pure $ Multiply left right
        ]

-- | Full expression trees with exactly the requested constructor depth.
expressionsAtDepth :: Int -> FTAGen.FTAGen String Expression
expressionsAtDepth depth
    | depth <= 0 = literals
    | otherwise = binaryLayer $ expressionsAtDepth (depth - 1)

-- | Exact number of full expressions at one constructor depth.
expressionCount :: Int -> Integer
expressionCount depth
    | depth <= 0 = 2
    | otherwise = 2 * expressionCount (depth - 1) ^ (2 :: Int)

-- | Interpret an integer expression.
evaluate :: Expression -> Int
evaluate (Literal integer) = integer
evaluate (Add left right) = evaluate left + evaluate right
evaluate (Multiply left right) = evaluate left * evaluate right

{- | Generate generic trees, recognize them with an ordinary FTA, and only then
decode them as expressions.

This example has no semantic condition, so the FTA accepts every candidate.
This generator is the naive baseline for an FTA: it measures the cost to
generate a generic tree and to recognize it.
-}
naiveExpressionGen :: Int -> QC.Gen Expression
naiveExpressionGen depth =
    QC.suchThatMap
        (genericTermAtDepth depth)
        ( \term ->
            if Automaton.accepts expressionAutomaton term
                then expressionFromTerm term
                else Nothing
        )

-- | Generate the same exact-depth language directly as a Haskell datatype.
handwrittenExpressionGen :: Int -> QC.Gen Expression
handwrittenExpressionGen depth
    | depth <= 0 = QC.elements [Literal 0, Literal 1]
    | otherwise = do
        constructor <- QC.elements [Add, Multiply]
        left <- handwrittenExpressionGen $ depth - 1
        right <- handwrittenExpressionGen $ depth - 1
        pure $ constructor left right

-- | One-state recognizer for the untyped expression language.
expressionAutomaton :: Automaton.PlainFTA () String
expressionAutomaton =
    case Automaton.mkFTA
        ()
        [
            ( ()
            ,
                [ Automaton.Transition "zero" [] noConstraint
                , Automaton.Transition "one" [] noConstraint
                , Automaton.Transition "add" [(), ()] noConstraint
                , Automaton.Transition "multiply" [(), ()] noConstraint
                ]
            )
        ] of
        Left err -> error $ "invalid expression FTA: " <> show err
        Right automaton -> automaton

-- | Generate a generic ranked term at one exact depth.
genericTermAtDepth :: Int -> QC.Gen (Term String)
genericTermAtDepth depth
    | depth <= 0 = QC.elements [Term.Node "zero" [], Term.Node "one" []]
    | otherwise = do
        symbol <- QC.elements ["add", "multiply"]
        left <- genericTermAtDepth $ depth - 1
        right <- genericTermAtDepth $ depth - 1
        pure $ Term.Node symbol [left, right]

-- | Decode a recognized generic term into the example datatype.
expressionFromTerm :: Term String -> Maybe Expression
expressionFromTerm (Term.Node "zero" []) = Just $ Literal 0
expressionFromTerm (Term.Node "one" []) = Just $ Literal 1
expressionFromTerm (Term.Node "add" [left, right]) =
    Add <$> expressionFromTerm left <*> expressionFromTerm right
expressionFromTerm (Term.Node "multiply" [left, right]) =
    Multiply <$> expressionFromTerm left <*> expressionFromTerm right
expressionFromTerm _ = Nothing
