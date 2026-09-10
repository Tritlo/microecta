{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE QualifiedDo #-}

{- | The ordinary-FTA member of the three-example progression.

There is only one implicit sort: every expression is an integer. An FTA needs
to describe constructor shape, but it does not need to relate annotations on
different paths. The ECTA flagship adds integer and Boolean result types to
this syntax; the LTA flagship then carries those types through state-machine
transitions.
-}
module Data.Tree.FTA.UntypedExpressionLanguage (
    Expression (..),
    literals,
    binaryLayer,
    expressionsAtDepth,
    expressionsUpToDepth,
    expressionCount,
    evaluate,
    naiveExpressionGen,
    handwrittenExpressionGen,
) where

import qualified Test.QuickCheck as QC

import qualified Data.Tree.FTA as Automaton
import qualified Data.Tree.FTA.Gen.QuickCheck as FTA
import Data.Tree.Term (Term (Term))

-- | Integer expressions with no explicit type annotation.
data Expression
    = Literal !Int
    | Add !Expression !Expression
    | Multiply !Expression !Expression
    deriving (Eq, Ord, Show)

-- | The two ground terms shared with the later examples.
literals :: FTA.FTAGen String Expression
literals =
    oneofOrDie
        "integer literals"
        [ FTA.leaf "zero" $ Literal 0
        , FTA.leaf "one" $ Literal 1
        ]

-- | Add one ordinary binary-constructor layer.
binaryLayer :: FTA.FTAGen String Expression -> FTA.FTAGen String Expression
binaryLayer children =
    oneofOrDie
        "integer operations"
        [ FTA.node "add" $ FTA.do
            left <- children
            right <- children
            FTA.pure $ Add left right
        , FTA.node "multiply" $ FTA.do
            left <- children
            right <- children
            FTA.pure $ Multiply left right
        ]

-- | Full expression trees with exactly the requested constructor depth.
expressionsAtDepth :: Int -> FTA.FTAGen String Expression
expressionsAtDepth depth
    | depth <= 0 = literals
    | otherwise = binaryLayer $ expressionsAtDepth (depth - 1)

-- | Expressions at every depth up to the requested finite boundary.
expressionsUpToDepth :: Int -> FTA.FTAGen String Expression
expressionsUpToDepth maximumDepth =
    oneofOrDie
        "bounded integer expressions"
        [ expressionsAtDepth depth
        | depth <- [0 .. maximumDepth]
        ]

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

There is no semantic side condition in this example, so every ranked candidate
is accepted. That zero-rejection case is the honest naive baseline for an FTA:
it measures the cost of generating a generic tree and recognizing it rather
than manufacturing an irrelevant predicate.
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
                [ Automaton.Transition "zero" [] ()
                , Automaton.Transition "one" [] ()
                , Automaton.Transition "add" [(), ()] ()
                , Automaton.Transition "multiply" [(), ()] ()
                ]
            )
        ] of
        Left err -> error $ "invalid expression FTA: " <> show err
        Right automaton -> automaton

-- | Generate a generic ranked term at one exact depth.
genericTermAtDepth :: Int -> QC.Gen (Term String)
genericTermAtDepth depth
    | depth <= 0 = QC.elements [Term "zero" [], Term "one" []]
    | otherwise = do
        symbol <- QC.elements ["add", "multiply"]
        left <- genericTermAtDepth $ depth - 1
        right <- genericTermAtDepth $ depth - 1
        pure $ Term symbol [left, right]

-- | Decode a recognized generic term into the example datatype.
expressionFromTerm :: Term String -> Maybe Expression
expressionFromTerm (Term "zero" []) = Just $ Literal 0
expressionFromTerm (Term "one" []) = Just $ Literal 1
expressionFromTerm (Term "add" [left, right]) =
    Add <$> expressionFromTerm left <*> expressionFromTerm right
expressionFromTerm (Term "multiply" [left, right]) =
    Multiply <$> expressionFromTerm left <*> expressionFromTerm right
expressionFromTerm _ = Nothing

-- | Select one known non-empty alternative set.
oneofOrDie :: String -> [FTA.FTAGen String a] -> FTA.FTAGen String a
oneofOrDie context alternatives =
    case FTA.oneof alternatives of
        Left err -> error $ context <> " is unexpectedly empty: " <> show err
        Right generator -> generator
