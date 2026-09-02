{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}

{- | The typed expression language with information-flow labels.

Every expression carries a security 'Label' as well as a ground 'Type', and
the two ride together in the grouping key. Binary applications join their
argument labels; a conditional additionally joins the condition's label into
its result, so implicit flows through control decisions are tracked, not just
direct data flows. A program prints one expression: the permissive @print@
propagates its argument's label, while the enforcing @print@ only admits
'Public' arguments, so a leaking program is unrepresentable rather than
rejected.
-}
module Data.ECTA.IFCExpressionLanguage (
    -- * Labels
    Label (..),
    allLabels,

    -- * Language
    Type (..),
    Function (..),
    Expression (..),
    LabeledExpression (..),
    Labeled,
    securityKey,
    atoms,

    -- * Generators
    atomsByKey,
    binaryLayer,
    conditionalLayer,
    applicationLayer,
    expressionsUpToDepth,
    programsUpToDepth,
    secureProgramsUpToDepth,

    -- * Exact counts
    expressionKeys,
    expressionCountUpTo,
    programCountUpToDepth,

    -- * Handwritten baseline
    handwrittenExpressionUpToDepth,
    handwrittenProgramGen,

    -- * Practical baseline
    practicalInt,
    practicalBool,
    practicalProgramGen,

    -- * Surface automaton
    surfaceExpressionNode,
    surfaceProgramNode,
    termToExpression,
) where

import qualified Data.Map.Strict as Map
import Data.String (fromString)
import qualified Test.QuickCheck as QC

import Data.ECTA (Edge (Edge), Node (EmptyNode, Node))
import Data.ECTA.Gen.QuickCheck (Grouped, Sig ((:*), (:->)))
import qualified Data.ECTA.Gen.QuickCheck as ECTAGen
import Data.ECTA.Term (Symbol, Term (Term))
import Data.ECTA.TypedExpressionLanguage (frequencyInteger)

{- | Security labels. The derived 'Ord' is the flow order, MAC's @Less@ at
the value level: @Public <= Private@ and nothing flows down. Because the
order is total, the lattice join is 'max'; a lattice with incomparable
labels would need a genuine least upper bound instead.
-}
data Label = Public | Private
    deriving (Bounded, Enum, Eq, Ord, Show)

-- | All security labels.
allLabels :: [Label]
allLabels = [minBound .. maxBound]

-- | Ground types; 'TUnit' is the type of a completed print.
data Type = TInt | TBool | TUnit
    deriving (Bounded, Enum, Eq, Ord, Show)

-- | Binary functions available to expressions, as in the base language.
data Function = Equal | Add | Multiply | Or | And
    deriving (Bounded, Enum, Eq, Ord, Show)

{- | The surface symbol of each binary function, without spacing.

One table for the 'Show' instance, which pads it, the surface automaton's edge
labels, and reading a surface term back.
-}
functionSymbol :: Function -> String
functionSymbol Equal = "=="
functionSymbol Add = "+"
functionSymbol Multiply = "*"
functionSymbol Or = "||"
functionSymbol And = "&&"

-- | Expression syntax, shown as concrete syntax for readable counterexamples.
data Expression
    = IntLiteral !Int
    | BoolLiteral !Bool
    | Variable !String
    | Not !Expression
    | ApplyBinary !Function !Expression !Expression
    | IfExpression !Expression !Expression !Expression
    | Print !Expression
    deriving (Eq, Ord)

instance Show Expression where
    showsPrec _ (IntLiteral value) = shows value
    showsPrec _ (BoolLiteral value) = shows value
    showsPrec _ (Variable name) = showString name
    showsPrec context (Not value) =
        showParen (context > 10) $
            showString "not " . showsPrec 11 value
    showsPrec context (ApplyBinary function_ first second) =
        showParen (context > 6) $
            showsPrec 7 first
                . showString (" " <> functionSymbol function_ <> " ")
                . showsPrec 7 second
    showsPrec context (IfExpression condition ifTrue ifFalse) =
        showParen (context > 0) $
            showString "if "
                . showsPrec 1 condition
                . showString " then "
                . shows ifTrue
                . showString " else "
                . shows ifFalse
    showsPrec context (Print value) =
        showParen (context > 10) $
            showString "print " . showsPrec 11 value

-- | An expression with its inferred ground type and security label.
data LabeledExpression = LabeledExpression
    { expressionType :: !Type
    , expressionLabel :: !Label
    , expression :: !Expression
    }
    deriving (Eq, Ord)

instance Show LabeledExpression where
    showsPrec context = showsPrec context . expression

-- | Type and label ride together in one grouping key.
type Labeled = (Type, Label)

-- | Project the grouping key of a labeled expression.
securityKey :: LabeledExpression -> Labeled
securityKey value = (expressionType value, expressionLabel value)

{- | Literals are 'Public'; the two variables split the lattice: @input@ is
'Public' and @secret@ is 'Private'.
-}
atoms :: [LabeledExpression]
atoms =
    [ LabeledExpression TInt Public (IntLiteral 0)
    , LabeledExpression TInt Public (IntLiteral 1)
    , LabeledExpression TBool Public (BoolLiteral False)
    , LabeledExpression TBool Public (BoolLiteral True)
    , LabeledExpression TInt Public (Variable "input")
    , LabeledExpression TInt Private (Variable "secret")
    ]

-- | Atoms grouped by type and label.
atomsByKey :: Grouped Labeled LabeledExpression
atomsByKey = ECTAGen.groupBy securityKey (ECTAGen.elements atoms)

-- | One ground-and-labeled instantiation of a binary function.
data BinaryFunctionInstance = BinaryFunctionInstance
    { binaryFunction :: !Function
    , firstArgumentKey :: !Labeled
    , secondArgumentKey :: !Labeled
    , binaryResultKey :: !Labeled
    }
    deriving (Eq, Ord, Show)

-- | Every ground instantiation, with the result label joining the arguments.
binaryFunctionInstances :: [BinaryFunctionInstance]
binaryFunctionInstances =
    [ BinaryFunctionInstance
        function_
        (firstType, firstLabel)
        (secondType, secondLabel)
        (resultType, max firstLabel secondLabel)
    | (function_, firstType, secondType, resultType) <- groundInstances
    , firstLabel <- allLabels
    , secondLabel <- allLabels
    ]
  where
    groundInstances =
        [ (Equal, TInt, TInt, TBool)
        , (Equal, TBool, TBool, TBool)
        , (Add, TInt, TInt, TInt)
        , (Multiply, TInt, TInt, TInt)
        , (Or, TBool, TBool, TBool)
        , (And, TBool, TBool, TBool)
        ]

-- | The complete signature of one binary instance.
binarySignature :: BinaryFunctionInstance -> Sig '[Labeled, Labeled] Labeled
binarySignature instance_ =
    firstArgumentKey instance_
        :* secondArgumentKey instance_
        :-> binaryResultKey instance_

-- | Binary instances grouped by their label-joining signature.
binaryFunctionsBySignature :: Grouped (Sig '[Labeled, Labeled] Labeled) BinaryFunctionInstance
binaryFunctionsBySignature =
    ECTAGen.groupBy binarySignature (ECTAGen.elements binaryFunctionInstances)

-- | Build one labeled binary application.
compileBinary :: BinaryFunctionInstance -> LabeledExpression -> LabeledExpression -> LabeledExpression
compileBinary instance_ first second =
    LabeledExpression joinedType joinedLabel $
        ApplyBinary (binaryFunction instance_) (expression first) (expression second)
  where
    (joinedType, joinedLabel) = binaryResultKey instance_

-- | Add one binary application layer.
binaryLayer :: Grouped Labeled LabeledExpression -> Grouped Labeled LabeledExpression
binaryLayer children = ECTAGen.do
    operation <- binaryFunctionsBySignature
    first <- children
    second <- children
    ECTAGen.pure (compileBinary operation first second)

-- | @not@ keeps its argument's label.
unarySignature :: Label -> Sig '[Labeled] Labeled
unarySignature label = (TBool, label) :-> (TBool, label)

-- | Build one labeled negation.
compileNot :: Label -> LabeledExpression -> LabeledExpression
compileNot label value = LabeledExpression TBool label (Not (expression value))

-- | Add one unary application layer.
unaryLayer :: Grouped Labeled LabeledExpression -> Grouped Labeled LabeledExpression
unaryLayer children = ECTAGen.do
    build <- compileNot <$> ECTAGen.groupBy unarySignature (ECTAGen.elements allLabels)
    value <- children
    ECTAGen.pure (build value)

{- | One conditional shape. The result label joins the /condition/ label as
well as both branch labels: choosing a branch on a 'Private' condition is an
implicit flow, and it taints the result even when both branches are 'Public'.
-}
data ConditionalInstance = ConditionalInstance
    { conditionKey :: !Labeled
    , trueKey :: !Labeled
    , falseKey :: !Labeled
    , conditionalResultKey :: !Labeled
    }
    deriving (Eq, Ord, Show)

-- | Every conditional shape over the expression types.
conditionalInstances :: [ConditionalInstance]
conditionalInstances =
    [ ConditionalInstance
        (TBool, condition)
        (branch, ifTrue)
        (branch, ifFalse)
        (branch, condition `max` ifTrue `max` ifFalse)
    | condition <- allLabels
    , branch <- expressionTypes
    , ifTrue <- allLabels
    , ifFalse <- allLabels
    ]

-- | The signature of one conditional shape.
conditionalSignature ::
    ConditionalInstance -> Sig '[Labeled, Labeled, Labeled] Labeled
conditionalSignature instance_ =
    conditionKey instance_
        :* trueKey instance_
        :* falseKey instance_
        :-> conditionalResultKey instance_

-- | Build one labeled conditional.
compileConditional ::
    ConditionalInstance ->
    LabeledExpression ->
    LabeledExpression ->
    LabeledExpression ->
    LabeledExpression
compileConditional instance_ condition ifTrue ifFalse =
    LabeledExpression resultType resultLabel $
        IfExpression (expression condition) (expression ifTrue) (expression ifFalse)
  where
    (resultType, resultLabel) = conditionalResultKey instance_

-- | Add one conditional layer, tracking implicit flows.
conditionalLayer :: Grouped Labeled LabeledExpression -> Grouped Labeled LabeledExpression
conditionalLayer children = ECTAGen.do
    shape <- ECTAGen.groupBy conditionalSignature (ECTAGen.elements conditionalInstances)
    condition <- children
    ifTrue <- children
    ifFalse <- children
    ECTAGen.pure (compileConditional shape condition ifTrue ifFalse)

-- | Add one application layer, weighted so every expression stays uniform.
applicationLayer :: Grouped Labeled LabeledExpression -> Grouped Labeled LabeledExpression
applicationLayer children =
    ECTAGen.uniformlyGrouped [unaryLayer children, binaryLayer children, conditionalLayer children]

-- | Labeled expressions of depth at most the bound, uniform across depths.
expressionsUpToDepth :: Int -> Grouped Labeled LabeledExpression
expressionsUpToDepth depth
    | depth <= 0 = atomsByKey
    | otherwise =
        ECTAGen.uniformlyGrouped [atomsByKey, applicationLayer (expressionsUpToDepth (depth - 1))]

-- | The enforcing print signatures: the flow check, written literally.
securePrintInstances :: [Labeled]
securePrintInstances = filter ((<= Public) . snd) expressionKeys

-- | @print :: a -> ()@, keeping its argument's label on the completed print.
printSignature :: Labeled -> Sig '[Labeled] Labeled
printSignature (argumentType, argumentLabel) =
    (argumentType, argumentLabel) :-> (TUnit, argumentLabel)

-- | Build one completed print.
compilePrint :: Labeled -> LabeledExpression -> LabeledExpression
compilePrint (_, argumentLabel) value =
    LabeledExpression TUnit argumentLabel (Print (expression value))

-- | A program prints one expression drawn from the given language.
printLayer ::
    [Labeled] ->
    Grouped Labeled LabeledExpression ->
    Grouped Labeled LabeledExpression
printLayer instances children = ECTAGen.do
    printAt <- compilePrint <$> ECTAGen.groupBy printSignature (ECTAGen.elements instances)
    value <- children
    ECTAGen.pure (printAt value)

-- | All programs, leaks included, keyed @(TUnit, label)@.
programsUpToDepth :: Int -> Grouped Labeled LabeledExpression
programsUpToDepth depth = printLayer expressionKeys (expressionsUpToDepth depth)

-- | Programs whose print only admits 'Public': a leak is unrepresentable.
secureProgramsUpToDepth :: Int -> Grouped Labeled LabeledExpression
secureProgramsUpToDepth depth = printLayer securePrintInstances (expressionsUpToDepth depth)

{- | The types an expression can have. 'TUnit' is excluded: it is the type of
a completed print, not of anything a print can take.
-}
expressionTypes :: [Type]
expressionTypes = [TInt, TBool]

-- | Every key an expression can have.
expressionKeys :: [Labeled]
expressionKeys = [(type_, label) | type_ <- expressionTypes, label <- allLabels]

-- | Number of expressions of depth at most the bound with the given key.
expressionCountUpTo :: Int -> Labeled -> Integer
expressionCountUpTo depth key
    | depth <= 0 = atomCount key
    | otherwise = atomCount key + applicationCount (expressionCountUpTo (depth - 1)) key

-- | Number of atoms with the given key.
atomCount :: Labeled -> Integer
atomCount key = toInteger $ length $ filter ((== key) . securityKey) atoms

-- | Count every application with the given result key.
applicationCount :: (Labeled -> Integer) -> Labeled -> Integer
applicationCount childCount key =
    unaryCount + binaryCount + conditionalCount
  where
    unaryCount = case key of
        (TBool, label) -> childCount (TBool, label)
        _ -> 0
    binaryCount =
        sum
            [ childCount (firstArgumentKey instance_)
                * childCount (secondArgumentKey instance_)
            | instance_ <- binaryFunctionInstances
            , binaryResultKey instance_ == key
            ]
    conditionalCount =
        sum
            [ childCount (conditionKey instance_)
                * childCount (trueKey instance_)
                * childCount (falseKey instance_)
            | instance_ <- conditionalInstances
            , conditionalResultKey instance_ == key
            ]

-- | Number of programs of depth at most the bound: one print per expression.
programCountUpToDepth :: Int -> Integer
programCountUpToDepth depth = sum $ map (expressionCountUpTo depth) expressionKeys

{- | The handwritten baseline makes the label dependency explicit by accepting
the desired key and selecting only compatible instances. Its weights make
every expression of depth at most the bound equally likely, matching the
transparent generator's distribution exactly.

Precondition: the key must be inhabited at that depth. A key with no members
leaves no alternative to weight, and the draw fails.
'handwrittenProgramGen' guards it with 'expressionCountUpTo'.
-}
handwrittenExpressionUpToDepth :: Int -> Labeled -> QC.Gen LabeledExpression
handwrittenExpressionUpToDepth depth key =
    frequencyInteger $ atomAlternatives <> applicationAlternatives
  where
    keyedAtoms = filter ((== key) . securityKey) atoms
    atomAlternatives =
        [(1, pure atom) | atom <- keyedAtoms]
    applicationAlternatives
        | depth <= 0 = []
        | otherwise = unaryAlternatives <> binaryAlternatives <> conditionalAlternatives
    childDepth = depth - 1
    count = expressionCountUpTo childDepth
    child = handwrittenExpressionUpToDepth childDepth
    unaryAlternatives =
        [ ( count (TBool, label)
          , compileNot label <$> child (TBool, label)
          )
        | (TBool, label) <- [key]
        ]
    binaryAlternatives =
        [ ( count (firstArgumentKey instance_)
                * count (secondArgumentKey instance_)
          , do
                first <- child (firstArgumentKey instance_)
                second <- child (secondArgumentKey instance_)
                pure $ compileBinary instance_ first second
          )
        | instance_ <- binaryFunctionInstances
        , binaryResultKey instance_ == key
        ]
    conditionalAlternatives =
        [ ( count (conditionKey instance_)
                * count (trueKey instance_)
                * count (falseKey instance_)
          , do
                condition <- child (conditionKey instance_)
                ifTrue <- child (trueKey instance_)
                ifFalse <- child (falseKey instance_)
                pure $ compileConditional instance_ condition ifTrue ifFalse
          )
        | instance_ <- conditionalInstances
        , conditionalResultKey instance_ == key
        ]

-- | Draw uniformly from all programs of depth at most the bound.
handwrittenProgramGen :: Int -> QC.Gen LabeledExpression
handwrittenProgramGen depth =
    frequencyInteger
        [ ( expressionCountUpTo depth key
          , compilePrint key <$> handwrittenExpressionUpToDepth depth key
          )
        | key <- expressionKeys
        , expressionCountUpTo depth key > 0
        ]

{- | The generator a practiced QuickCheck user actually writes: one function
per type, mutually recursive, choosing constructions with 'QC.oneof' and
decrementing a depth bound. Labels are not steered at all; they are computed
from the finished term, which is how a property about labels would read them
anyway.

This is the baseline a benchmark would compare against: no exact weights, no
instance machinery, just the grammar spelled out. In return its distribution
is whatever constructor-uniform choice yields, not the uniform language. No
benchmark uses it yet.
-}
practicalInt :: Int -> QC.Gen Expression
practicalInt 0 =
    QC.elements [IntLiteral 0, IntLiteral 1, Variable "input", Variable "secret"]
practicalInt depth =
    QC.oneof
        [ practicalInt 0
        , ApplyBinary Add <$> sub <*> sub
        , ApplyBinary Multiply <$> sub <*> sub
        , IfExpression <$> practicalBool (depth - 1) <*> sub <*> sub
        ]
  where
    sub = practicalInt (depth - 1)

-- | The boolean half of the practical generator.
practicalBool :: Int -> QC.Gen Expression
practicalBool 0 = QC.elements [BoolLiteral False, BoolLiteral True]
practicalBool depth =
    QC.oneof
        [ practicalBool 0
        , Not <$> sub
        , ApplyBinary Equal <$> practicalInt (depth - 1) <*> practicalInt (depth - 1)
        , ApplyBinary Equal <$> sub <*> sub
        , ApplyBinary Or <$> sub <*> sub
        , ApplyBinary And <$> sub <*> sub
        , IfExpression <$> sub <*> sub <*> sub
        ]
  where
    sub = practicalBool (depth - 1)

-- | Print one expression of either type, annotated after the fact.
practicalProgramGen :: Int -> QC.Gen LabeledExpression
practicalProgramGen depth = do
    value <- QC.oneof [practicalInt depth, practicalBool depth]
    pure $ LabeledExpression TUnit (practicalLabel value) (Print value)

-- | Join the labels of every atom in a finished term.
practicalLabel :: Expression -> Label
practicalLabel (Variable name)
    | name == "secret" = Private
practicalLabel (Not value) = practicalLabel value
practicalLabel (ApplyBinary _ first second) =
    practicalLabel first `max` practicalLabel second
practicalLabel (IfExpression condition ifTrue ifFalse) =
    practicalLabel condition `max` practicalLabel ifTrue `max` practicalLabel ifFalse
practicalLabel (Print value) = practicalLabel value
practicalLabel _ = Public

{- | The same language as an automaton over surface symbols, so shape queries
can be asked with "Data.ECTA" templates: the literals and variables, @==@,
@+@, @*@, @||@, @&&@, @not@, @if@, and @print@ are the term symbols. The label
discipline is baked into which child nodes each edge takes, exactly as in the
grouped generator.

The generator's own 'ECTAGen.support' cannot serve here. It is built over
namespaced @$ecta-gen/...@ symbols and carries the joins' equality
constraints, so a template cannot name its symbols and @fromECTA@ rejects it.
-}
surfaceExpressionNode :: Int -> Labeled -> Node Symbol
surfaceExpressionNode depth key =
    Map.findWithDefault EmptyNode key $ surfaceLevels !! max 0 depth

{- | The expression node of every key, one list entry per depth.

Each level is built once from the level below it, rather than once per edge
slot that mentions it, which is about 27 times per level.
-}
surfaceLevels :: [Map.Map Labeled (Node Symbol)]
surfaceLevels = iterate deeper base
  where
    base = Map.fromList [(key, Node (atomEdges key)) | key <- expressionKeys]
    deeper below =
        Map.fromList
            [ (key, Node (atomEdges key <> applicationEdges (childOf below) key))
            | key <- expressionKeys
            ]
    childOf below childKey = Map.findWithDefault EmptyNode childKey below

    atomEdges key =
        [ Edge (fromString $ show $ expression atom) []
        | atom <- atoms
        , securityKey atom == key
        ]
    applicationEdges child key =
        unaryEdges child key <> binaryEdges child key <> conditionalEdges child key
    unaryEdges child key =
        [ Edge "not" [child (TBool, label)]
        | (TBool, label) <- [key]
        ]
    binaryEdges child key =
        [ Edge
            (fromString $ functionSymbol $ binaryFunction instance_)
            [child (firstArgumentKey instance_), child (secondArgumentKey instance_)]
        | instance_ <- binaryFunctionInstances
        , binaryResultKey instance_ == key
        ]
    conditionalEdges child key =
        [ Edge
            "if"
            [ child (conditionKey instance_)
            , child (trueKey instance_)
            , child (falseKey instance_)
            ]
        | instance_ <- conditionalInstances
        , conditionalResultKey instance_ == key
        ]

-- | All programs with the given result label, as a surface automaton.
surfaceProgramNode :: Int -> Label -> Node Symbol
surfaceProgramNode depth label =
    Node
        [ Edge "print" [surfaceExpressionNode depth (type_, label)]
        | type_ <- expressionTypes
        ]

-- | Read a surface term back as an expression, for readable output.
termToExpression :: Term Symbol -> Maybe Expression
termToExpression (Term "print" [value]) = Print <$> termToExpression value
termToExpression (Term "not" [value]) = Not <$> termToExpression value
termToExpression (Term "if" [condition, ifTrue, ifFalse]) =
    IfExpression
        <$> termToExpression condition
        <*> termToExpression ifTrue
        <*> termToExpression ifFalse
termToExpression (Term symbol [first, second])
    | Just function_ <- lookup symbol binaryFunctionSymbols =
        ApplyBinary function_ <$> termToExpression first <*> termToExpression second
termToExpression (Term symbol []) = lookup symbol atomSymbols
termToExpression _ = Nothing

-- | The surface symbol of every binary function, as the automaton spells it.
binaryFunctionSymbols :: [(Symbol, Function)]
binaryFunctionSymbols =
    [(fromString $ functionSymbol function_, function_) | function_ <- [minBound ..]]

-- | The surface symbol of every atom, as the automaton spells it.
atomSymbols :: [(Symbol, Expression)]
atomSymbols =
    [(fromString $ show $ expression atom, expression atom) | atom <- atoms]
