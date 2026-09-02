{- | A small expression language that makes refinement relationships visible in
the Haskell values as well as in their LTA witnesses.

The examples are intentionally finite. That makes every accepted program and
every semantic shrink inspectable in the specs, while exercising the same
guards that a sampled QuickCheck pool uses.
-}
module Data.LTA.TypedExpressionLanguage (
    Expression (..),
    RefinedExpression (..),
    value,
    variable,
    nonNegative,
    nonZero,
    solverDeclarations,
    atoms,
    nonNegativeExpressions,
    divisions,
    subtypePairs,
    dependentApplications,
) where

import qualified Language.Fixpoint.Types as Fixpoint

import Data.LTA (Guard, Refinement, Symbol)
import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.Guard (Position, allOf, descendant, isSubtypeOf, requires, unconstrained, withActualFor)
import Data.LTA.Refinement (true, (.+.), (./=.), (.==.), (.>=.))

-- | Expressions used by the LTA capability examples.
data Expression
    = Unknown
    | Variable !String
    | Integer !Int
    | SquareRoot !Expression
    | Divide !Expression !Expression
    | ApplyIncrement !Expression
    deriving (Eq, Ord, Show)

-- | An expression paired with the refinement used for its LTA witness.
data RefinedExpression = RefinedExpression
    { expression :: !Expression
    , expressionRefinement :: !Refinement
    }
    deriving (Eq, Show)

-- | Liquid Fixpoint's distinguished value variable for these examples.
value :: Fixpoint.Expr
value = variable "v"

-- | Build a Liquid Fixpoint variable expression.
variable :: String -> Fixpoint.Expr
variable = Fixpoint.EVar . Fixpoint.symbol

-- | The non-negative integer refinement.
nonNegative :: Refinement
nonNegative = value .>=. (0 :: Int)

-- | The non-zero integer refinement.
nonZero :: Refinement
nonZero = value ./=. (0 :: Int)

-- | All free integer symbols that can reach a solver query in the examples.
solverDeclarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
solverDeclarations =
    [ (Fixpoint.symbol name, Fixpoint.FInt)
    | name <- ["v", "x", "y", "p", "n"] :: [String]
    ]

-- | Atoms ordered from least information to more useful concrete witnesses.
atoms :: LTA.LTAGen RefinedExpression
atoms =
    LTA.pool
        [ atom Unknown "u" true
        , atom (Integer (-1)) "minus-one" (value .==. (-1 :: Int))
        , atom (Integer 0) "zero" (value .==. (0 :: Int))
        , atom (Integer 1) "one" (value .==. (1 :: Int))
        , atom (Variable "n") "n" nonNegative
        ]

-- | A unary operation whose argument must establish non-negativity.
nonNegativeExpressions :: LTA.LTAGen RefinedExpression
nonNegativeExpressions =
    LTA.node "sqrt" true (\argument -> argument `requires` nonNegative) $ LTA.do
        argument <- atoms
        LTA.pure $ RefinedExpression (SquareRoot $ expression argument) true

-- | Division expressions whose denominator proves it is non-zero.
divisions :: LTA.LTAGen RefinedExpression
divisions =
    LTA.node "divide" true divisionGuard $ LTA.do
        numerator <- atoms
        denominator <- atoms
        LTA.pure $
            RefinedExpression
                (Divide (expression numerator) (expression denominator))
                true

divisionGuard :: Position -> Position -> Guard
divisionGuard _ denominator = denominator `requires` nonZero

-- | Every ordered atom pair where the left refinement is a subtype of the right.
subtypePairs :: LTA.LTAGen (RefinedExpression, RefinedExpression)
subtypePairs =
    LTA.node "ascribe" true (\actual expected -> actual `isSubtypeOf` expected) $ LTA.do
        actual <- atoms
        expected <- atoms
        LTA.pure (actual, expected)

{- | Dependent application as represented in the LTA paper.

The application has explicit result-type, function, and argument children. The
function subtree contains formal-name, input-type, and output-type children.
The guard checks argument subtyping, then substitutes the actual variable for
the formal variable before comparing the dependent output with the result.
-}
dependentApplications :: LTA.LTAGen RefinedExpression
dependentApplications =
    LTA.node "app" true applicationGuard $ LTA.do
        result <- resultTypes
        _function <- incrementFunction
        argument <- namedArguments
        LTA.pure $ RefinedExpression (ApplyIncrement $ expression argument) (resultRefinement result)
  where
    applicationGuard result function argument =
        allOf
            [ argument `isSubtypeOf` descendant function [1]
            , withActualFor argument (descendant function [0]) $
                descendant function [2] `isSubtypeOf` result
            ]

data ResultType = ResultType
    { resultRefinement :: !Refinement
    }

resultTypes :: LTA.LTAGen ResultType
resultTypes =
    LTA.pool
        [ result "result-x" "x"
        , result "result-y" "y"
        , result "result-p" "p"
        ]
  where
    result symbolName actualName =
        let refinement = value .==. (variable actualName .+. (1 :: Int))
         in LTA.refined (ResultType refinement) symbolName refinement

namedArguments :: LTA.LTAGen RefinedExpression
namedArguments =
    LTA.pool
        [ atom (Variable "x") "x" (value .==. (0 :: Int))
        , atom (Variable "y") "y" (value .==. (-1 :: Int))
        , atom (Variable "p") "p" (value .==. (1 :: Int))
        ]

incrementFunction :: LTA.LTAGen ()
incrementFunction =
    LTA.node "increment" true unconstrained $ LTA.do
        _formal <- LTA.leaf () "n" true
        _input <- LTA.leaf () "input" nonNegative
        _output <- LTA.leaf () "output" (value .==. (variable "n" .+. (1 :: Int)))
        LTA.pure ()

atom :: Expression -> Symbol -> Refinement -> LTA.Refined RefinedExpression
atom expression symbol refinement =
    LTA.refined (RefinedExpression expression refinement) symbol refinement
