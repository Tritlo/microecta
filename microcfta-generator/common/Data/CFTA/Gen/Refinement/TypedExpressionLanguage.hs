{- | A small expression language that makes refinement relationships visible in
the Haskell values as well as in their LTA witnesses.

The examples are intentionally finite. That makes every accepted program and
every semantic shrink inspectable in the specs, while exercising the same
guards that a sampled QuickCheck pool uses.
-}
module Data.CFTA.Gen.Refinement.TypedExpressionLanguage (
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

import Data.CFTA.Gen.Refinement.ExampleSupport (nonNegative)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Refinement (LiquidConstraint, Refinement, Symbol)
import Data.CFTA.Refinement.Expression (true, value, variable, (.+.), (./=.), (.==.))
import Data.CFTA.Refinement.Guard (Position, allOf, descendant, isSubtypeOf, requires, unconstrained, withActualFor)

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
atoms :: LTAGen.LTAGen RefinedExpression
atoms =
    LTAGen.pool
        [ atom Unknown "u" true
        , atom (Integer (-1)) "minus-one" (value .==. (-1 :: Int))
        , atom (Integer 0) "zero" (value .==. (0 :: Int))
        , atom (Integer 1) "one" (value .==. (1 :: Int))
        , atom (Variable "n") "n" nonNegative
        ]

-- | A unary operation whose argument must establish non-negativity.
nonNegativeExpressions :: LTAGen.LTAGen RefinedExpression
nonNegativeExpressions =
    LTAGen.node "sqrt" (`requires` nonNegative) $ LTAGen.do
        argument <- atoms
        LTAGen.pure $ RefinedExpression (SquareRoot $ expression argument) true

-- | Division expressions whose denominator proves it is non-zero.
divisions :: LTAGen.LTAGen RefinedExpression
divisions =
    LTAGen.node "divide" divisionGuard $ LTAGen.do
        numerator <- atoms
        denominator <- atoms
        LTAGen.pure $
            RefinedExpression
                (Divide (expression numerator) (expression denominator))
                true

divisionGuard :: Position -> Position -> LiquidConstraint
divisionGuard _ denominator = denominator `requires` nonZero

-- | Every ordered atom pair where the left refinement is a subtype of the right.
subtypePairs :: LTAGen.LTAGen (RefinedExpression, RefinedExpression)
subtypePairs =
    LTAGen.node "ascribe" (\actual expected -> actual `isSubtypeOf` expected) $ LTAGen.do
        actual <- atoms
        expected <- atoms
        LTAGen.pure (actual, expected)

{- | Dependent application as represented in the LTA paper.

The application has explicit result-type, function, and argument children. The
function subtree contains formal-name, input-type, and output-type children.
The guard checks argument subtyping, then substitutes the actual variable for
the formal variable before comparing the dependent output with the result.
-}
dependentApplications :: LTAGen.LTAGen RefinedExpression
dependentApplications =
    LTAGen.node "app" applicationGuard $ LTAGen.do
        result <- resultTypes
        _function <- incrementFunction
        argument <- namedArguments
        LTAGen.pure $ RefinedExpression (ApplyIncrement $ expression argument) (resultRefinement result)
  where
    applicationGuard result function argument =
        allOf
            [ argument `isSubtypeOf` descendant function [1]
            , withActualFor argument (descendant function [0]) $
                descendant function [2] `isSubtypeOf` result
            ]

newtype ResultType = ResultType
    { resultRefinement :: Refinement
    }

resultTypes :: LTAGen.LTAGen ResultType
resultTypes =
    LTAGen.pool
        [ result "result-x" "x"
        , result "result-y" "y"
        , result "result-p" "p"
        ]
  where
    result symbolName actualName =
        let refinement = value .==. (variable actualName .+. (1 :: Int))
         in LTAGen.Refined (ResultType refinement) symbolName refinement

namedArguments :: LTAGen.LTAGen RefinedExpression
namedArguments =
    LTAGen.pool
        [ atom (Variable "x") "x" (value .==. (0 :: Int))
        , atom (Variable "y") "y" (value .==. (-1 :: Int))
        , atom (Variable "p") "p" (value .==. (1 :: Int))
        ]

incrementFunction :: LTAGen.LTAGen ()
incrementFunction =
    LTAGen.node "increment" unconstrained $ LTAGen.do
        _formal <- LTAGen.leaf () "n" true
        _input <- LTAGen.leaf () "input" nonNegative
        _output <- LTAGen.leaf () "output" (value .==. (variable "n" .+. (1 :: Int)))
        LTAGen.pure ()

atom :: Expression -> Symbol -> Refinement -> LTAGen.Refined RefinedExpression
atom expression symbol refinement =
    LTAGen.Refined (RefinedExpression expression refinement) symbol refinement
