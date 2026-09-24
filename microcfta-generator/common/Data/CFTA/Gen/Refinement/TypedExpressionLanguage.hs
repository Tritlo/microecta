{- | A small expression language that makes refinement relationships visible in
the Haskell values as well as in their LTA witnesses.

The examples are intentionally finite. That makes every accepted program and
every semantic shrink inspectable in the specs, while exercising the same
guards that a sampled QuickCheck pool uses.
-}
module Data.CFTA.Gen.Refinement.TypedExpressionLanguage (
    Expression (..),
    RefinedExpression (..),
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
import Data.CFTA.Refinement (Formula, Symbol)
import Data.CFTA.Refinement.Expression (Refinement, refinementFormula, true, variable, (./=), (.==))
import Data.CFTA.Refinement.Guard (allOf, descendant, isSubtypeOf, withActualFor)

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
    , expressionRefinement :: !Formula
    }
    deriving (Eq, Show)

-- | The non-zero integer refinement.
nonZero :: Refinement
nonZero v = v ./= 0

-- | All free integer symbols that can reach a solver query in the examples.
solverDeclarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
solverDeclarations =
    [ (Fixpoint.symbol name, Fixpoint.FInt)
    | name <- ["v", "x", "y", "p", "n"] :: [String]
    ]

-- | Atoms ordered from least information to more useful concrete witnesses.
atoms :: LTAGen.LTAGen RefinedExpression
atoms =
    LTAGen.namedPool
        [ atom Unknown "u" (const true)
        , atom (Integer (-1)) "minus-one" (\v -> v .== -1)
        , atom (Integer 0) "zero" (\v -> v .== 0)
        , atom (Integer 1) "one" (\v -> v .== 1)
        , atom (Variable "n") "n" nonNegative
        ]

-- | A unary operation whose argument must establish non-negativity.
nonNegativeExpressions :: LTAGen.LTAGen RefinedExpression
nonNegativeExpressions = LTAGen.node "sqrt" $ LTAGen.do
    argument <- atoms `LTAGen.satisfying` nonNegative
    LTAGen.pure $ RefinedExpression (SquareRoot $ expression argument) true

-- | Division expressions whose denominator proves it is non-zero.
divisions :: LTAGen.LTAGen RefinedExpression
divisions = LTAGen.node "divide" $ LTAGen.do
    numerator <- atoms
    denominator <- atoms `LTAGen.satisfying` nonZero
    LTAGen.pure $
        RefinedExpression
            (Divide (expression numerator) (expression denominator))
            true

{- | Every ordered atom pair where the left refinement is a subtype of the right.

Subtyping relates the two refinements, not two values, so it stays a
positional guard of 'LTAGen.refinedNode'. It is the form that Liquid Haskell
writes as @{v | p} <: {v | q}@.
-}
subtypePairs :: LTAGen.LTAGen (RefinedExpression, RefinedExpression)
subtypePairs =
    LTAGen.refinedNode "ascribe" (const true) (\actual expected -> actual `isSubtypeOf` expected) $ LTAGen.do
        actual <- atoms
        expected <- atoms
        LTAGen.pure (actual, expected)

{- | Dependent application as represented in the LTA paper.

The application has explicit result-type, function, and argument children. The
function subtree contains formal-name, input-type, and output-type children.
The guard checks argument subtyping, then substitutes the actual variable for
the formal variable before comparing the dependent output with the result.

This is the paper's encoding, kept as the comparison with contracts: the
function type is generated data, so the guard names positions inside it. For a
fixed function, a contract over the argument and result values states the same
check, as the sized-vector and safe-buffer languages do.
-}
dependentApplications :: LTAGen.LTAGen RefinedExpression
dependentApplications =
    LTAGen.refinedNode "app" (const true) applicationGuard $ LTAGen.do
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
    { resultRefinement :: Formula
    }

resultTypes :: LTAGen.LTAGen ResultType
resultTypes =
    LTAGen.namedPool
        [ result "result-x" "x"
        , result "result-y" "y"
        , result "result-p" "p"
        ]
  where
    result symbolName actualName =
        let refinement v = v .== (variable actualName + 1)
         in LTAGen.Refined (ResultType (refinementFormula refinement)) symbolName refinement

namedArguments :: LTAGen.LTAGen RefinedExpression
namedArguments =
    LTAGen.namedPool
        [ atom (Variable "x") "x" (\v -> v .== 0)
        , atom (Variable "y") "y" (\v -> v .== -1)
        , atom (Variable "p") "p" (\v -> v .== 1)
        ]

incrementFunction :: LTAGen.LTAGen ()
incrementFunction =
    LTAGen.node "increment" $ LTAGen.do
        _formal <- LTAGen.leaf () "n" (const true)
        _input <- LTAGen.leaf () "input" nonNegative
        _output <- LTAGen.leaf () "output" (\v -> v .== (variable "n" + 1))
        LTAGen.pure ()

atom :: Expression -> Symbol -> Refinement -> LTAGen.Refined RefinedExpression
atom expression symbol refinement =
    LTAGen.Refined (RefinedExpression expression (refinementFormula refinement)) symbol refinement
