{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{- | Guard syntax in terms of constructor arguments, and the transition
builders that check it against the constructor's children.
-}
module Data.CFTA.Refinement.Guard (
    transition,
    automaton,
    Position,
    GuardBuilder (buildGuardFrom, guardArgumentCount),
    buildGuard,
    root,
    unconstrained,
    argument,
    descendant,
    requires,
    ContractBuilder (contractArity, contractFormulaFrom),
    contract,
    ResultBuilder (resultArity, resultTermFrom),
    resultTerm,
    isSubtypeOf,
    isSameTermAs,
    withActualFor,
    withActualsFor,
    allOf,
    anyOf,
    notGuard,
) where

import Data.CFTA.Refinement (
    Automaton,
    AutomatonError (GuardArityMismatch),
    Formula,
    Guard (Entails, Holds, Not, Or, Same, Satisfies, Substitute),
    LiquidConstraint,
    Node (Node),
    Substitution (Substitution),
    Symbol,
    Transition,
    combineConstraints,
    constraintAsGuard,
    contractTermName,
    path,
    semanticConstraint,
    unconstrainedConstraint,
    validate,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (Expr, Refinement, refinementFormula, variable)
import Data.Maybe (fromMaybe)
import qualified Language.Fixpoint.Types as Fixpoint
import Numeric.Natural (Natural)

-- | A position relative to the root of the guarded constructor.
newtype Position = Position [Natural]

-- | The root/result of the guarded transition.
root :: Position
root = Position []

-- | A transition with no liquid constraint.
unconstrained :: LiquidConstraint
unconstrained = unconstrainedConstraint

{- | A constraint or a function over consecutive constructor arguments.

For example, @\actual expected -> actual `isSubtypeOf` expected@ receives
arguments zero and one without exposing those indices at the call site.
-}
class GuardBuilder guard where
    {- | Build a guard starting at the supplied argument index.
    Most callers should use 'buildGuard'.
    -}
    buildGuardFrom :: Natural -> guard -> LiquidConstraint

    {- | Number of named constructor arguments, when this is a guard function.

    Raw constraints have no argument-count requirement. Their paths can be
    absent in some alternatives, as required by Boolean constraint semantics.
    -}
    guardArgumentCount :: guard -> Maybe Int
    guardArgumentCount _ = Nothing

instance GuardBuilder LiquidConstraint where
    buildGuardFrom _ = id

instance GuardBuilder Guard where
    buildGuardFrom _ = semanticConstraint

instance (position ~ Position, GuardBuilder guard) => GuardBuilder (position -> guard) where
    buildGuardFrom index continue =
        buildGuardFrom (index + 1) (continue $ argument index)

    guardArgumentCount continue =
        Just $ 1 + fromMaybe 0 (guardArgumentCount $ continue root)

-- | Turn a raw or argument-building guard into a concrete LTA constraint.
buildGuard :: (GuardBuilder guard) => guard -> LiquidConstraint
buildGuard = buildGuardFrom 0

-- | Select a zero-based constructor argument.
argument :: Natural -> Position
argument index = Position [index]

-- | Select a nested position below an existing position.
descendant :: Position -> [Natural] -> Position
descendant (Position prefix) suffix = Position (prefix <> suffix)

{- | Require the refinement at a position to imply a literal predicate.

For a division node, for example, @denominator `requires` nonZero@ states the
precondition directly; it does not need a synthetic predicate child.
-}
requires :: Position -> Refinement -> LiquidConstraint
requires (Position target) refinement =
    semanticConstraint $ Satisfies (path $ map fromIntegral target) (refinementFormula refinement)

{- | A contract: a formula about the children of a constructor.

Write it as a function with one term for each child, in order, as in
@\\n i -> 0 .<= i .&& i .< n@. Each term stands for its child's value, and the
child's refinement holds for it.
-}
class ContractBuilder contract where
    -- | The number of children that the contract names.
    contractArity :: contract -> Int

    -- | The formula, with the terms of the children numbered from an index.
    contractFormulaFrom :: Int -> contract -> Formula

instance ContractBuilder Formula where
    contractArity _ = 0
    contractFormulaFrom _ formula = formula

instance (term ~ Expr, ContractBuilder contract) => ContractBuilder (term -> contract) where
    contractArity continue = 1 + contractArity (continue (variable (contractTermName 0)))
    contractFormulaFrom index continue =
        contractFormulaFrom (index + 1) (continue (variable (contractTermName index)))

{- | A result: a term of the children of a constructor, one term for each
child, in order, as in @\\l _ -> l + 1@.
-}
class ResultBuilder result where
    -- | The number of children that the result takes.
    resultArity :: result -> Int

    -- | The term, with the child at index @i@ named by 'contractTermName' @i@, from the given index.
    resultTermFrom :: Int -> result -> Expr

instance ResultBuilder Expr where
    resultArity _ = 0
    resultTermFrom _ term = term

instance (term ~ Expr, ResultBuilder result) => ResultBuilder (term -> result) where
    resultArity continue = 1 + resultArity (continue $ variable $ contractTermName 0)
    resultTermFrom index continue = resultTermFrom (index + 1) (continue $ variable $ contractTermName index)

-- | The term of a result, with the child at index @i@ named by 'contractTermName' @i@.
resultTerm :: (ResultBuilder result) => result -> Expr
resultTerm = resultTermFrom 0

{- | Require a contract about the children of the constructor.

The solver proves each conjunct of the contract formula separately. For a
conjunct, it assumes the refinement of each child that the conjunct names, then
proves the conjunct. The compiler decides each conjunct once for each group of
those children, as it decides the parts of an 'allOf'.
-}
contract :: (ContractBuilder contract) => contract -> LiquidConstraint
contract builder =
    allOf
        [ semanticConstraint $ Holds [path [index] | index <- named] (renumbered named conjunct)
        | conjunct <- conjuncts $ contractFormulaFrom 0 builder
        , conjunct /= Fixpoint.PTrue
        , let named = [index | (index, name) <- terms, name `elem` Fixpoint.syms conjunct]
        ]
  where
    terms = [(index, Fixpoint.symbol $ contractTermName index) | index <- [0 .. contractArity builder - 1]]
    conjuncts (Fixpoint.PAnd parts) = concatMap conjuncts parts
    conjuncts formula = [formula]
    renumbered named =
        Fixpoint.subst $
            Fixpoint.mkSubst
                [ (Fixpoint.symbol $ contractTermName old, Fixpoint.EVar $ Fixpoint.symbol $ contractTermName new)
                | (new, old) <- zip [0 ..] named
                ]

-- | Require the left position's refinement to be a subtype of the right one.
isSubtypeOf :: Position -> Position -> LiquidConstraint
isSubtypeOf (Position subtype) (Position supertype) =
    semanticConstraint $
        Entails
            (path $ map fromIntegral subtype)
            (path $ map fromIntegral supertype)

-- | Require both positions to contain the same annotated LTA term.
isSameTermAs :: Position -> Position -> LiquidConstraint
isSameTermAs (Position left) (Position right) =
    semanticConstraint $
        Same
            (path $ map fromIntegral left)
            (path $ map fromIntegral right)

{- | Check a guard after substituting the actual position's symbol for the
formal position's symbol throughout the complete guard. This includes the
constructor symbols and refinement expressions compared by 'isSameTermAs'.
The evaluator also assumes that symbol satisfies the actual subtree's
refinement. The substitution does not change returned or generated terms.
-}
withActualFor :: Position -> Position -> LiquidConstraint -> LiquidConstraint
withActualFor actual formal = withActualsFor [(actual, formal)]

{- | Apply several actual-for-formal substitutions to one complete constraint.

The substitutions affect predicates and the annotated terms compared by
'isSameTermAs'. The first non-identity mapping for a repeated formal name takes
precedence. The substitutions do not change returned or generated terms.
-}
withActualsFor :: [(Position, Position)] -> LiquidConstraint -> LiquidConstraint
withActualsFor substitutions constraint =
    semanticConstraint
        $ Substitute (map substitution substitutions)
        $ constraintAsGuard constraint
  where
    substitution (Position actual, Position formal) =
        Substitution
            (path $ map fromIntegral actual)
            (path $ map fromIntegral formal)

-- | Conjoin a collection of guard requirements.
allOf :: [LiquidConstraint] -> LiquidConstraint
allOf = foldr combineConstraints unconstrainedConstraint

-- | Accept when at least one complete LTA constraint holds.
anyOf :: [LiquidConstraint] -> LiquidConstraint
anyOf = semanticConstraint . Or . map constraintAsGuard

-- | Negate one complete LTA constraint, including syntactic equality.
notGuard :: LiquidConstraint -> LiquidConstraint
notGuard = semanticConstraint . Not . constraintAsGuard

{- | Build a transition from a guard that names the constructor arguments.

A guard written as a function receives one position per child, in order, and
the construction fails when the counts differ. 'automaton' collects the
checked transitions of one node.
-}
transition ::
    (GuardBuilder guard) =>
    Symbol ->
    Refinement ->
    [Automaton] ->
    guard ->
    Either AutomatonError Transition
transition symbol refinement children guard =
    case guardArgumentCount guard of
        Just supplied
            | supplied /= length children ->
                Left $ GuardArityMismatch symbol (length children) supplied
        _ -> Right $ Transition symbol (refinementFormula refinement) children (buildGuard guard)

-- | Collect checked transitions into one validated node.
automaton :: [Either AutomatonError Transition] -> Either AutomatonError Automaton
automaton transitions = do
    alternatives <- sequence transitions
    let node = Node alternatives
    validate node
    pure node
