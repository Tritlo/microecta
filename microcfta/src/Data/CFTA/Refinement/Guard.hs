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
    Path,
    GuardBuilder (buildGuardFrom, guardArgumentCount),
    buildGuard,
    root,
    unconstrained,
    argument,
    descendant,
    requires,
    ContractBuilder (contractArity, contractFormulaFrom),
    contract,
    MeasureBuilder (measureArity, measureTermFrom),
    measureTerm,
    isSubtypeOf,
    isSameTermAs,
    withActualFor,
    withActualsFor,
    allOf,
    anyOf,
    notGuard,
) where

import Data.CFTA.Index (ArgumentIndex (..), Arity (..))
import Data.CFTA.Refinement (
    Automaton,
    AutomatonError (GuardArityMismatch),
    ChildIndex (..),
    Constraint,
    Formula,
    Guard (And, Entails, Holds, Not, Or, Same, Satisfies, Substitute),
    Node (Node),
    Path (EmptyPath),
    Substitution (Substitution),
    Symbol,
    Transition,
    conjoinConstraints,
    constraintAsGuard,
    contractTermName,
    noConstraint,
    path,
    semanticConstraint,
    unPath,
    validate,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (Expr, Refinement, refinementFormula, variable)
import Data.Maybe (fromMaybe)
import qualified Language.Fixpoint.Types as Fixpoint
import Numeric.Natural (Natural)

-- | The root/result of the guarded transition.
root :: Path
root = EmptyPath

-- | A transition with no liquid constraint.
unconstrained :: Constraint
unconstrained = noConstraint

{- | A constraint or a function over consecutive constructor arguments.

For example, @\actual expected -> actual `isSubtypeOf` expected@ receives
arguments zero and one without exposing those indices at the call site.
-}
class GuardBuilder guard where
    {- | Build a guard starting at the supplied argument index.
    Most callers should use 'buildGuard'.
    -}
    buildGuardFrom :: ArgumentIndex -> guard -> Constraint

    {- | Number of named constructor arguments, when this is a guard function.

    Raw constraints have no argument-count requirement. Their paths can be
    absent in some alternatives, as required by Boolean constraint semantics.
    -}
    guardArgumentCount :: guard -> Maybe Arity
    guardArgumentCount _ = Nothing

instance GuardBuilder Constraint where
    buildGuardFrom _ = id

instance GuardBuilder Guard where
    buildGuardFrom _ = semanticConstraint

instance (position ~ Path, GuardBuilder guard) => GuardBuilder (position -> guard) where
    buildGuardFrom index continue =
        buildGuardFrom (index + 1) (continue $ argumentPath index)

    guardArgumentCount continue =
        Just $ 1 + fromMaybe 0 (guardArgumentCount $ continue root)

-- | Turn a raw or argument-building guard into a concrete LTA constraint.
buildGuard :: (GuardBuilder guard) => guard -> Constraint
buildGuard = buildGuardFrom 0

-- | Select a zero-based constructor argument.
argument :: Natural -> Path
argument index = path [fromIntegral index]

-- | The path of an argument of a guard or a contract. Argument @i@ is child @i@.
argumentPath :: ArgumentIndex -> Path
argumentPath (ArgumentIndex index) = path [ChildIndex index]

-- | Select a nested position below an existing position.
descendant :: Path -> [Natural] -> Path
descendant prefix suffix = prefix <> path (map fromIntegral suffix)

{- | Require the refinement at a position to imply a literal predicate.

For a division node, for example, @denominator `requires` nonZero@ states the
precondition directly; it does not need a synthetic predicate child.
-}
requires :: Path -> Refinement -> Constraint
requires target refinement =
    semanticConstraint $ Satisfies target (refinementFormula refinement)

{- | A contract: a formula about the children of a constructor.

Write it as a function with one term for each child, in order, as in
@\\n i -> 0 .<= i .&& i .< n@. Each term stands for its child's value, and the
child's refinement holds for it.
-}
class ContractBuilder contract where
    -- | The number of children that the contract names.
    contractArity :: contract -> Arity

    -- | The formula, with the terms of the children numbered from an index.
    contractFormulaFrom :: ArgumentIndex -> contract -> Formula

instance ContractBuilder Formula where
    contractArity _ = 0
    contractFormulaFrom _ formula = formula

instance (term ~ Expr, ContractBuilder contract) => ContractBuilder (term -> contract) where
    contractArity continue = 1 + contractArity (continue (variable (contractTermName 0)))
    contractFormulaFrom index continue =
        contractFormulaFrom (index + 1) (continue (variable (contractTermName index)))

{- | A measure: the integer term of a constructed term, written as a function
with one term for each child, in order, as in @\\leftHeight _ -> leftHeight + 1@.
Each term stands for the measure of its child.
-}
class MeasureBuilder measure where
    -- | The number of children that the measure takes.
    measureArity :: measure -> Arity

    -- | The term, with the child at index @i@ named by 'contractTermName' @i@, from the given index.
    measureTermFrom :: ArgumentIndex -> measure -> Expr

instance MeasureBuilder Expr where
    measureArity _ = 0
    measureTermFrom _ term = term

instance (term ~ Expr, MeasureBuilder measure) => MeasureBuilder (term -> measure) where
    measureArity continue = 1 + measureArity (continue $ variable $ contractTermName 0)
    measureTermFrom index continue = measureTermFrom (index + 1) (continue $ variable $ contractTermName index)

-- | The term of a measure, with the child at index @i@ named by 'contractTermName' @i@.
measureTerm :: (MeasureBuilder measure) => measure -> Expr
measureTerm = measureTermFrom 0

{- | Require a contract about the children of the constructor.

The solver proves each conjunct of the contract formula separately. For a
conjunct, it assumes the refinement of each child that the conjunct names, then
proves the conjunct. The solver decides each distinct formula once, through its
cache. The evaluator tests the whole guard for each tuple of child groups.

'notGuard' of a contract holds when the refinements of the named children refute
one of its conjuncts, and when a named child is absent. A failed conjunct only
means that those refinements do not prove it, so a term can satisfy neither the
contract nor its negation.
-}
contract :: (ContractBuilder contract) => contract -> Constraint
contract builder =
    allOf
        [ semanticConstraint $ Holds (map argumentPath named) (renumbered named conjunct)
        | conjunct <- conjuncts $ contractFormulaFrom 0 builder
        , conjunct /= Fixpoint.PTrue
        , let named = [index | (index, name) <- terms, name `elem` Fixpoint.syms conjunct]
        ]
  where
    Arity count = contractArity builder
    terms = [(index, Fixpoint.symbol $ contractTermName index) | index <- map ArgumentIndex [0 .. count - 1]]
    conjuncts (Fixpoint.PAnd parts) = concatMap conjuncts parts
    conjuncts formula = [formula]
    -- A quantifier renames its bound name when the renaming uses that name, so no term is captured.
    renumbered named conjunct =
        Fixpoint.rapierSubstExpr (Fixpoint.exprSymbolsSet conjunct <> Fixpoint.substSymbolsSet renaming) renaming conjunct
      where
        renaming =
            Fixpoint.mkSubst
                [ (Fixpoint.symbol $ contractTermName old, Fixpoint.EVar $ Fixpoint.symbol $ contractTermName new)
                | (new, old) <- zip [0 ..] named
                ]

-- | Require the left position's refinement to be a subtype of the right one.
isSubtypeOf :: Path -> Path -> Constraint
isSubtypeOf subtype supertype = semanticConstraint $ Entails subtype supertype

-- | Require both positions to contain the same annotated LTA term.
isSameTermAs :: Path -> Path -> Constraint
isSameTermAs left right = semanticConstraint $ Same left right

{- | Check a guard after substituting the actual position's symbol for the
formal position's symbol throughout the complete guard. This includes the
constructor symbols and refinement expressions compared by 'isSameTermAs'.
The evaluator also assumes that symbol satisfies the actual subtree's
refinement. The substitution does not change returned or generated terms.
-}
withActualFor :: Path -> Path -> Constraint -> Constraint
withActualFor actual formal = withActualsFor [(actual, formal)]

{- | Apply several actual-for-formal substitutions to one complete constraint.

The substitutions affect predicates and the annotated terms compared by
'isSameTermAs'. The first non-identity mapping for a repeated formal name takes
precedence. The substitutions do not change returned or generated terms.
-}
withActualsFor :: [(Path, Path)] -> Constraint -> Constraint
withActualsFor substitutions constraint =
    semanticConstraint
        $ Substitute (map (uncurry Substitution) substitutions)
        $ constraintAsGuard constraint

-- | Conjoin a collection of guard requirements.
allOf :: [Constraint] -> Constraint
allOf = foldr conjoinConstraints noConstraint

-- | Accept when at least one complete LTA constraint holds.
anyOf :: [Constraint] -> Constraint
anyOf = semanticConstraint . Or . map constraintAsGuard

{- | Negate one complete LTA constraint, including syntactic equality.

Negation moves through 'allOf', 'anyOf', 'notGuard', 'withActualFor', and
'withActualsFor' to the checks. A negated 'requires' or 'contract' holds only
when the refinements refute its formula. A negated 'isSubtypeOf' or
'isSameTermAs' holds when the check fails. A negated check at a missing
position holds.
-}
notGuard :: Constraint -> Constraint
notGuard = semanticConstraint . Not . constraintAsGuard

{- | Build a transition from a guard that names the constructor arguments.

A guard written as a function receives one position per child, in order, and
the construction fails when the counts differ. It also fails when a 'contract'
names more terms than the constructor has children, because such a contract
holds for no term. 'automaton' collects the checked transitions of one node.
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
            | supplied /= Arity (length children) ->
                Left $ GuardArityMismatch symbol (Arity (length children)) supplied
        _
            | Just named <- contractReach built
            , named > Arity (length children) ->
                Left $ GuardArityMismatch symbol (Arity (length children)) named
            | otherwise -> Right $ Transition symbol (refinementFormula refinement) children built
  where
    built = buildGuard guard

{- | One more than the largest child index that a 'Holds' atom of a constraint
names, when the constraint has such an atom. Only 'contract' makes these atoms.
-}
contractReach :: Constraint -> Maybe Arity
contractReach constraint = case [index | Holds targets _ <- atoms (constraintAsGuard constraint), ChildIndex index : _ <- map unPath targets] of
    [] -> Nothing
    indices -> Just (Arity (maximum indices + 1))
  where
    atoms (Not nested) = atoms nested
    atoms (And guards) = concatMap atoms guards
    atoms (Or guards) = concatMap atoms guards
    atoms (Substitute _ nested) = atoms nested
    atoms atom = [atom]

-- | Collect checked transitions into one validated node.
automaton :: [Either AutomatonError Transition] -> Either AutomatonError Automaton
automaton transitions = do
    alternatives <- sequence transitions
    let node = Node alternatives
    validate node
    pure node
