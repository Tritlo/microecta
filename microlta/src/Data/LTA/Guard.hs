{-# LANGUAGE FlexibleInstances #-}

-- | Guard syntax in terms of constructor arguments.
module Data.LTA.Guard (
    Position,
    GuardBuilder (buildGuardFrom),
    buildGuard,
    root,
    unconstrained,
    argument,
    descendant,
    requires,
    isSubtypeOf,
    isSameTermAs,
    withActualFor,
    withActualsFor,
    allOf,
    anyOf,
    notGuard,

    -- * Compatibility aliases
    refines,
    sameAs,
) where

import Data.LTA (
    Guard (Entails, Not, Or, Same, Satisfies, Substitute),
    LiquidConstraint (constraintGuard),
    Refinement,
    Substitution (Substitution),
    combineConstraints,
    constraintAsGuard,
    path,
    semanticConstraint,
    unconstrainedConstraint,
 )
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

instance GuardBuilder LiquidConstraint where
    buildGuardFrom _ = id

instance GuardBuilder Guard where
    buildGuardFrom _ = semanticConstraint

instance (GuardBuilder guard) => GuardBuilder (Position -> guard) where
    buildGuardFrom index continue =
        buildGuardFrom (index + 1) (continue $ argument index)

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
    semanticConstraint $ Satisfies (path $ map fromIntegral target) refinement

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
formal position's symbol in every refinement predicate. The evaluator also
assumes that symbol satisfies the refinement carried by the actual subtree.
-}
withActualFor :: Position -> Position -> LiquidConstraint -> LiquidConstraint
withActualFor actual formal = withActualsFor [(actual, formal)]

-- | Apply several actual-for-formal substitutions to one semantic guard.
withActualsFor :: [(Position, Position)] -> LiquidConstraint -> LiquidConstraint
withActualsFor substitutions constraint =
    constraint
        { constraintGuard =
            Substitute (map substitution substitutions) $ constraintGuard constraint
        }
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

-- | Require the refinement at the left position to imply the right one.
refines :: Position -> Position -> LiquidConstraint
refines = isSubtypeOf

-- | Require both positions to contain the same annotated LTA term.
sameAs :: Position -> Position -> LiquidConstraint
sameAs = isSameTermAs
