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
    Guard (And, Entails, Not, Or, Same, Satisfies, Substitute, Top),
    Refinement,
    Substitution (Substitution),
    path,
 )
import Numeric.Natural (Natural)

-- | A position relative to the root of the guarded constructor.
newtype Position = Position [Natural]

-- | The root/result of the guarded transition.
root :: Position
root = Position []

-- | A transition with no liquid constraint.
unconstrained :: Guard
unconstrained = Top

{- | A guard or a function over consecutive constructor arguments.

For example, @\actual expected -> actual `isSubtypeOf` expected@ receives
arguments zero and one without exposing those indices at the call site.
-}
class GuardBuilder guard where
    {- | Build a guard starting at the supplied argument index.
    Most callers should use 'buildGuard'.
    -}
    buildGuardFrom :: Natural -> guard -> Guard

instance GuardBuilder Guard where
    buildGuardFrom _ = id

instance (GuardBuilder guard) => GuardBuilder (Position -> guard) where
    buildGuardFrom index continue =
        buildGuardFrom (index + 1) (continue $ argument index)

-- | Turn a raw or argument-building guard into a concrete LTA guard.
buildGuard :: (GuardBuilder guard) => guard -> Guard
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
requires :: Position -> Refinement -> Guard
requires (Position target) = Satisfies (path $ map fromIntegral target)

-- | Require the left position's refinement to be a subtype of the right one.
isSubtypeOf :: Position -> Position -> Guard
isSubtypeOf (Position subtype) (Position supertype) =
    Entails
        (path $ map fromIntegral subtype)
        (path $ map fromIntegral supertype)

-- | Require both positions to contain the same unrefined term.
isSameTermAs :: Position -> Position -> Guard
isSameTermAs (Position left) (Position right) =
    Same (path $ map fromIntegral left) (path $ map fromIntegral right)

{- | Check a guard after substituting the actual position's symbol for the
formal position's symbol in every refinement predicate. The evaluator also
assumes that symbol satisfies the refinement carried by the actual subtree.
-}
withActualFor :: Position -> Position -> Guard -> Guard
withActualFor actual formal = withActualsFor [(actual, formal)]

-- | Apply several actual-for-formal substitutions to one semantic guard.
withActualsFor :: [(Position, Position)] -> Guard -> Guard
withActualsFor substitutions =
    Substitute $ map substitution substitutions
  where
    substitution (Position actual, Position formal) =
        Substitution
            (path $ map fromIntegral actual)
            (path $ map fromIntegral formal)

-- | Conjoin a collection of guard requirements.
allOf :: [Guard] -> Guard
allOf = And

-- | Accept when at least one guard requirement holds.
anyOf :: [Guard] -> Guard
anyOf = Or

-- | Negate one guard requirement.
notGuard :: Guard -> Guard
notGuard = Not

-- | Require the refinement at the left position to imply the right one.
refines :: Position -> Position -> Guard
refines = isSubtypeOf

-- | Require both positions to contain the same unrefined term.
sameAs :: Position -> Position -> Guard
sameAs = isSameTermAs
