{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Guard syntax in terms of constructor arguments.
module Data.LTA.Guard (
    Position,
    GuardBuilder (buildGuardFrom, guardArgumentCount),
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
) where

import Data.LTA (
    Guard (Entails, Not, Or, Same, Satisfies, Substitute),
    LiquidConstraint,
    Refinement,
    Substitution (Substitution),
    combineConstraints,
    constraintAsGuard,
    path,
    semanticConstraint,
    unconstrainedConstraint,
 )
import Data.Maybe (fromMaybe)
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
