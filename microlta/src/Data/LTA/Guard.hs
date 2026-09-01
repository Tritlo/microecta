{-# LANGUAGE FlexibleInstances #-}

-- | Guard syntax in terms of constructor arguments.
module Data.LTA.Guard (
    Position,
    GuardBuilder (buildGuardFrom),
    buildGuard,
    argument,
    descendant,
    refines,
    sameAs,
) where

import Data.LTA (Guard (Entails, Same), path)
import Numeric.Natural (Natural)

-- | A position relative to the root of the guarded constructor.
newtype Position = Position [Natural]

{- | A guard or a function over consecutive constructor arguments.

For example, @\left right -> left `refines` right@ receives arguments zero and
one without exposing those indices at the call site.
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

-- | Require the refinement at the left position to imply the right one.
refines :: Position -> Position -> Guard
refines (Position antecedent) (Position consequent) =
    Entails (path $ map fromIntegral antecedent) (path $ map fromIntegral consequent)

-- | Require both positions to contain the same unrefined term.
sameAs :: Position -> Position -> Guard
sameAs (Position left) (Position right) =
    Same (path $ map fromIntegral left) (path $ map fromIntegral right)
