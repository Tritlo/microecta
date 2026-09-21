{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}

{- | The Boolean constraint language carried by an LTA transition.

A 'LiquidConstraint' holds the authoritative Boolean 'Guard' and a compiled
cache of its positive syntactic equalities. This module only builds and
inspects constraints; "Data.CFTA.Refinement.Evaluate" decides them.
-}
module Data.CFTA.Refinement.Constraint (
    Guard (..),
    Substitution (..),
    LiquidConstraint (..),
    unconstrainedConstraint,
    semanticConstraint,
    equalityConstraint,
    combineConstraints,
    constraintAsGuard,
    equalityPathPairs,
    guardPaths,
    symbolSensitivePaths,
    constraintPaths,
    splitGuard,
    conjoin,
) where

import Data.Hashable (Hashable)
import Data.Maybe (isNothing)
import GHC.Generics (Generic)

import Data.CFTA.Constraint (Constraint (..), HasEqualities (..))
import Data.CFTA.Equality.Constraint (
    EqConstraints (EmptyConstraints),
    combineEqConstraints,
    constraintsAreContradictory,
    mkEqConstraints,
    subsumptionOrderedEclasses,
    unPathEClass,
 )
import Data.CFTA.Path (Path)

import Data.CFTA.Refinement.Types (Refinement)

-- | A transition guard over paths relative to the transition's root term.
data Guard
    = -- | The guard that always succeeds.
      Top
    | -- | The guard that always fails.
      Bottom
    | -- | Require the two paths to contain the same annotated LTA term.
      Same !Path !Path
    | -- | Require the refinement at the first path to imply the second.
      Entails !Path !Path
    | -- | Require the refinement at a path to imply a literal requirement.
      Satisfies !Path !Refinement
    | -- | Apply actual-for-formal substitutions before checking a guard.
      Substitute ![Substitution] !Guard
    | -- | Logical negation.
      Not !Guard
    | -- | Logical conjunction.
      And ![Guard]
    | -- | Logical disjunction.
      Or ![Guard]
    deriving (Eq, Show, Generic)

instance Hashable Guard

{- | A complete LTA constraint with an optional normalized equality cache.

The authoritative semantics is the full Boolean 'Guard', including 'Same'. The
equality field is a compiled positive-conjunction form that the equality
reduction and the enumerator use. 'constraintAsGuard' always recovers the complete paper-level
constraint, so the split representation cannot erase Boolean equality.
-}
data LiquidConstraint = LiquidConstraint
    { constraintEqualities :: !EqConstraints
    , constraintGuard :: !Guard
    }
    deriving (Eq, Show, Generic)

instance Hashable LiquidConstraint

{- | Pure construction operations. Semantic checks remain in the LTA layer.

The path equalities of a constraint are its cached equalities together with
the positive 'Same' atoms of its guard, so enumeration solves those by
unification. A guard with anything else, including a scoped or negated
equality, is a residual that the complete subterm must be checked against.
-}
instance HasEqualities LiquidConstraint where
    fromEqualities = equalityConstraint

instance Constraint LiquidConstraint where
    noConstraint = unconstrainedConstraint
    conjoinConstraints = combineConstraints
    contradictory LiquidConstraint{constraintEqualities, constraintGuard} =
        constraintsAreContradictory constraintEqualities || constraintGuard == Bottom
    equalities LiquidConstraint{constraintEqualities, constraintGuard} =
        maybe constraintEqualities (combineEqConstraints constraintEqualities) (positiveEqualities constraintGuard)
    residual LiquidConstraint{constraintGuard} = isNothing (positiveEqualities constraintGuard)

{- | The path equalities of a guard made only of 'Top', 'Same' between two
distinct paths, and 'And'. A reflexive 'Same' requires its path to exist and
is not an equality, so it stays a residual.
-}
positiveEqualities :: Guard -> Maybe EqConstraints
positiveEqualities Top = Just EmptyConstraints
positiveEqualities (Same left right)
    | left /= right = Just $ mkEqConstraints [[left, right]]
positiveEqualities (And guards) = foldr (\guard rest -> combineEqConstraints <$> positiveEqualities guard <*> rest) (Just EmptyConstraints) guards
positiveEqualities _ = Nothing

-- | A transition with neither equality nor liquid obligations.
unconstrainedConstraint :: LiquidConstraint
unconstrainedConstraint = LiquidConstraint EmptyConstraints Top

-- | Lift one complete guard into an LTA transition constraint.
semanticConstraint :: Guard -> LiquidConstraint
semanticConstraint = LiquidConstraint EmptyConstraints

-- | Lift normalized positive equalities into an LTA transition constraint.
equalityConstraint :: EqConstraints -> LiquidConstraint
equalityConstraint eqs = LiquidConstraint eqs Top

-- | Conjoin equality classes and semantic obligations.
combineConstraints :: LiquidConstraint -> LiquidConstraint -> LiquidConstraint
combineConstraints
    (LiquidConstraint leftEqualities leftGuard)
    (LiquidConstraint rightEqualities rightGuard) =
        LiquidConstraint
            (combineEqConstraints leftEqualities rightEqualities)
            (combineGuards leftGuard rightGuard)

-- | Recover the complete paper-level Boolean constraint.
constraintAsGuard :: LiquidConstraint -> Guard
constraintAsGuard LiquidConstraint{constraintEqualities, constraintGuard} =
    combineGuards (equalitiesAsGuard constraintEqualities) constraintGuard

{- | The normalized equality classes of a constraint set, as path lists.

The result is 'Nothing' when the classes are contradictory.
-}
equalityClasses :: EqConstraints -> Maybe [[Path]]
equalityClasses = fmap (map unPathEClass) . subsumptionOrderedEclasses

{- | Pair the anchor of each normalized equality class with its other members.

The pairs span the class, so they require exactly the terms the class requires.
The result is 'Nothing' when the classes are contradictory.
-}
equalityPathPairs :: EqConstraints -> Maybe [(Path, Path)]
equalityPathPairs = fmap (concatMap anchoredPairs) . equalityClasses
  where
    anchoredPairs [] = []
    anchoredPairs (anchor : rest) = map (anchor,) rest

-- | Reify normalized positive ECTA equalities as ordinary LTA atoms.
equalitiesAsGuard :: EqConstraints -> Guard
equalitiesAsGuard eqs =
    maybe Bottom (conjoin . map (uncurry Same)) $ equalityPathPairs eqs

{- | Replace the name at the formal path with the name at the actual path while
evaluating a guard. 'Same' compares renamed symbols and refinement annotations.
The instantiated refinement carried by the actual subtree is added to each
resulting entailment antecedent. The candidate term itself stays unchanged.

This is the paper's @[actual/formal]@ position substitution. Both positions are
relative to the root of the guarded transition.
-}
data Substitution = Substitution
    { substitutionActual :: !Path
    , substitutionFormal :: !Path
    }
    deriving (Eq, Show, Generic)

instance Hashable Substitution

{- | Collect the term positions of one guard with an atom selector.

The traversal always collects both positions of every substitution. The
selector decides which positions of the atoms below it are collected.
-}
collectGuardPaths :: (Guard -> [Path]) -> Guard -> [Path]
collectGuardPaths atomPaths = go
  where
    go (Substitute substitutions nested) =
        concatMap substitutionPaths substitutions <> go nested
    go (Not nested) = go nested
    go (And guards) = concatMap go guards
    go (Or guards) = concatMap go guards
    go atom = atomPaths atom

    substitutionPaths Substitution{substitutionActual, substitutionFormal} =
        [substitutionActual, substitutionFormal]

-- | Every term position inspected by a guard, including substitutions.
guardPaths :: Guard -> [Path]
guardPaths = collectGuardPaths atomPaths
  where
    atomPaths (Same left right) = [left, right]
    atomPaths (Entails antecedent consequent) = [antecedent, consequent]
    atomPaths (Satisfies target _) = [target]
    atomPaths _ = []

-- | Paths whose constructor symbol participates in substitution.
symbolSensitivePaths :: Guard -> [Path]
symbolSensitivePaths = collectGuardPaths atomPaths
  where
    atomPaths (Same left right) = [left, right]
    atomPaths _ = []

-- | Every term position inspected by either transition constraint theory.
constraintPaths :: LiquidConstraint -> [Path]
constraintPaths LiquidConstraint{constraintEqualities, constraintGuard} =
    maybe [] concat (equalityClasses constraintEqualities) <> guardPaths constraintGuard

-- | Conjoin two complete guards.
combineGuards :: Guard -> Guard -> Guard
combineGuards Top right = right
combineGuards left Top = left
combineGuards left right
    | left == right = left
    | otherwise = And [left, right]

-- | Split independently reducible semantic conjuncts from syntactic equality.
splitGuard :: Guard -> (Guard, Guard)
splitGuard guard
    | not $ containsSame guard = (guard, Top)
splitGuard (And guards) =
    (conjoin semantic, conjoin structural)
  where
    (semantic, structural) = foldr separate ([], []) guards
    separate nested (semanticGuards, structuralGuards) =
        let (semanticGuard, structuralGuard) = splitGuard nested
         in ( prepend semanticGuard semanticGuards
            , prepend structuralGuard structuralGuards
            )

    prepend Top rest = rest
    prepend guard rest = guard : rest
splitGuard guard = (Top, guard)

-- | Whether a Boolean constraint contains syntactic equality.
containsSame :: Guard -> Bool
containsSame Top = False
containsSame Bottom = False
containsSame (Same _ _) = True
containsSame (Entails _ _) = False
containsSame (Satisfies _ _) = False
containsSame (Substitute _ nested) = containsSame nested
containsSame (Not nested) = containsSame nested
containsSame (And guards) = any containsSame guards
containsSame (Or guards) = any containsSame guards

-- | Build a conjunction without redundant Boolean structure.
conjoin :: [Guard] -> Guard
conjoin [] = Top
conjoin [guard] = guard
conjoin guards = And guards
