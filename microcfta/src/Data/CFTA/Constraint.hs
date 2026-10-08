{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}

{- | The transition constraints of the automata.

A 'Constraint' is a set of path equalities and a Boolean 'Guard'. An ordinary
tree automaton has no constraints ('noConstraint'). An equality automaton has
path equalities ('equalityConstraint'). A liquid tree automaton also has guards
that a solver decides ('semanticConstraint'). One type serves all three, so an
operation on automata is written once.

The guard is the complete semantics, including 'Same'. The equality field is
a compiled positive-conjunction form that the equality reduction and the
enumerator use. 'constraintAsGuard' recovers the complete constraint. This
module only builds and inspects constraints: "Data.CFTA.Refinement.Evaluate"
decides guards, and the equality engine decides equalities.

Every constraint exposes the path equalities it requires ('equalities').
Enumeration solves those by unification, and hands a constraint with a
'residual' to a check together with the complete subterm. Symbolic counting
reads a constraint as 'indicators': a signed sum of equality indicators, where
each summand is a weight and the path classes that must exist and hold equal
subterms. A guard with only Boolean structure over equalities has that form;
one that needs a solver does not.
-}
module Data.CFTA.Constraint (
    -- * Constraints
    Constraint (..),
    Guard (..),
    Substitution (..),
    noConstraint,
    equalityConstraint,
    semanticConstraint,
    conjoinConstraints,

    -- * Inspection
    contradictory,
    equalities,
    equalitiesHold,
    residual,
    indicators,
    equalityIndicators,
    constraintAsGuard,
    constraintIndicators,
    equalityPathPairs,
    guardPaths,
    symbolSensitivePaths,
    constraintPaths,
    splitGuard,
    conjoin,
    contractTermName,
) where

import Data.Hashable (Hashable)
import Data.Maybe (isNothing)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import GHC.Generics (Generic)

import Data.CFTA.Equality.Constraint (
    EqConstraints (EmptyConstraints, EqConstraints, EqContradiction),
    combineEqConstraints,
    constraintsAreContradictory,
    mkEqConstraints,
    subsumptionOrderedEclasses,
    unPathEClass,
 )
import Data.CFTA.Path (Path, getPath)
import Data.CFTA.Symbol (Formula)

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
      Satisfies !Path !Formula
    | {- | Require a formula about the terms at the paths. The formula names the
      term at the path with index @i@ by 'contractTermName' @i@, and each term's
      refinement is assumed for its name.
      -}
      Holds ![Path] !Formula
    | -- | Apply actual-for-formal substitutions before checking a guard.
      Substitute ![Substitution] !Guard
    | {- | Logical negation. The negation of 'Satisfies' or 'Holds' requires
      the refinements to refute the formula.
      -}
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
reduction and the enumerator use. 'constraintAsGuard' always recovers the
complete paper-level constraint, so the split representation cannot erase
Boolean equality.
-}
data Constraint = Constraint
    { constraintEqualities :: !EqConstraints
    , constraintGuard :: !Guard
    }
    deriving (Eq, Show, Generic)

instance Hashable Constraint

{- | Whether a constraint is impossible. This recognizes contradictory
equalities and the guard 'Bottom' without a solver; a constraint that only a
solver can refute is not recognized.
-}
contradictory :: Constraint -> Bool
contradictory Constraint{constraintEqualities, constraintGuard} =
    constraintsAreContradictory constraintEqualities || constraintGuard == Bottom

{- | The path equalities of a constraint: its cached equalities together with
the positive 'Same' atoms of its guard. Enumeration solves these by
unification.
-}
equalities :: Constraint -> EqConstraints
equalities Constraint{constraintEqualities, constraintGuard} =
    case positiveEqualities constraintGuard of
        -- The stored equalities are normalized, so a guard without 'Same'
        -- atoms adds nothing, and the memoized combination is not needed.
        Just EmptyConstraints -> constraintEqualities
        Just guardEqualities -> combineEqConstraints constraintEqualities guardEqualities
        Nothing -> constraintEqualities

{- | Whether a complete term satisfies the path equalities of a constraint.

Every path of a class must exist in the term, as in enumeration, and the
subterms at the paths must be equal. A constraint that 'contradictory'
recognizes, such as contradictory equalities or the guard 'Bottom', holds for
no term, as interning drops its edge. The rest of the residual beyond the
equalities is not decided here.
-}
equalitiesHold :: (Eq symbol) => Constraint -> Tree.Tree symbol -> Bool
equalitiesHold constraint term
    | contradictory constraint = False
    | otherwise = case equalities constraint of
        EqContradiction -> False
        EqConstraints classes -> all (maybe False allSame . traverse (`getPath` term) . Set.toList . unPathEClass) classes
  where
    allSame (first : rest) = all (== first) rest
    allSame [] = True

{- | Whether a constraint requires more than its path equalities. A guard with
anything but positive 'Same' atoms, including a scoped or negated equality, is
a residual that the complete subterm must be checked against.
-}
residual :: Constraint -> Bool
residual Constraint{constraintGuard} = isNothing $ positiveEqualities constraintGuard

-- | The constraint as a signed sum of equality indicators, if it has one.
indicators :: Constraint -> Maybe [(Integer, [[Path]])]
indicators = either (const Nothing) Just . constraintIndicators

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

{- | Express a constraint as a signed sum of equality indicators.

'Top', 'Bottom', 'Same', 'Not', 'And', and 'Or' have an inclusion-exclusion
form. A guard that needs a solver, or a substitution, is returned as the
residual it is.
-}
constraintIndicators :: Constraint -> Either Guard [(Integer, [[Path]])]
constraintIndicators Constraint{constraintEqualities, constraintGuard} =
    conjoinTerms (equalityIndicators constraintEqualities) <$> guardTerms constraintGuard
  where
    guardTerms Top = Right [(1, [])]
    guardTerms Bottom = Right []
    guardTerms (Same left right) = Right [(1, [[left, right]])]
    guardTerms (Not guard) = complement <$> guardTerms guard
    guardTerms (And guards) = foldl' conjoinTerms [(1, [])] <$> traverse guardTerms guards
    guardTerms (Or guards) = complement . foldl' conjoinTerms [(1, [])] . map complement <$> traverse guardTerms guards
    guardTerms guard = Left guard

    complement summands = (1, []) : [(negate weight, classes) | (weight, classes) <- summands]
    conjoinTerms left right =
        [ (leftWeight * rightWeight, leftClasses <> rightClasses)
        | (leftWeight, leftClasses) <- left
        , (rightWeight, rightClasses) <- right
        ]

-- | A transition with neither equality nor liquid obligations.
noConstraint :: Constraint
noConstraint = Constraint EmptyConstraints Top

-- | Lift one complete guard into an LTA transition constraint.
semanticConstraint :: Guard -> Constraint
semanticConstraint = Constraint EmptyConstraints

-- | Lift normalized positive equalities into an LTA transition constraint.
equalityConstraint :: EqConstraints -> Constraint
equalityConstraint eqs = Constraint eqs Top

-- | Conjoin equality classes and semantic obligations.
conjoinConstraints :: Constraint -> Constraint -> Constraint
conjoinConstraints
    (Constraint leftEqualities leftGuard)
    (Constraint rightEqualities rightGuard) =
        Constraint
            (combineEqConstraints leftEqualities rightEqualities)
            (combineGuards leftGuard rightGuard)

-- | Recover the complete paper-level Boolean constraint.
constraintAsGuard :: Constraint -> Guard
constraintAsGuard Constraint{constraintEqualities, constraintGuard} =
    combineGuards (equalitiesAsGuard constraintEqualities) constraintGuard

{- | The normalized equality classes of a constraint set.

The result is 'Nothing' when the classes are contradictory.
-}
equalityClasses :: EqConstraints -> Maybe [Set Path]
equalityClasses = fmap (map unPathEClass) . subsumptionOrderedEclasses

{- | Pair the anchor of each normalized equality class with its other members.

The pairs span the class, so they require exactly the terms the class requires.
The result is 'Nothing' when the classes are contradictory.
-}
equalityPathPairs :: EqConstraints -> Maybe [(Path, Path)]
equalityPathPairs = fmap (concatMap anchoredPairs) . equalityClasses
  where
    -- The least path of a class is its anchor.
    anchoredPairs paths = case Set.minView paths of
        Nothing -> []
        Just (anchor, rest) -> map (anchor,) $ Set.toAscList rest

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
    atomPaths (Holds targets _) = targets
    atomPaths _ = []

-- | Paths whose constructor symbol participates in substitution.
symbolSensitivePaths :: Guard -> [Path]
symbolSensitivePaths = collectGuardPaths atomPaths
  where
    atomPaths (Same left right) = [left, right]
    atomPaths _ = []

-- | Every term position inspected by either transition constraint theory.
constraintPaths :: Constraint -> [Path]
constraintPaths Constraint{constraintEqualities, constraintGuard} =
    maybe [] (concatMap Set.toAscList) (equalityClasses constraintEqualities) <> guardPaths constraintGuard

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
      where
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
containsSame (Holds _ _) = False
containsSame (Substitute _ nested) = containsSame nested
containsSame (Not nested) = containsSame nested
containsSame (And guards) = any containsSame guards
containsSame (Or guards) = any containsSame guards

{- | The reserved solver name of the term at one path of a 'Holds' guard.

The name starts with the reserved prefix @__microcfta_@, which the library
also uses for its integer and pool names. 'Data.CFTA.Refinement.Expression.variable'
documents the reservation. A user name with that prefix can collide with these
names, and nothing checks for such a name.
-}
contractTermName :: Int -> String
contractTermName index = "__microcfta_contract_" <> show index

-- | Build a conjunction without redundant Boolean structure.
conjoin :: [Guard] -> Guard
conjoin [] = Top
conjoin [guard] = guard
conjoin guards = And guards

-- | Path equality classes as one indicator summand, or none when contradictory.
equalityIndicators :: EqConstraints -> [(Integer, [[Path]])]
equalityIndicators =
    maybe [] (\classes -> [(1, map (Set.toAscList . unPathEClass) classes)]) . subsumptionOrderedEclasses
