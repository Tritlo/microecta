-- | The constraint theories of the automaton engine.
module Data.CFTA.Constraint (Constraint (..)) where

import Data.Hashable (Hashable)
import Data.Typeable (Typeable)

import Data.CFTA.Constraint.Equality (
    EqConstraints (EmptyConstraints),
    combineEqConstraints,
    constraintsAreContradictory,
 )

{- | A constraint theory with a pure conjunction operation.

Conjunction must be associative, commutative, and idempotent in denotation.
'noConstraint' is its identity. 'contradictory' must return 'True' only for
an impossible constraint. It can return 'False' when a solver would be needed.
These operations do not evaluate a constraint against a concrete term.

Every theory exposes the path equalities it requires. Enumeration solves
those by unification and hands a constraint with a 'residual' to a check
together with the complete subterm.
-}
class (Hashable constraint, Typeable constraint) => Constraint constraint where
    -- | Constraint that permits every term.
    noConstraint :: constraint

    -- | Require both constraints.
    conjoinConstraints :: constraint -> constraint -> constraint

    -- | Recognize a contradiction without a solver.
    contradictory :: constraint -> Bool

    -- | The path equalities the constraint requires.
    equalities :: constraint -> EqConstraints

    -- | Whether the constraint requires more than its path equalities.
    residual :: constraint -> Bool

instance Constraint () where
    noConstraint = ()
    conjoinConstraints _ _ = ()
    contradictory _ = False
    equalities _ = EmptyConstraints
    residual _ = False

instance Constraint EqConstraints where
    noConstraint = EmptyConstraints
    conjoinConstraints = combineEqConstraints
    contradictory = constraintsAreContradictory
    equalities = id
    residual _ = False
