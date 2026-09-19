-- | Pure operations used by the interned automaton engine.
module Data.CFTA.Constraint (Constraint (..)) where

import Data.Hashable (Hashable)
import Data.Typeable (Typeable)

{- | A constraint theory with a pure conjunction operation.

Conjunction must be associative, commutative, and idempotent in denotation.
'noConstraint' is its identity. 'contradictory' must return 'True' only for
an impossible constraint. It can return 'False' when a solver would be needed.
These operations do not evaluate a constraint against a concrete term.
-}
class (Hashable constraint, Typeable constraint) => Constraint constraint where
    -- | Constraint that permits every term.
    noConstraint :: constraint

    -- | Require both constraints.
    conjoinConstraints :: constraint -> constraint -> constraint

    -- | Recognize a contradiction without a solver.
    contradictory :: constraint -> Bool

instance Constraint () where
    noConstraint = ()
    conjoinConstraints _ _ = ()
    contradictory _ = False
