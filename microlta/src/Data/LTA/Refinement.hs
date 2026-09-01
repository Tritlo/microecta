-- | Small expression helpers over Liquid Fixpoint refinements.
module Data.LTA.Refinement (
    true,
    false,
    (.==.),
    (./=.),
    (.<.),
    (.<=.),
    (.>.),
    (.>=.),
) where

import Data.LTA (Refinement)
import qualified Language.Fixpoint.Types as Fixpoint

-- | The refinement that accepts every value.
true :: Refinement
true = Fixpoint.PTrue

-- | The refinement that accepts no values.
false :: Refinement
false = Fixpoint.PFalse

infix 4 .==., ./=., .<., .<=., .>., .>=.

-- | Equality between two Liquid Fixpoint expressions.
(.==.) :: (Fixpoint.Expression left, Fixpoint.Expression right) => left -> right -> Refinement
left .==. right = relation Fixpoint.Eq left right

-- | Disequality between two Liquid Fixpoint expressions.
(./=.) :: (Fixpoint.Expression left, Fixpoint.Expression right) => left -> right -> Refinement
left ./=. right = relation Fixpoint.Ne left right

-- | Strictly-less-than between two Liquid Fixpoint expressions.
(.<.) :: (Fixpoint.Expression left, Fixpoint.Expression right) => left -> right -> Refinement
left .<. right = relation Fixpoint.Lt left right

-- | Less-than-or-equal between two Liquid Fixpoint expressions.
(.<=.) :: (Fixpoint.Expression left, Fixpoint.Expression right) => left -> right -> Refinement
left .<=. right = relation Fixpoint.Le left right

-- | Strictly-greater-than between two Liquid Fixpoint expressions.
(.>.) :: (Fixpoint.Expression left, Fixpoint.Expression right) => left -> right -> Refinement
left .>. right = relation Fixpoint.Gt left right

-- | Greater-than-or-equal between two Liquid Fixpoint expressions.
(.>=.) :: (Fixpoint.Expression left, Fixpoint.Expression right) => left -> right -> Refinement
left .>=. right = relation Fixpoint.Ge left right

relation ::
    (Fixpoint.Expression left, Fixpoint.Expression right) =>
    Fixpoint.Brel ->
    left ->
    right ->
    Refinement
relation operator left right =
    Fixpoint.PAtom operator (Fixpoint.expr left) (Fixpoint.expr right)
