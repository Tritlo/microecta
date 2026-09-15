-- | Small expression helpers over Liquid Fixpoint refinements.
module Data.LTA.Refinement (
    Expr,
    variable,
    integer,
    value,
    true,
    false,
    (.+.),
    (.-.),
    (.*.),
    (.==.),
    (./=.),
    (.<.),
    (.<=.),
    (.>.),
    (.>=.),
) where

import Data.LTA (Refinement)
import qualified Language.Fixpoint.Types as Fixpoint

-- | A Liquid Fixpoint expression. Its solver sort comes from declarations.
type Expr = Fixpoint.Expr

-- | Refer to a named value. This does not declare its solver sort.
variable :: String -> Expr
variable = Fixpoint.EVar . Fixpoint.symbol

-- | Build an integer literal without an overloaded numeric type.
integer :: Integer -> Expr
integer = Fixpoint.expr

{- | The conventional refinement variable named @v@.

Declare @v@ with the sort of the values described by the refinement.
Use 'variable' for other named inputs and formal parameters.
-}
value :: Expr
value = variable "v"

-- | The refinement that accepts every value.
true :: Refinement
true = Fixpoint.PTrue

-- | The refinement that accepts no values.
false :: Refinement
false = Fixpoint.PFalse

infixl 6 .+., .-.
infixl 7 .*.
infix 4 .==., ./=., .<., .<=., .>., .>=.

-- | Integer addition between two Liquid Fixpoint expressions.
(.+.) :: (Fixpoint.Expression left, Fixpoint.Expression right) => left -> right -> Expr
left .+. right = arithmetic Fixpoint.Plus left right

-- | Integer subtraction between two Liquid Fixpoint expressions.
(.-.) :: (Fixpoint.Expression left, Fixpoint.Expression right) => left -> right -> Expr
left .-. right = arithmetic Fixpoint.Minus left right

-- | Integer multiplication between two Liquid Fixpoint expressions.
(.*.) :: (Fixpoint.Expression left, Fixpoint.Expression right) => left -> right -> Expr
left .*. right = arithmetic Fixpoint.Times left right

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

arithmetic ::
    (Fixpoint.Expression left, Fixpoint.Expression right) =>
    Fixpoint.Bop ->
    left ->
    right ->
    Expr
arithmetic operator left right =
    Fixpoint.EBin operator (Fixpoint.expr left) (Fixpoint.expr right)
