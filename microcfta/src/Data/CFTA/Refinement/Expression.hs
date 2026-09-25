{- | The refinement logic: terms, formulas, and refinements.

A refinement is a Haskell function from the refined value to a formula, as in
@\\v -> v ./= 0@. Terms support integer literals and arithmetic through 'Num',
so @\\v -> v .== 2 * n + 1@ needs no conversion. The comparison operators
take two terms and give a formula. The connectives combine formulas.
-}
module Data.CFTA.Refinement.Expression (
    -- * Terms
    Expr,
    variable,
    Literal (literal),
    fromExpr,
    toExpr,

    -- * Formulas
    Formula,
    true,
    false,
    (.==),
    (./=),
    (.<),
    (.<=),
    (.>),
    (.>=),
    (.&&),
    (.||),
    lnot,
    substitute,

    -- * Refinements
    Refinement,
    refinementFormula,
) where

import Data.CFTA.Refinement (Formula)
import qualified Language.Fixpoint.Types as Fixpoint

-- | A term of the refinement logic. Its solver sort comes from declarations.
newtype Expr = Expr Fixpoint.Expr
    deriving (Eq, Show)

-- | Integer literals and arithmetic build terms. A negative literal is one constant.
instance Num Expr where
    Expr left + Expr right = Expr $ Fixpoint.EBin Fixpoint.Plus left right
    Expr left - Expr right = Expr $ Fixpoint.EBin Fixpoint.Minus left right
    Expr left * Expr right = Expr $ Fixpoint.EBin Fixpoint.Times left right
    negate (Expr (Fixpoint.ECon (Fixpoint.I constant))) = Expr $ Fixpoint.ECon $ Fixpoint.I $ negate constant
    negate (Expr term) = Expr $ Fixpoint.ENeg term
    abs term = conditional (term .>= 0) term (negate term)
    signum term = conditional (term .> 0) 1 (conditional (term .== 0) 0 (-1))
    fromInteger = Expr . Fixpoint.expr

-- | Choose between two terms by a formula.
conditional :: Formula -> Expr -> Expr -> Expr
conditional condition (Expr yes) (Expr no) = Expr $ Fixpoint.EIte condition yes no

{- | Values that the logic writes as a literal term.

A generator infers the refinement @\\v -> v .== literal x@ for such a value.
The solver declares @v@ as an integer, so the instances are integers.
-}
class Literal a where
    -- | The term that denotes the value.
    literal :: a -> Expr

instance Literal Integer where
    literal = fromInteger

instance Literal Int where
    literal = fromIntegral

-- | Refer to a named value. This does not declare its solver sort.
variable :: String -> Expr
variable = Expr . Fixpoint.EVar . Fixpoint.symbol

-- | The Liquid Fixpoint expression of a term.
fromExpr :: Expr -> Fixpoint.Expr
fromExpr (Expr term) = term

-- | Use a Liquid Fixpoint expression as a term.
toExpr :: Fixpoint.Expr -> Expr
toExpr = Expr

-- | The formula that every value satisfies.
true :: Formula
true = Fixpoint.PTrue

-- | The formula that no value satisfies.
false :: Formula
false = Fixpoint.PFalse

infix 4 .==, ./=, .<, .<=, .>, .>=
infixr 3 .&&
infixr 2 .||

-- | The two terms are equal.
(.==) :: Expr -> Expr -> Formula
(.==) = relation Fixpoint.Eq

-- | The two terms are different.
(./=) :: Expr -> Expr -> Formula
(./=) = relation Fixpoint.Ne

-- | The first term is less than the second.
(.<) :: Expr -> Expr -> Formula
(.<) = relation Fixpoint.Lt

-- | The first term is less than or equal to the second.
(.<=) :: Expr -> Expr -> Formula
(.<=) = relation Fixpoint.Le

-- | The first term is greater than the second.
(.>) :: Expr -> Expr -> Formula
(.>) = relation Fixpoint.Gt

-- | The first term is greater than or equal to the second.
(.>=) :: Expr -> Expr -> Formula
(.>=) = relation Fixpoint.Ge

-- | Both formulas hold.
(.&&) :: Formula -> Formula -> Formula
left .&& right = Fixpoint.pAnd [left, right]

-- | At least one formula holds.
(.||) :: Formula -> Formula -> Formula
left .|| right = Fixpoint.pOr [left, right]

-- | The formula does not hold.
lnot :: Formula -> Formula
lnot = Fixpoint.PNot

-- | Replace named values in a formula by terms, all at once.
substitute :: [(String, Expr)] -> Formula -> Formula
substitute replacements =
    Fixpoint.subst $ Fixpoint.mkSubst [(Fixpoint.symbol name, term) | (name, Expr term) <- replacements]

relation :: Fixpoint.Brel -> Expr -> Expr -> Formula
relation operator (Expr left) (Expr right) = Fixpoint.PAtom operator left right

{- | A refinement: a formula about the refined value.

Write it as a function of the value, as in @\\v -> 0 .<= v .&& v .< n@.
-}
type Refinement = Expr -> Formula

-- | The formula of a refinement, stated about the value variable @v@.
refinementFormula :: Refinement -> Formula
refinementFormula refinement = refinement (variable "v")
