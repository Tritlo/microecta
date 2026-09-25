{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}

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
    Literal (..),
    literal,
    Enumerated (..),
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
    definingTerm,
    freeNames,

    -- * Refinements
    Refinement,
    refinementFormula,
) where

import Data.Int (Int16, Int32, Int64, Int8)
import Data.Word (Word16, Word32, Word64, Word8)
import Numeric.Natural (Natural)

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

{- | Values that integers stand for, so that the logic writes each value as a
literal term.

The solver declares @v@ as an integer, so each value stands for one integer:
'toLiteral' gives the integer, and 'fromLiteral' gives the value back.
'literalRange' gives the least and the greatest value of a bounded type. A
generator infers the refinement @\\v -> v .== literal x@ for such a value,
and @every@ draws every value of such a type.

The instances write integral types as themselves, and 'Bool', 'Char',
'Ordering', and @()@ as their positions, 'fromEnum'. Derive an instance for a
bounded enumeration with 'Enumerated'.
-}
class Literal a where
    -- | The integer that stands for the value.
    toLiteral :: a -> Integer

    -- | The value that an integer stands for. The integer must stand for a value.
    fromLiteral :: Integer -> a

    -- | The least and the greatest value, if the type has them.
    literalRange :: (Maybe a, Maybe a)

-- | The term that denotes the value.
literal :: (Literal a) => a -> Expr
literal = fromInteger . toLiteral

instance Literal Integer where
    toLiteral = id
    fromLiteral = id
    literalRange = (Nothing, Nothing)

instance Literal Natural where
    toLiteral = toInteger
    fromLiteral = fromInteger
    literalRange = (Just 0, Nothing)

-- | Write the values of a bounded integral type as themselves.
newtype BoundedIntegral a = BoundedIntegral a

instance (Bounded a, Integral a) => Literal (BoundedIntegral a) where
    toLiteral (BoundedIntegral value) = toInteger value
    fromLiteral = BoundedIntegral . fromInteger
    literalRange = (Just $ BoundedIntegral minBound, Just $ BoundedIntegral maxBound)

deriving via BoundedIntegral Int instance Literal Int
deriving via BoundedIntegral Int8 instance Literal Int8
deriving via BoundedIntegral Int16 instance Literal Int16
deriving via BoundedIntegral Int32 instance Literal Int32
deriving via BoundedIntegral Int64 instance Literal Int64
deriving via BoundedIntegral Word instance Literal Word
deriving via BoundedIntegral Word8 instance Literal Word8
deriving via BoundedIntegral Word16 instance Literal Word16
deriving via BoundedIntegral Word32 instance Literal Word32
deriving via BoundedIntegral Word64 instance Literal Word64

{- | Write the values of a bounded enumeration as their positions, 'fromEnum'.

Derive the instance of an enumeration with @DerivingVia@:

@
data Color = Red | Green | Blue
    deriving (Bounded, Enum, Show)
    deriving (Literal) via (Enumerated Color)
@
-}
newtype Enumerated a = Enumerated a

instance (Bounded a, Enum a) => Literal (Enumerated a) where
    toLiteral (Enumerated value) = toInteger $ fromEnum value
    fromLiteral = Enumerated . toEnum . fromInteger
    literalRange = (Just $ Enumerated minBound, Just $ Enumerated maxBound)

deriving via Enumerated Bool instance Literal Bool
deriving via Enumerated Char instance Literal Char
deriving via Enumerated Ordering instance Literal Ordering
deriving via Enumerated () instance Literal ()

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

-- | The term @t@ of a formula @v .== t@ or @t .== v@ about the value @v@, if the formula has that form.
definingTerm :: Formula -> Maybe Expr
definingTerm formula = case formula of
    Fixpoint.PAtom Fixpoint.Eq (Fixpoint.EVar name) term | name == valueSymbol -> Just $ Expr term
    Fixpoint.PAtom Fixpoint.Eq term (Fixpoint.EVar name) | name == valueSymbol -> Just $ Expr term
    _ -> Nothing
  where
    valueSymbol = Fixpoint.symbol ("v" :: String)

-- | The names that occur free in a formula.
freeNames :: Formula -> [String]
freeNames = map Fixpoint.symbolString . Fixpoint.syms

relation :: Fixpoint.Brel -> Expr -> Expr -> Formula
relation operator (Expr left) (Expr right) = Fixpoint.PAtom operator left right

{- | A refinement: a formula about the refined value.

Write it as a function of the value, as in @\\v -> 0 .<= v .&& v .< n@.
-}
type Refinement = Expr -> Formula

-- | The formula of a refinement, stated about the value variable @v@.
refinementFormula :: Refinement -> Formula
refinementFormula refinement = refinement (variable "v")
