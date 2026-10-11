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
import Data.String (fromString)
import qualified Data.Text as Text
import Data.Word (Word16, Word32, Word64, Word8)
import Numeric.Natural (Natural)

import Data.CFTA.Formula (Formula (..), Name (..), Relation (..), Term (..), conjunction, disjunction)
import qualified Data.CFTA.Formula as Formula
import Data.CFTA.Symbol (valueName)

-- | A term of the refinement logic: an integer.
newtype Expr = Expr Term
    deriving (Eq, Show)

-- | Integer literals and arithmetic build terms. A negative literal is one constant.
instance Num Expr where
    Expr left + Expr right = Expr $ Add left right
    Expr left - Expr right = Expr $ Sub left right
    Expr left * Expr right = Expr $ Mul left right
    negate (Expr (Lit constant)) = Expr $ Lit $ negate constant
    negate (Expr term) = Expr $ Neg term
    abs term = conditional (term .>= 0) term (negate term)
    signum term = conditional (term .> 0) 1 (conditional (term .== 0) 0 (-1))
    fromInteger = Expr . Lit

-- | Choose between two terms by a formula.
conditional :: Formula -> Expr -> Expr -> Expr
conditional condition (Expr yes) (Expr no) = Expr $ Ite condition yes no

{- | Values that integers stand for, so that the logic writes each value as a
literal term.

The solver declares the value 'valueName' as an integer, so each value stands
for one integer: 'toLiteral' gives the integer, and 'fromLiteral' gives the
value back. 'literalRange' gives the least and the greatest value of a
bounded type. A generator infers the refinement @\\v -> v .== literal x@ for
such a value, and @every@ draws every value of such a type.

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

{- | Refer to a named value. This does not declare its solver sort.

Names that start with @__cfta_@ are reserved for the solver names that
the library makes. A user name with that prefix can collide with them.
-}
variable :: String -> Expr
variable = Expr . Var . fromString

-- | The 'Term' of an expression.
fromExpr :: Expr -> Term
fromExpr (Expr term) = term

-- | Use a 'Term' as an expression.
toExpr :: Term -> Expr
toExpr = Expr

-- | The formula that every value satisfies.
true :: Formula
true = Top

-- | The formula that no value satisfies.
false :: Formula
false = Bottom

infix 4 .==, ./=, .<, .<=, .>, .>=
infixr 3 .&&
infixr 2 .||

-- | The two terms are equal.
(.==) :: Expr -> Expr -> Formula
(.==) = relation Eq

-- | The two terms are different.
(./=) :: Expr -> Expr -> Formula
(./=) = relation Ne

-- | The first term is less than the second.
(.<) :: Expr -> Expr -> Formula
(.<) = relation Lt

-- | The first term is less than or equal to the second.
(.<=) :: Expr -> Expr -> Formula
(.<=) = relation Le

-- | The first term is greater than the second.
(.>) :: Expr -> Expr -> Formula
(.>) = relation Gt

-- | The first term is greater than or equal to the second.
(.>=) :: Expr -> Expr -> Formula
(.>=) = relation Ge

-- | Both formulas hold.
(.&&) :: Formula -> Formula -> Formula
left .&& right = conjunction [left, right]

-- | At least one formula holds.
(.||) :: Formula -> Formula -> Formula
left .|| right = disjunction [left, right]

-- | The formula does not hold.
lnot :: Formula -> Formula
lnot = Not

{- | Replace named values in a formula by terms, all at once.

For a name with more than one replacement, the first replacement applies.
-}
substitute :: [(String, Expr)] -> Formula -> Formula
substitute replacements = Formula.substitute [(fromString name, term) | (name, Expr term) <- replacements]

{- | The term @t@ of a formula @v .== t@ or @t .== v@, where @v@ is the value
'valueName', if the formula has that form.
-}
definingTerm :: Formula -> Maybe Expr
definingTerm formula = case formula of
    Atom Eq (Var name) term | name == value -> Just $ Expr term
    Atom Eq term (Var name) | name == value -> Just $ Expr term
    _ -> Nothing
  where
    value = fromString valueName

-- | The names that occur in a formula, each once, in the order of 'Formula.freeNames'.
freeNames :: Formula -> [String]
freeNames formula = [Text.unpack text | Name text <- Formula.freeNames formula]

-- | The atom that compares two terms with a relation.
relation :: Relation -> Expr -> Expr -> Formula
relation operator (Expr left) (Expr right) = Atom operator left right

{- | A refinement: a formula about the refined value.

Write it as a function of the value, as in @\\v -> 0 .<= v .&& v .< n@.
-}
type Refinement = Expr -> Formula

-- | The formula of a refinement, stated about the value variable 'valueName'.
refinementFormula :: Refinement -> Formula
refinementFormula refinement = refinement (variable valueName)
