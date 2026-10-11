{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{- | The formulas of the refinement logic.

A 'Formula' states a fact about named integer values. A 'Term' gives an
integer from names and literals. An atom compares two terms, and the
connectives combine formulas. The logic has no quantifiers, so 'substitute'
cannot capture a name.

'conjunction' and 'disjunction' simplify their result as the functions
@pAnd@ and @pOr@ of Liquid Fixpoint do. Formula equality decides the interning
of symbols and the hits of solver caches, so the simplification must not
change.

The constructor order of each type is the order of the matching constructors
of Liquid Fixpoint. The derived 'Ord' instances therefore order formulas as
Liquid Fixpoint does. 'conjunction' sorts its parts by this order, and symbols
with the same text sort by it.
-}
module Data.CFTA.Formula (
    Name (..),
    Term (..),
    Relation (..),
    Formula (..),
    conjunction,
    disjunction,
    implies,
    iff,
    freeNames,
    substitute,
) where

import qualified Data.HashSet as HashSet
import Data.Hashable (Hashable (..))
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.String (IsString (..))
import Data.Text (Text)
import qualified Data.Text as Text
import GHC.Generics (Generic)

-- | The name of an integer value. It shows as its text.
newtype Name = Name Text
    deriving newtype (Eq, Ord, Show)

{- | A name hashes as its text. The instance defines only 'hashWithSalt', so
'hash' uses the default salt, as for the symbols of Liquid Fixpoint. A hash set
of names then lists them in the order of Liquid Fixpoint, and 'freeNames'
keeps that order.
-}
instance Hashable Name where
    hashWithSalt salt (Name text) = hashWithSalt salt text

instance IsString Name where
    fromString = Name . Text.pack

-- | An integer term.
data Term
    = -- | An integer literal.
      Lit !Integer
    | -- | A named value.
      Var !Name
    | -- | The negation of a term.
      Neg !Term
    | -- | The sum of two terms.
      Add !Term !Term
    | -- | The difference of two terms.
      Sub !Term !Term
    | -- | The product of two terms.
      Mul !Term !Term
    | -- | The first term when the formula holds, and the second term when it does not.
      Ite !Formula !Term !Term
    deriving (Eq, Ord, Show, Generic)

instance Hashable Term

-- | A comparison of two terms.
data Relation = Eq | Ne | Gt | Ge | Lt | Le
    deriving (Eq, Ord, Show, Enum, Generic)

instance Hashable Relation

{- | A formula. 'Top' is the empty conjunction and 'Bottom' is the empty
disjunction: 'conjunction' and 'disjunction' do not give an 'And' or an 'Or'
without parts.
-}
data Formula
    = -- | The formula that always holds.
      Top
    | -- | All parts hold.
      And ![Formula]
    | -- | The formula that never holds.
      Bottom
    | -- | At least one part holds.
      Or ![Formula]
    | -- | The formula does not hold.
      Not !Formula
    | -- | The relation holds between the two terms.
      Atom !Relation !Term !Term
    deriving (Eq, Ord, Show, Generic)

instance Hashable Formula

{- | The conjunction of the formulas, simplified as @pAnd@ of Liquid Fixpoint.

A contradiction among the formulas gives 'Bottom'. Otherwise each formula is
simplified, and tautologies go. Nested conjunctions are flattened, and the
parts are sorted without duplicates. No part gives 'Top', and one part gives
that part.
-}
conjunction :: [Formula] -> Formula
conjunction = simplify . And

{- | The disjunction of the formulas, simplified as @pOr@ of Liquid Fixpoint.

A tautology among the formulas gives 'Top'. Otherwise each formula is
simplified, and contradictions go. The parts are not flattened, sorted, or
made distinct. One formula gives that formula, simplified. No remaining part
gives 'Bottom', and one remaining part gives an 'Or' of that part.
-}
disjunction :: [Formula] -> Formula
disjunction = simplify . Or

{- | Simplify a formula as @simplify@ of Liquid Fixpoint does.

Only a conjunction, a disjunction, or a negation changes below the root. A
negation of a negation becomes the inner formula. An atom that is a tautology
or a contradiction becomes 'Top' or 'Bottom'.
-}
simplify :: Formula -> Formula
simplify formula = case formula of
    Or [] -> Bottom
    Or [part] -> simplify part
    Not inner -> case simplify inner of
        Not negated -> negated
        simplified -> Not simplified
    And parts
        | any contradiction parts -> Bottom
        | otherwise -> case Set.toList $ Set.fromList $ flatten $ filter (not . tautology) $ map simplify parts of
            [] -> Top
            [part] -> part
            several -> And several
    Or parts
        | any tautology parts -> Top
        | otherwise -> case filter (not . contradiction) $ map simplify parts of
            [] -> Bottom
            kept -> Or kept
    _
        | contradiction formula -> Bottom
        | tautology formula -> Top
        | otherwise -> formula
  where
    flatten = concatMap $ \part -> case part of
        And nested -> flatten nested
        _ -> [part]

-- | Whether a formula is 'Top' or an atom that always holds.
tautology :: Formula -> Bool
tautology formula = case formula of
    Top -> True
    Atom Eq left right -> left == right
    Atom Le left right -> left == right
    Atom Ge left right -> left == right
    Atom Ne (Lit left) (Lit right) -> left /= right
    _ -> False

-- | Whether a formula is 'Bottom' or an atom that never holds.
contradiction :: Formula -> Bool
contradiction formula = case formula of
    Bottom -> True
    Atom Eq (Lit left) (Lit right) -> left /= right
    Atom Ne left right -> left == right
    _ -> False

-- | The first formula implies the second. The result is not simplified.
implies :: Formula -> Formula -> Formula
implies premise conclusion = Or [Not premise, conclusion]

-- | Both formulas hold or neither holds. The result is not simplified.
iff :: Formula -> Formula -> Formula
iff left right = Or [And [left, right], And [Not left, Not right]]

{- | The names in a formula, each once.

The order is the order of a hash set of the names, as for @syms@ of Liquid
Fixpoint. It is the same in each process.
-}
freeNames :: Formula -> [Name]
freeNames = HashSet.toList . inFormula
  where
    inFormula formula = case formula of
        Top -> HashSet.empty
        And parts -> foldMap inFormula parts
        Bottom -> HashSet.empty
        Or parts -> foldMap inFormula parts
        Not inner -> inFormula inner
        Atom _ left right -> inTerm left <> inTerm right
    inTerm term = case term of
        Lit _ -> HashSet.empty
        Var name -> HashSet.singleton name
        Neg inner -> inTerm inner
        Add left right -> inTerm left <> inTerm right
        Sub left right -> inTerm left <> inTerm right
        Mul left right -> inTerm left <> inTerm right
        Ite condition yes no -> inFormula condition <> inTerm yes <> inTerm no

{- | Replace names by terms, all at once.

For a name with more than one replacement, the first replacement applies. A
replacement of a name by the same name is ignored. The result is not
simplified.
-}
substitute :: [(Name, Term)] -> Formula -> Formula
substitute replacements = inFormula
  where
    active = filter (\(name, term) -> term /= Var name) replacements
    inFormula formula = case formula of
        And parts -> And $ map inFormula parts
        Or parts -> Or $ map inFormula parts
        Not inner -> Not $ inFormula inner
        Atom relation left right -> Atom relation (inTerm left) (inTerm right)
        _ -> formula
    inTerm term = case term of
        Var name -> fromMaybe term $ lookup name active
        Neg inner -> Neg $ inTerm inner
        Add left right -> Add (inTerm left) (inTerm right)
        Sub left right -> Sub (inTerm left) (inTerm right)
        Mul left right -> Mul (inTerm left) (inTerm right)
        Ite condition yes no -> Ite (inFormula condition) (inTerm yes) (inTerm no)
        Lit _ -> term
