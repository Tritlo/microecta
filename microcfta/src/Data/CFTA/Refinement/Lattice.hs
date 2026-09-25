{- | Count and rank the integer points that a linear formula admits.

A formula over named integer variables, with linear atoms and the connectives,
describes a finite union of polytopes. 'points' writes the formula as a signed
sum of conjunctions, by inclusion and exclusion, and sums the variables out
from the last to the first, as in
Pugh, "Counting solutions to Presburger formulas: how and why" (PLDI 1994).
At each step the number of completions is a sum of polynomials over
polyhedral pieces, and the Faulhaber formulas give each sum in closed form.
'pointCount' is therefore exact without enumeration. 'pointAt' decodes a rank
in lexicographic order, with one binary search for each variable.

Every variable must be bounded. When a variable is summed out, its coefficient
in each bound must be one or minus one after the bound is divided by the
greatest common divisor of its coefficients. Other formulas give a
'LatticeError'.
-}
module Data.CFTA.Refinement.Lattice (
    LatticeError (..),
    Points,
    points,
    pointCount,
    pointAt,
    onlyPoint,
) where

import Control.Monad (when)
import Data.Either (lefts, rights)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.List (elemIndex, partition)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Ratio (denominator, numerator)
import qualified Language.Fixpoint.Types as Fixpoint

import Data.CFTA.Refinement.Types (Formula)

-- | Why the integer points of a formula cannot be counted.
data LatticeError
    = -- | A term multiplies two variables, divides, or applies a function.
      NonLinearTerm !Formula
    | -- | The formula uses a form other than linear atoms and connectives.
      UnsupportedFormula !Formula
    | -- | The formula names a variable that is not in the list of variables.
      UnknownName !Fixpoint.Symbol
    | -- | No bound limits the variable in one direction.
      UnboundedVariable !Fixpoint.Symbol
    | -- | A bound has a coefficient other than one or minus one on the variable.
      NonUnitCoefficient !Fixpoint.Symbol
    deriving (Eq, Show)

{- | The integer points of a formula, ready to count and decode.

Level @k@ holds the number of completions of the first @k@ variables, as a
sum of polynomials over polyhedral pieces.
-}
data Points = Points !Int [[Piece]] !Integer

-- | The number of integer points.
pointCount :: Points -> Integer
pointCount (Points _ _ total) = total

{- | Collect the integer points of a formula over the given variables.

The order of the variables is the lexicographic order of the ranks.
-}
points :: [String] -> Formula -> Either LatticeError Points
points names formula = do
    terms <- signed variableOf formula
    let initial = [Piece region $ polynomialConstant $ fromInteger sign | (region, sign) <- Map.toList terms]
    levels <- sumOut (dimension - 1) [initial]
    total <- integral $ sum [polynomialValue polynomial | Piece _ polynomial <- concat $ take 1 levels]
    pure $ Points dimension levels total
  where
    dimension = length names
    symbols = map Fixpoint.symbol names
    variableOf name = elemIndex name symbols
    sumOut variable levels@(current : _)
        | variable < 0 = Right levels
        | otherwise = do
            next <- eliminate (symbols !! variable) variable current
            sumOut (variable - 1) (next : levels)
    sumOut _ [] = Right []
    integral value
        | denominator value == 1 = Right $ numerator value
        | otherwise =
            error
                "microcfta bug in Data.CFTA.Refinement.Lattice.points: \
                \a count is not an integer"

-- | The one integer that a formula admits for the variable, if it admits exactly one.
onlyPoint :: String -> Formula -> Maybe Integer
onlyPoint name formula = case points [name] formula of
    Right found | pointCount found == 1, [value] <- pointAt found 0 -> Just value
    _ -> Nothing

{- | The point at a rank, in lexicographic order of the variables.

The rank must be at least zero and less than 'pointCount'.
-}
pointAt :: Points -> Integer -> [Integer]
pointAt (Points dimension levels _) = go 0 IntMap.empty
  where
    go variable prefix rank
        | variable == dimension = IntMap.elems prefix
        | otherwise =
            let candidates =
                    [ (low, high, sumOver variable (constant low) upTo $ substitute prefix polynomial)
                    | Piece region polynomial <- levels !! (variable + 1)
                    , Just (low, high) <- [interval variable prefix region]
                    ]
                -- The sum from the low end up to the variable itself, once for each piece.
                upTo = Linear (IntMap.singleton variable 1) 0
                through bound =
                    sum
                        [ polynomialValue $ substitute (IntMap.singleton variable $ min high bound) cumulative
                        | (low, high, cumulative) <- candidates
                        , min high bound >= low
                        ]
                value =
                    search
                        (minimum [low | (low, _, _) <- candidates])
                        (maximum [high | (_, high, _) <- candidates])
                        (\bound -> through bound > fromInteger rank)
             in go (variable + 1) (IntMap.insert variable value prefix) (rank - numerator (through $ value - 1))

{- | The interval of one variable in a region, when the earlier variables have
the given values.
-}
interval :: Int -> IntMap Integer -> [Linear] -> Maybe (Integer, Integer)
interval variable prefix = foldr (narrow . substituteLinear prefix) (Just (minimumBound, maximumBound))
  where
    -- The pieces bound every variable, so these limits only start the fold.
    minimumBound = negate maximumBound
    maximumBound = 2 ^ (256 :: Int)
    narrow _ Nothing = Nothing
    narrow (Linear coefficients offset) (Just (low, high)) = case IntMap.findWithDefault 0 variable coefficients of
        0
            | offset >= 0 -> Just (low, high)
            | otherwise -> Nothing
        coefficient
            | coefficient > 0 -> nonEmpty (max low $ negate $ offset `div` coefficient) high
            | otherwise -> nonEmpty low (min high $ offset `div` negate coefficient)
    nonEmpty low high
        | low <= high = Just (low, high)
        | otherwise = Nothing

-- | The smallest value in an interval that satisfies a monotone predicate.
search :: Integer -> Integer -> (Integer -> Bool) -> Integer
search low high predicate
    | low >= high = low
    | predicate middle = search low middle predicate
    | otherwise = search (middle + 1) high predicate
  where
    middle = low + (high - low) `div` 2

-- Linear forms

-- | A linear form: the coefficient of each variable, and a constant.
data Linear = Linear !(IntMap Integer) !Integer
    deriving (Eq, Ord, Show)

-- | A form without variables.
constant :: Integer -> Linear
constant = Linear IntMap.empty

-- | The sum of two forms.
plus :: Linear -> Linear -> Linear
plus (Linear left leftOffset) (Linear right rightOffset) =
    Linear (IntMap.filter (/= 0) $ IntMap.unionWith (+) left right) (leftOffset + rightOffset)

-- | The difference of two forms.
minus :: Linear -> Linear -> Linear
minus left right = plus left $ scale (-1) right

-- | A form multiplied by a constant.
scale :: Integer -> Linear -> Linear
scale 0 _ = constant 0
scale factor (Linear coefficients offset) = Linear (IntMap.map (factor *) coefficients) (factor * offset)

-- | Replace the variables that have values.
substituteLinear :: IntMap Integer -> Linear -> Linear
substituteLinear values (Linear coefficients offset) =
    Linear
        (IntMap.difference coefficients values)
        (offset + sum (IntMap.intersectionWith (*) coefficients values))

-- | Whether a form has a coefficient on the variable.
mentions :: Int -> Linear -> Bool
mentions variable (Linear coefficients _) = IntMap.member variable coefficients

-- | Read a term of the formula as a linear form.
linearTerm :: (Fixpoint.Symbol -> Maybe Int) -> Formula -> Either LatticeError Linear
linearTerm variableOf = go
  where
    go term = case term of
        Fixpoint.ECon (Fixpoint.I value) -> Right $ constant value
        Fixpoint.EVar name -> maybe (Left $ UnknownName name) (\variable -> Right $ Linear (IntMap.singleton variable 1) 0) $ variableOf name
        Fixpoint.ENeg inner -> scale (-1) <$> go inner
        Fixpoint.ECst inner _ -> go inner
        Fixpoint.EBin Fixpoint.Plus left right -> plus <$> go left <*> go right
        Fixpoint.EBin Fixpoint.Minus left right -> minus <$> go left <*> go right
        Fixpoint.EBin Fixpoint.Times left right -> do
            leftForm <- go left
            rightForm <- go right
            case (leftForm, rightForm) of
                (Linear leftCoefficients factor, _) | IntMap.null leftCoefficients -> Right $ scale factor rightForm
                (_, Linear rightCoefficients factor) | IntMap.null rightCoefficients -> Right $ scale factor leftForm
                _ -> Left $ NonLinearTerm term
        _ -> Left $ NonLinearTerm term

-- Formulas

{- | A formula as a signed sum of conjunctions.

The indicator of the formula is the sum of the indicators of the
conjunctions, each multiplied by its sign. Each form of a conjunction is at
least zero. Negation is one minus the formula, and a disjunction follows
inclusion and exclusion, so no step negates a form.
-}
type Signed = Map [Linear] Integer

-- | Read a formula as a signed sum of conjunctions.
signed :: (Fixpoint.Symbol -> Maybe Int) -> Formula -> Either LatticeError Signed
signed variableOf = go
  where
    go formula = case formula of
        Fixpoint.PAnd parts -> foldr conjoin always <$> traverse go parts
        Fixpoint.POr parts -> foldr disjoin never <$> traverse go parts
        Fixpoint.PNot inner -> complement <$> go inner
        Fixpoint.PImp premise conclusion -> disjoin . complement <$> go premise <*> go conclusion
        Fixpoint.PIff left right -> do
            leftSum <- go left
            rightSum <- go right
            Right $ disjoin (conjoin leftSum rightSum) (conjoin (complement leftSum) (complement rightSum))
        Fixpoint.ECst inner _ -> go inner
        Fixpoint.PAtom relation left right -> do
            difference <- minus <$> linearTerm variableOf right <*> linearTerm variableOf left
            Right $ atom relation difference
        _ -> Left $ UnsupportedFormula formula

-- | The formula that every point satisfies.
always :: Signed
always = Map.singleton [] 1

-- | The formula that no point satisfies.
never :: Signed
never = Map.empty

-- | Both formulas.
conjoin :: Signed -> Signed -> Signed
conjoin left right =
    simplify
        [ (leftForms <> rightForms, leftSign * rightSign)
        | (leftForms, leftSign) <- Map.toList left
        , (rightForms, rightSign) <- Map.toList right
        ]

-- | At least one formula.
disjoin :: Signed -> Signed -> Signed
disjoin left right =
    simplify $
        Map.toList left <> Map.toList right <> [(forms, negate sign) | (forms, sign) <- Map.toList $ conjoin left right]

-- | The points that the formula excludes.
complement :: Signed -> Signed
complement formula = simplify $ ([], 1) : [(forms, negate sign) | (forms, sign) <- Map.toList formula]

-- | Normalize each conjunction, merge equal ones, and drop the ones without points.
simplify :: [([Linear], Integer)] -> Signed
simplify terms =
    Map.filter (/= 0) $
        Map.fromListWith
            (+)
            [(forms, sign) | (conjunction, sign) <- terms, Just forms <- [normalize conjunction], feasible forms]

-- | An atom about the difference of its right side and its left side.
atom :: Fixpoint.Brel -> Linear -> Signed
atom relation difference = case relation of
    Fixpoint.Le -> single [difference]
    Fixpoint.Lt -> single [difference `minus` constant 1]
    Fixpoint.Ge -> single [scale (-1) difference]
    Fixpoint.Gt -> single [scale (-1) difference `minus` constant 1]
    Fixpoint.Eq -> equal
    Fixpoint.Ueq -> equal
    Fixpoint.Ne -> complement equal
    Fixpoint.Une -> complement equal
  where
    single forms = simplify [(forms, 1)]
    equal = single [difference, scale (-1) difference]

{- | Simplify a conjunction, or find that no point satisfies it.

Each form is divided by the greatest common divisor of its coefficients, which
is exact for integer points. Only the tightest form of each direction remains.
-}
normalize :: [Linear] -> Maybe [Linear]
normalize forms = do
    reduced <- concat <$> traverse reduce forms
    let tightest = Map.fromListWith min [(coefficients, offset) | Linear coefficients offset <- reduced]
    if any (contradicts tightest) $ Map.toList tightest
        then Nothing
        else Just [Linear coefficients offset | (coefficients, offset) <- Map.toList tightest]
  where
    reduce (Linear coefficients offset)
        | IntMap.null coefficients = if offset >= 0 then Just [] else Nothing
        | otherwise =
            let divisor = foldr gcd 0 $ IntMap.elems coefficients
             in Just [Linear (IntMap.map (`quot` divisor) coefficients) (offset `div` divisor)]
    contradicts tightest (coefficients, offset) =
        maybe False (\opposite -> offset + opposite < 0) $ Map.lookup (IntMap.map negate coefficients) tightest

{- | Whether a conjunction can have an integer point.

Fourier-Motzkin elimination combines each lower bound of a variable with each
upper bound, and 'normalize' tightens each result for integer points. A
contradiction proves that no integer point exists. The result 'True' does not
prove that a point exists: such a piece counts zero points later.
-}
feasible :: [Linear] -> Bool
feasible forms = case normalize forms of
    Nothing -> False
    Just reduced -> case cheapest reduced of
        Nothing -> True
        Just variable -> feasible $ project variable reduced
  where
    cheapest reduced =
        fmap snd $
            minimumOn
                [ ( length (filter ((> 0) . coefficientOf variable) reduced) * length (filter ((< 0) . coefficientOf variable) reduced)
                  , variable
                  )
                | variable <- IntMap.keys $ IntMap.unions [coefficients | Linear coefficients _ <- reduced]
                ]
    minimumOn [] = Nothing
    minimumOn candidates = Just $ minimum candidates
    project variable reduced =
        [form | form <- reduced, coefficientOf variable form == 0]
            <> [ scale (negate $ coefficientOf variable upper) lower `plus` scale (coefficientOf variable lower) upper
               | lower <- reduced
               , coefficientOf variable lower > 0
               , upper <- reduced
               , coefficientOf variable upper < 0
               ]

-- | The coefficient of a variable in a form.
coefficientOf :: Int -> Linear -> Integer
coefficientOf variable (Linear coefficients _) = IntMap.findWithDefault 0 variable coefficients

-- Summation

{- | A polyhedral piece: a conjunction, and a polynomial that counts
completions in it. The polynomial of a piece can be negative; the sum over
the pieces of a level is the number of completions.
-}
data Piece = Piece ![Linear] !Polynomial

{- | Sum one variable out of each piece.

For each choice of the largest lower bound and the smallest upper bound, the
variable ranges over one interval, and the piece requires that choice. Ties go
to the first bound, so the choices of one piece are disjoint.
-}
eliminate :: Fixpoint.Symbol -> Int -> [Piece] -> Either LatticeError [Piece]
eliminate name variable = fmap concat . traverse split
  where
    split (Piece constraints polynomial) = do
        let (involved, rest) = partition (mentions variable) constraints
        bounds <- traverse bound involved
        let lowers = lefts bounds
            uppers = rights bounds
        when (null lowers || null uppers) $ Left $ UnboundedVariable name
        Right
            [ Piece region $ sumOver variable low high polynomial
            | (lowIndex, low) <- zip [0 :: Int ..] lowers
            , (highIndex, high) <- zip [0 :: Int ..] uppers
            , Just region <-
                [ normalize $
                    rest
                        <> [ strictBefore lowIndex index (low `minus` other)
                           | (index, other) <- zip [0 ..] lowers
                           , index /= lowIndex
                           ]
                        <> [ strictBefore highIndex index (other `minus` high)
                           | (index, other) <- zip [0 ..] uppers
                           , index /= highIndex
                           ]
                        <> [high `minus` low]
                ]
            , feasible region
            ]
    -- The chosen bound is strictly better than the bounds before it.
    strictBefore chosen index difference
        | index < chosen = difference `minus` constant 1
        | otherwise = difference
    bound (Linear coefficients offset) = case IntMap.lookup variable coefficients of
        Just 1 -> Right $ Left $ scale (-1) $ Linear (IntMap.delete variable coefficients) offset
        Just (-1) -> Right $ Right $ Linear (IntMap.delete variable coefficients) offset
        _ -> Left $ NonUnitCoefficient name

-- Polynomials

-- | A polynomial with rational coefficients. A monomial maps each variable to its exponent.
newtype Polynomial = Polynomial (Map (IntMap Int) Rational)

-- | A constant polynomial.
polynomialConstant :: Rational -> Polynomial
polynomialConstant value = Polynomial $ Map.filter (/= 0) $ Map.singleton IntMap.empty value

-- | A linear form as a polynomial.
fromLinear :: Linear -> Polynomial
fromLinear (Linear coefficients offset) =
    Polynomial
        $ Map.filter (/= 0)
        $ Map.fromList
        $ (IntMap.empty, fromInteger offset)
            : [(IntMap.singleton variable 1, fromInteger coefficient) | (variable, coefficient) <- IntMap.toList coefficients]

-- | The sum of two polynomials.
addPolynomials :: Polynomial -> Polynomial -> Polynomial
addPolynomials (Polynomial left) (Polynomial right) = Polynomial $ Map.filter (/= 0) $ Map.unionWith (+) left right

-- | The product of two polynomials.
multiplyPolynomials :: Polynomial -> Polynomial -> Polynomial
multiplyPolynomials (Polynomial left) (Polynomial right) =
    Polynomial
        $ Map.filter (/= 0)
        $ Map.fromListWith
            (+)
            [ (IntMap.unionWith (+) leftMonomial rightMonomial, leftCoefficient * rightCoefficient)
            | (leftMonomial, leftCoefficient) <- Map.toList left
            , (rightMonomial, rightCoefficient) <- Map.toList right
            ]

-- | Replace the variables that have values.
substitute :: IntMap Integer -> Polynomial -> Polynomial
substitute values (Polynomial terms) =
    Polynomial
        $ Map.filter (/= 0)
        $ Map.fromListWith
            (+)
            [ ( IntMap.difference monomial values
              , coefficient
                    * product [fromInteger value ^ power | (value, power) <- IntMap.elems $ IntMap.intersectionWith (,) values monomial]
              )
            | (monomial, coefficient) <- Map.toList terms
            ]

-- | The value of a polynomial without variables.
polynomialValue :: Polynomial -> Rational
polynomialValue (Polynomial terms) = Map.findWithDefault 0 IntMap.empty terms

{- | The sum of a polynomial over one variable, from a lower form to an upper
form, as a polynomial in the other variables.

The result is exact when the upper form is at least the lower form minus one.
-}
sumOver :: Int -> Linear -> Linear -> Polynomial -> Polynomial
sumOver variable low high (Polynomial terms) =
    foldr
        addPolynomials
        (polynomialConstant 0)
        [ multiplyPolynomials
            (Polynomial $ Map.singleton (IntMap.delete variable monomial) coefficient)
            (powerSum $ IntMap.findWithDefault 0 variable monomial)
        | (monomial, coefficient) <- Map.toList terms
        ]
  where
    powerSum power =
        faulhaber power (fromLinear high)
            `addPolynomials` multiplyPolynomials (polynomialConstant (-1)) (faulhaber power (fromLinear $ low `minus` constant 1))

{- | The Faulhaber polynomial @1^p + 2^p + ... + n^p@ at a polynomial @n@.

The polynomial identity @S(b) - S(a - 1) = a^p + ... + b^p@ holds for all
integers @a <= b + 1@, negative ones included.
-}
faulhaber :: Int -> Polynomial -> Polynomial
faulhaber power argument =
    foldr
        addPolynomials
        (polynomialConstant 0)
        [ multiplyPolynomials
            (polynomialConstant $ fromInteger (binomial (power + 1) index) * bernoulliPlus index / fromIntegral (power + 1))
            (powerOf (power + 1 - index))
        | index <- [0 .. power]
        ]
  where
    powerOf count = foldr multiplyPolynomials (polynomialConstant 1) $ replicate count argument

-- | The Bernoulli number @B_n@ with @B_1 = 1/2@.
bernoulliPlus :: Int -> Rational
bernoulliPlus 1 = 1 / 2
bernoulliPlus index = bernoulliNumbers !! index

-- | The Bernoulli numbers with @B_1 = -1/2@.
bernoulliNumbers :: [Rational]
bernoulliNumbers = map number [0 ..]
  where
    number :: Int -> Rational
    number 0 = 1
    number index =
        negate (sum [fromInteger (binomial (index + 1) earlier) * bernoulliNumbers !! earlier | earlier <- [0 .. index - 1]])
            / fromIntegral (index + 1)

-- | The binomial coefficient.
binomial :: Int -> Int -> Integer
binomial total chosen = product [toInteger (total - chosen + 1) .. toInteger total] `div` product [1 .. toInteger chosen]
