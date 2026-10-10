{-# LANGUAGE DeriveFunctor #-}

{- | A reference model of the generator engine, for differential tests.

A description ('Desc', and 'GDesc' for the grouped layer) is a small
first-order syntax for a generator. It has two interpretations. 'build' gives
the engine generator through the public API. 'model' gives a naive model that
lists the members of the language. The model states the rules of the engine
directly:

* Size. Sizes count pays, as in FEAT. A member of @pure@ has size zero. A
  member of @elements@, of an @atomic@ language, or of a group from @groupOn@
  has size one. A product adds the sizes of its sides, and an application adds
  the size of the operation and of every argument. A node label and @pay@ add
  one. A map and a choice keep the size.
* Guards. A recursion reaches its occurrence through a pay, or through a
  product whose other side has no member of size zero, and through a product
  or a node, which adds a term node. Otherwise the occurrence is unguarded.
* Finite ranks. A finite language ranks in mixed radix. A choice puts the
  ranks of its alternatives one after the other. A product orders by the rank
  of its left side first. An application orders by the operation, then by the
  arguments from left to right.
* Recursive ranks. A recursive or bounded language ranks by size first. In one
  size class, a choice keeps the order of its alternatives, and a product
  orders by the size of its left side, then by the left member, then by the
  right member.
* Weights. A finite choice selects an alternative by its weight. In one size
  class, a choice selects an alternative by its member count, and a product
  selects the sizes of its sides by their member counts. Only an atomic
  language keeps its own distribution in a size class. A bounded language
  selects a size class by its member count.
* Groups. A finite group has a mass: the probability of its key. A recursive
  group has a mass at each size, which is its member count unless an atomic
  group sets it. In a recursive family, merged groups and applications select
  by these masses instead of by counts.
* Errors. The model gives the error that the engine gives, with the same
  precedence. A bound or an atomic boundary around a language that reaches the
  occurrence of an enclosing recursion is an error. A join, a grouping, or an
  application over a recursion that failed gives the error of that recursion.

The model lists every member of a size class, so it is slow. It is correct
because it is simple.
-}
module Data.CFTA.Gen.Reference (
    -- * Descriptions
    Desc (..),
    GDesc (..),
    Value (..),
    groupKey,
    closed,
    closedGrouped,
    build,
    buildGrouped,

    -- * Automata
    Automaton (..),
    AutomatonEdge (..),
    closedAutomaton,
    automatonNode,
    termsOfSize,

    -- * The model
    Lang (..),
    Family (..),
    Group (..),
    Model (..),
    Member (..),
    model,
    modelGrouped,
    members,
) where

import Control.Monad (when)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import Data.Maybe (catMaybes, listToMaybe)
import Data.Text (Text)

import Data.CFTA.Constraint (equalityConstraint)
import qualified Data.CFTA.Equality as ECTA
import Data.CFTA.Gen (Args (..), Gen, GenError (..), On (..), Sig (..))
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Index (Weight (..))
import Data.CFTA.Symbol (Symbol (Symbol))
import qualified Data.Tree as Tree

-- | A description of a generator of 'Value'.
data Desc
    = -- | @pure (Atom n)@
      Pure Int
    | -- | @elements (map Atom ns)@
      Elements [Int]
    | -- | @node symbol@
      Node Text Desc
    | -- | @pay@
      Pay Desc
    | -- | @fmap (Tagged n)@
      Tag Int Desc
    | -- | @Paired \<$\> left \<*\> right@
      Pair Desc Desc
    | -- | @frequency@
      Frequency [(Integer, Desc)]
    | -- | @uniformly@
      Uniformly [Desc]
    | -- | @atomic@
      Atomic Desc
    | -- | @upToSize@
      UpToSize Int Desc
    | -- | @recur@
      Recur Desc
    | -- | The occurrence of an enclosing 'Recur': zero for the innermost one, one for the next, and so on.
      Var Int
    | -- | @atKey@
      AtKey Int GDesc
    | -- | @ungroup@
      Ungroup GDesc
    | -- | @uncurry Paired \<$\> match (groupKey n :==: groupKey n)@
      Match Int Desc Desc
    | -- | @uncurry Paired \<$\> relate (groupKey n) (groupKey n) (<=)@
      Relate Int Desc Desc
    deriving (Eq, Show)

-- | A description of a grouped generator of 'Value' with 'Int' keys.
data GDesc
    = -- | @keyed@
      Keyed Int Desc
    | -- | @groupOn (groupKey n)@
      GroupOn Int Desc
    | -- | @regroupOn (\`mod\` n)@
      Regroup Int GDesc
    | -- | @mapWithKey Tagged@
      MapWithKey GDesc
    | -- | @node symbol@ on every group
      GNode Text GDesc
    | -- | @frequencies@
      Frequencies [(Integer, GDesc)]
    | {- | @apply@ with one argument family. Each operation has an argument key,
      a result key, and a description. The operation of value @v@ maps @a@ to
      @Paired v a@. The operations form one family through @frequencies@ with
      equal weights.
      -}
      Apply1 [(Int, Int, Desc)] GDesc
    | -- | @apply@ with two argument families. The operation of value @v@ maps @a@ and @b@ to @Paired v (Paired a b)@.
      Apply2 [(Int, Int, Int, Desc)] GDesc GDesc
    | -- | @recurGrouped@
      RecurGrouped GDesc
    | -- | The occurrence of an enclosing 'RecurGrouped', counted as 'Var' counts 'Recur'.
      GVar Int
    deriving (Eq, Show)

-- | The values of a described generator.
data Value = Atom Int | Tagged Int Value | Paired Value Value
    deriving (Eq, Ord, Show)

-- | The key of a value for 'GroupOn': the sum of its atoms and tags, modulo @n@.
groupKey :: Int -> Value -> Int
groupKey n value = total value `mod` max 1 n
  where
    total (Atom k) = k
    total (Tagged tag inner) = tag + total inner
    total (Paired left right) = total left + total right

-- | Whether every 'Var' and 'GVar' of a description is inside its recursion.
closed :: Desc -> Bool
closed = closedIn 0 0

-- | 'closed' for a grouped description.
closedGrouped :: GDesc -> Bool
closedGrouped = closedGroupedIn 0 0

closedIn :: Int -> Int -> Desc -> Bool
closedIn flat grouped = \case
    Pure _ -> True
    Elements _ -> True
    Node _ inner -> go inner
    Pay inner -> go inner
    Tag _ inner -> go inner
    Pair left right -> go left && go right
    Frequency alternatives -> all (go . snd) alternatives
    Uniformly alternatives -> all go alternatives
    Atomic inner -> go inner
    UpToSize _ inner -> go inner
    Recur body -> closedIn (flat + 1) grouped body
    Var index -> index >= 0 && index < flat
    AtKey _ family -> closedGroupedIn flat grouped family
    Ungroup family -> closedGroupedIn flat grouped family
    Match _ left right -> go left && go right
    Relate _ left right -> go left && go right
  where
    go = closedIn flat grouped

closedGroupedIn :: Int -> Int -> GDesc -> Bool
closedGroupedIn flat grouped = \case
    Keyed _ inner -> closedIn flat grouped inner
    GroupOn _ inner -> closedIn flat grouped inner
    Regroup _ family -> go family
    MapWithKey family -> go family
    GNode _ family -> go family
    Frequencies alternatives -> all (go . snd) alternatives
    Apply1 operations argument ->
        all (\(_, _, operation) -> closedIn flat grouped operation) operations && go argument
    Apply2 operations first second ->
        all (\(_, _, _, operation) -> closedIn flat grouped operation) operations && go first && go second
    RecurGrouped body -> closedGroupedIn flat (grouped + 1) body
    GVar index -> index >= 0 && index < grouped
  where
    go = closedGroupedIn flat grouped

-- | The engine generator of a closed description.
build :: Desc -> Gen Text Value
build = buildIn [] []

-- | The engine family of a closed grouped description.
buildGrouped :: GDesc -> Gen.Grouped Text Int Value
buildGrouped = buildGroupedIn [] []

buildIn ::
    [Gen Text Value] ->
    [Gen.Grouped Text Int Value] ->
    Desc ->
    Gen Text Value
buildIn env families = \case
    Pure n -> pure $ Atom n
    Elements ns -> Gen.elements $ map Atom ns
    Node symbol inner -> Gen.node symbol $ go inner
    Pay inner -> Gen.pay $ go inner
    Tag n inner -> Tagged n <$> go inner
    Pair left right -> Paired <$> go left <*> go right
    Frequency alternatives -> Gen.frequency [(Weight weight, go alternative) | (weight, alternative) <- alternatives]
    Uniformly alternatives -> Gen.uniformly $ map go alternatives
    Atomic inner -> Gen.atomic $ go inner
    UpToSize bound inner -> Gen.upToSize (toEnum bound) $ go inner
    Recur body -> Gen.recur $ \self -> buildIn (self : env) families body
    Var index -> env !! index
    AtKey key family -> Gen.atKey key $ buildGroupedIn env families family
    Ungroup family -> Gen.ungroup $ buildGroupedIn env families family
    Match n left right -> uncurry Paired <$> Gen.match (groupKey n :==: groupKey n) (go left) (go right)
    Relate n left right -> uncurry Paired <$> Gen.relate (groupKey n) (groupKey n) (<=) (go left) (go right)
  where
    go = buildIn env families

buildGroupedIn ::
    [Gen Text Value] ->
    [Gen.Grouped Text Int Value] ->
    GDesc ->
    Gen.Grouped Text Int Value
buildGroupedIn env families = \case
    Keyed key inner -> Gen.keyed key $ flat inner
    GroupOn n inner -> Gen.groupOn (groupKey n) $ flat inner
    Regroup n family -> Gen.regroupOn (`mod` max 1 n) $ go family
    MapWithKey family -> Gen.mapWithKey Tagged $ go family
    GNode symbol family -> Gen.node symbol $ go family
    Frequencies alternatives -> Gen.frequencies [(Weight weight, go alternative) | (weight, alternative) <- alternatives]
    Apply1 operations argument ->
        Gen.apply
            ( Gen.frequencies
                [ (1, Gen.keyed (argumentKey :-> resultKey) $ Paired <$> flat operation)
                | (argumentKey, resultKey, operation) <- operations
                ]
            )
            (go argument :& ANil)
    Apply2 operations first second ->
        Gen.apply
            ( Gen.frequencies
                [ (1, Gen.keyed (firstKey :* secondKey :-> resultKey) $ (\v a b -> Paired v (Paired a b)) <$> flat operation)
                | (firstKey, secondKey, resultKey, operation) <- operations
                ]
            )
            (go first :& go second :& ANil)
    RecurGrouped body -> Gen.recurGrouped $ \self -> buildGroupedIn env (self : families) body
    GVar index -> families !! index
  where
    flat = buildIn env families
    go = buildGroupedIn env families

{- | A description of an automaton over the symbols @a@ and @b@ of arity
zero, @f@ of arity one, and @g@ and @h@ of arity two.
-}
data Automaton
    = -- | A node and its alternatives.
      States [AutomatonEdge]
    | -- | A recursive node; its occurrences are 'Back'.
      Loop Automaton
    | -- | The occurrence of an enclosing 'Loop': zero for the innermost one.
      Back Int
    deriving (Eq, Show)

-- | An alternative: its symbol, its children, and whether its two children must be equal.
data AutomatonEdge = AutomatonEdge Text [Automaton] Bool
    deriving (Eq, Show)

-- | Whether every 'Back' of an automaton is inside its 'Loop'.
closedAutomaton :: Automaton -> Bool
closedAutomaton = go 0
  where
    go depth = \case
        States edges -> and [all (go depth) children | AutomatonEdge _ children _ <- edges]
        Loop body -> go (depth + 1) body
        Back index -> index >= 0 && index < depth

-- | The interned node of a closed automaton.
automatonNode :: Automaton -> ECTA.Node Symbol
automatonNode = go []
  where
    go loops = \case
        States edges ->
            ECTA.Node
                [ ECTA.mkEdge (Symbol symbol) (map (go loops) children) $
                    if equal
                        then equalityConstraint $ ECTA.mkEqConstraints [[ECTA.path [0], ECTA.path [1]]]
                        else (equalityConstraint ECTA.EmptyConstraints)
                | AutomatonEdge symbol children equal <- edges
                ]
        Loop body -> ECTA.createMu $ \self -> go (self : loops) body
        Back index -> if index < length loops then loops !! index else ECTA.EmptyNode

{- | The terms of one size, the number of their nodes, of an automaton,
without its equalities. A term comes once for each accepting run.
-}
termsOfSize :: Automaton -> Integer -> [Tree.Tree Symbol]
termsOfSize = go []
  where
    go loops automaton size = case automaton of
        States edges ->
            [ Tree.Node (Symbol symbol) children
            | AutomatonEdge symbol parts _ <- edges
            , children <- spread loops parts (size - 1)
            ]
        Loop body -> knot size
          where
            knot = memo [] $ go (knot : loops) body
        Back index -> (loops !! index) size
    spread _ [] 0 = [[]]
    spread _ [] _ = []
    spread loops (part : rest) size =
        [ first : others
        | firstSize <- [1 .. size - toInteger (length rest)]
        , first <- go loops part firstSize
        , others <- spread loops rest (size - firstSize)
        ]

{- | A language of the model: whether the engine builds it as a recursive
language, and its model or the error that the engine gives.
-}
data Lang a = Lang
    { langRecursive :: Bool
    , langModel :: Either GenError (Model a)
    }
    deriving (Functor)

-- | The members of one language.
data Model a = Model
    { modelFinite :: Maybe (Integer, [Member a])
    -- ^ A finite language: its cardinality and its members in rank order.
    , modelAtomic :: Bool
    -- ^ Whether an atomic boundary closes this finite language.
    , modelCount :: Integer -> Integer
    -- ^ The number of members of one size.
    , modelClass :: Integer -> [(a, Rational)]
    -- ^ The members of one size in size-class order, each with its probability in the class.
    , modelMinimum :: Maybe Integer
    , modelLargest :: Maybe Integer
    {- ^ The largest size, when the sizes end: always for a finite language,
    and for a recursive one that holds no tied recursion.
    -}
    , modelReaches :: IntSet
    -- ^ The tokens of the enclosing recursions whose occurrence the language reaches.
    , modelUnguarded :: IntSet
    {- ^ The tokens whose occurrence the language reaches with no pay and no
    product whose other side has no member of size zero between.
    -}
    , modelTermless :: IntSet
    -- ^ The tokens whose occurrence the language reaches with no product and no node between.
    }
    deriving (Functor)

{- | One member of a finite language: its value, its size, its probability,
and its weight in its size class. In each size class the weights add up to
the number of members.
-}
data Member a = Member
    { memberValue :: a
    , memberSize :: Integer
    , memberMass :: Rational
    , memberWeight :: Rational
    }
    deriving (Eq, Show, Functor)

-- | A grouped language of the model, as 'Lang' is for an ordinary one.
data Family key a = Family
    { familyRecursive :: Bool
    , familyGroups :: Either GenError (Map.Map key (Group a))
    }

{- | One group: the language conditional on its key, with the mass of a finite
group, or the mass at each size of a recursive group.
-}
data Group a = Group
    { groupModel :: Model a
    , groupMass :: Rational
    , groupMassAt :: Integer -> Rational
    }
    deriving (Functor)

{- | The enclosing recursions: the occurrences of the ordinary ones and the
families of the grouped ones, innermost first.
-}
data Env = Env [Occurrence] [Map.Map Int (Group Value)]

-- | The occurrence of an ordinary recursion.
data Occurrence = Occurrence
    { occurrenceToken :: Int
    , occurrenceMinimum :: Maybe Integer
    , occurrenceCount :: Integer -> Integer
    , occurrenceClass :: Integer -> [(Value, Rational)]
    }

-- | A token for a new recursion: the number of recursions around it.
nextToken :: Env -> Int
nextToken (Env flat grouped) = length flat + length grouped

-- | The model of a closed description.
model :: Desc -> Lang Value
model = interpret $ Env [] []

-- | The model of a closed grouped description.
modelGrouped :: GDesc -> Family Int Value
modelGrouped = interpretGrouped $ Env [] []

{- | The members of a language in rank order, with their sizes, up to a size
bound for a recursive language.
-}
members :: Integer -> Lang a -> [(a, Integer)]
members bound lang = case langModel lang of
    Left _ -> []
    Right model' -> case modelFinite model' of
        Just (_, finite) -> [(memberValue member, memberSize member) | member <- finite]
        Nothing -> [(value, size) | size <- [0 .. bound], (value, _) <- modelClass model' size]

interpret :: Env -> Desc -> Lang Value
interpret env@(Env flat _) = \case
    Pure n -> finiteLang $ leafModel 0 False [(Atom n, 1)]
    Elements [] -> Lang False $ Left EmptyGenerator
    Elements ns -> finiteLang $ atomModel False [(Atom n, 1 / fromIntegral (length ns)) | n <- ns]
    Node _ inner -> nodeLang $ go inner
    Pay inner -> payLang $ go inner
    Tag n inner -> Tagged n <$> go inner
    Pair left right -> pairLang Paired (go left) (go right)
    Frequency alternatives -> frequencyLang [(weight, go alternative) | (weight, alternative) <- alternatives]
    Uniformly alternatives -> uniformlyLang $ map go alternatives
    Atomic inner -> atomicLang $ go inner
    UpToSize bound inner -> boundLang (toInteger bound) $ go inner
    Recur body -> recurLang env body
    Var index -> Lang True $ Right $ occurrenceModel $ flat !! index
    AtKey key family -> atKeyLang key $ interpretGrouped env family
    Ungroup family -> atKeyLang () $ regroupFamily (const ()) $ interpretGrouped env family
    Match n left right -> joinLang (==) (groupKey n) (go left) (go right)
    Relate n left right -> joinLang (<=) (groupKey n) (go left) (go right)
  where
    go = interpret env
    occurrenceModel occurrence =
        Model
            { modelFinite = Nothing
            , modelAtomic = False
            , modelCount = occurrenceCount occurrence
            , modelClass = occurrenceClass occurrence
            , modelMinimum = occurrenceMinimum occurrence
            , modelLargest = Nothing
            , modelReaches = IntSet.singleton $ occurrenceToken occurrence
            , modelUnguarded = IntSet.singleton $ occurrenceToken occurrence
            , modelTermless = IntSet.singleton $ occurrenceToken occurrence
            }

finiteLang :: Model a -> Lang a
finiteLang = Lang False . Right

{- | A finite language of members of size one, each with its mass. An atomic
language keeps its distribution in its size class.
-}
atomModel :: Bool -> [(a, Rational)] -> Model a
atomModel = leafModel 1

-- | A finite language of members of one size, each with its mass.
leafModel :: Integer -> Bool -> [(a, Rational)] -> Model a
leafModel leafSize atomic weighted =
    Model
        { modelFinite = Just (total, [Member value leafSize mass (fromInteger total * mass) | (value, mass) <- weighted])
        , modelAtomic = atomic
        , modelCount = \size -> if size == leafSize then total else 0
        , modelClass = \size -> if size == leafSize then weighted else []
        , modelMinimum = Just leafSize
        , modelLargest = Just leafSize
        , modelReaches = IntSet.empty
        , modelUnguarded = IntSet.empty
        , modelTermless = IntSet.empty
        }
  where
    total = toInteger $ length weighted

{- | A node: a pay, and a term node, so no occurrence below it is unguarded or
termless.
-}
nodeLang :: Lang a -> Lang a
nodeLang (Lang recursive result) = Lang recursive $ nodeModel <$> result

-- | 'nodeLang' for every group of a family. The mass at each size of a group moves up by one.
nodeFamily :: Family key a -> Family key a
nodeFamily (Family recursive groups) = Family recursive $ fmap nodeGroup <$> groups
  where
    nodeGroup group =
        group
            { groupModel = nodeModel $ groupModel group
            , groupMassAt = \size -> if size < 1 then 0 else groupMassAt group (size - 1)
            }

-- | The model of 'nodeLang'.
nodeModel :: Model a -> Model a
nodeModel model' = (payModel model'){modelTermless = IntSet.empty}

{- | A pay: every member is one larger, and no occurrence below it is
unguarded.
-}
payLang :: Lang a -> Lang a
payLang (Lang recursive result) = Lang recursive $ payModel <$> result

-- | The model of 'payLang'.
payModel :: Model a -> Model a
payModel model' =
    model'
        { modelFinite = fmap (map $ \member -> member{memberSize = memberSize member + 1}) <$> modelFinite model'
        , modelCount = \size -> if size < 1 then 0 else modelCount model' (size - 1)
        , modelClass = \size -> if size < 1 then [] else modelClass model' (size - 1)
        , modelMinimum = (+ 1) <$> modelMinimum model'
        , modelLargest = (+ 1) <$> modelLargest model'
        , modelUnguarded = IntSet.empty
        }

-- | The member count of a model as a weight for a choice in a size class.
byCount :: Model a -> Integer -> Rational
byCount model' = fromInteger . modelCount model'

pairLang :: (a -> b -> c) -> Lang a -> Lang b -> Lang c
pairLang combine left right = case (left, right) of
    (Lang False (Left err), _) -> Lang False $ Left err
    (_, Lang False (Left err)) -> Lang False $ Left err
    (Lang False (Right leftModel), Lang False (Right rightModel)) ->
        finiteLang $ pairModel combine (byCount leftModel) leftModel (byCount rightModel) rightModel
    _ -> Lang True $ do
        leftModel <- langModel left
        rightModel <- langModel right
        pure $ pairModel combine (byCount leftModel) leftModel (byCount rightModel) rightModel

{- | A product. The weight functions choose the sizes of the sides in a size
class: the member counts for an ordinary product, the group masses for an
application in a recursive family.
-}
pairModel :: (a -> b -> c) -> (Integer -> Rational) -> Model a -> (Integer -> Rational) -> Model b -> Model c
pairModel combine leftWeight left rightWeight right =
    Model
        { modelFinite = do
            (leftTotal, leftMembers) <- modelFinite left
            (rightTotal, rightMembers) <- modelFinite right
            pure
                ( leftTotal * rightTotal
                , [ Member
                        (combine (memberValue first) (memberValue second))
                        (memberSize first + memberSize second)
                        (memberMass first * memberMass second)
                        (memberWeight first * memberWeight second)
                  | first <- leftMembers
                  , second <- rightMembers
                  ]
                )
        , modelAtomic = False
        , modelCount = \size -> sum [modelCount left leftSize * modelCount right (size - leftSize) | leftSize <- splitSizes size]
        , modelClass = \size ->
            let splits =
                    [ (leftWeight leftSize * rightWeight (size - leftSize), leftSize)
                    | leftSize <- splitSizes size
                    , modelCount left leftSize * modelCount right (size - leftSize) > 0
                    ]
                total = sum $ map fst splits
             in [ (combine first second, weight / total * firstMass * secondMass)
                | (weight, leftSize) <- splits
                , (first, firstMass) <- modelClass left leftSize
                , (second, secondMass) <- modelClass right (size - leftSize)
                ]
        , modelMinimum = (+) <$> modelMinimum left <*> modelMinimum right
        , modelLargest = (+) <$> modelLargest left <*> modelLargest right
        , modelReaches = IntSet.union (modelReaches left) (modelReaches right)
        , -- A side guards the occurrences of the other side unless it has a member of size zero.
          modelUnguarded = IntSet.union (besideZero right $ modelUnguarded left) (besideZero left $ modelUnguarded right)
        , modelTermless = IntSet.empty
        }
  where
    besideZero other unguarded = if modelMinimum other == Just 0 then unguarded else IntSet.empty
    splitSizes = productSplits (modelMinimum left) (modelMinimum right)

{- | The sizes of the left side of the splits of a product of one size, from
the minimum sizes of its sides. The bounds keep a recursive occurrence that a
side guards from being read at the size of the product.
-}
productSplits :: Maybe Integer -> Maybe Integer -> Integer -> [Integer]
productSplits (Just leftMinimum) (Just rightMinimum) size = [leftMinimum .. size - rightMinimum]
productSplits _ _ _ = []

frequencyLang :: [(Integer, Lang a)] -> Lang a
frequencyLang weighted
    | weight : _ <- [weight | (weight, _) <- weighted, weight <= 0] =
        Lang False $ Left $ NonPositiveWeight $ Weight weight
    | err : _ <- [err | (_, Lang False (Left err)) <- weighted, err /= EmptyGenerator] =
        Lang False $ Left err
    | null live = Lang False $ Left EmptyGenerator
    | not $ any (langRecursive . snd) live =
        finiteLang $ choiceModel [(fromInteger weight, byCount model', model') | (weight, Lang _ (Right model')) <- live]
    | otherwise = Lang True $ do
        models <- traverse (langModel . snd) live
        if equalWeights $ map fst live
            then Right $ choiceModel [(fromInteger weight, byCount model', model') | (weight, model') <- zip (map fst live) models]
            else Left WeightedRecursiveAlternatives
  where
    live = [alternative | alternative@(_, Lang _ result) <- weighted, not $ isEmpty result]

isEmpty :: Either GenError a -> Bool
isEmpty (Left EmptyGenerator) = True
isEmpty _ = False

equalWeights :: [Integer] -> Bool
equalWeights (weight : rest) = all (== weight) rest
equalWeights [] = True

{- | Pairs of members of two finite languages whose keys the relation relates.
The key pairs come in ascending order, and the pairs of one key pair in
mixed radix. Every pair has size two. The mass and the weight in the size
class of a pair are the products of those of its sides, normalized.
-}
joinLang :: (Ord key) => (key -> key -> Bool) -> (Value -> key) -> Lang Value -> Lang Value -> Lang Value
joinLang relation key left right = case (left, right) of
    (Lang False (Left err), _) -> Lang False $ Left err
    (_, Lang False (Left err)) -> Lang False $ Left err
    (Lang True (Left err), _) -> Lang False $ Left err
    (_, Lang True (Left err)) -> Lang False $ Left err
    (Lang True _, _) -> Lang False $ Left UnboundedGenerator
    (_, Lang True _) -> Lang False $ Left UnboundedGenerator
    (Lang False (Right leftModel), Lang False (Right rightModel))
        | null pairs -> Lang False $ Left EmptyGenerator
        | otherwise ->
            finiteLang
                Model
                    { modelFinite =
                        Just
                            ( count
                            , [ Member
                                    (Paired (memberValue first) (memberValue second))
                                    2
                                    (memberMass first * memberMass second / mass)
                                    (fromInteger count * memberWeight first * memberWeight second / weight)
                              | (first, second) <- pairs
                              ]
                            )
                    , modelAtomic = False
                    , modelCount = \size -> if size == 2 then count else 0
                    , modelClass = \size ->
                        if size == 2
                            then
                                [ (Paired (memberValue first) (memberValue second), memberWeight first * memberWeight second / weight)
                                | (first, second) <- pairs
                                ]
                            else []
                    , modelMinimum = Just 2
                    , modelLargest = Just 2
                    , modelReaches = IntSet.empty
                    , modelUnguarded = IntSet.empty
                    , modelTermless = IntSet.empty
                    }
      where
        byKey model' = Map.fromListWith (flip (<>)) [(key $ memberValue member, [member]) | member <- maybe [] snd $ modelFinite model']
        groups =
            [ (firsts, seconds)
            | (leftKey, firsts) <- Map.toAscList $ byKey leftModel
            , (rightKey, seconds) <- Map.toAscList $ byKey rightModel
            , relation leftKey rightKey
            ]
        pairs = [(first, second) | (firsts, seconds) <- groups, first <- firsts, second <- seconds]
        count = toInteger $ length pairs
        mass = sum [sum (map memberMass firsts) * sum (map memberMass seconds) | (firsts, seconds) <- groups]
        weight = sum [memberWeight first * memberWeight second | (first, second) <- pairs]

{- | A choice. Each alternative has its weight in a finite choice, its weight
in a size class, and its model.
-}
choiceModel :: [(Rational, Integer -> Rational, Model a)] -> Model a
choiceModel alternatives =
    Model
        { modelFinite = do
            finites <- traverse (\(_, _, model') -> modelFinite model') alternatives
            let totalWeight = sum [weight | (weight, _, _) <- alternatives]
            pure
                ( sum $ map fst finites
                , concat
                    [ [member{memberMass = weight / totalWeight * memberMass member} | member <- finite]
                    | ((weight, _, _), (_, finite)) <- zip alternatives finites
                    ]
                )
        , modelAtomic = False
        , modelCount = \size -> sum [modelCount model' size | (_, _, model') <- alternatives]
        , modelClass = \size ->
            let live =
                    [ (weightAt size, model')
                    | (_, weightAt, model') <- alternatives
                    , modelCount model' size > 0
                    , weightAt size > 0
                    ]
                total = sum $ map fst live
             in [(value, weight / total * mass) | (weight, model') <- live, (value, mass) <- modelClass model' size]
        , modelMinimum = minimumOf [modelMinimum model' | (_, _, model') <- alternatives]
        , modelLargest = maximum <$> traverse (\(_, _, model') -> modelLargest model') alternatives
        , modelReaches = IntSet.unions [modelReaches model' | (_, _, model') <- alternatives]
        , modelUnguarded = IntSet.unions [modelUnguarded model' | (_, _, model') <- alternatives]
        , modelTermless = IntSet.unions [modelTermless model' | (_, _, model') <- alternatives]
        }

minimumOf :: [Maybe Integer] -> Maybe Integer
minimumOf sizes = case catMaybes sizes of
    [] -> Nothing
    found -> Just $ minimum found

uniformlyLang :: [Lang a] -> Lang a
uniformlyLang langs
    | any langRecursive langs = frequencyLang [(1, lang) | lang <- langs]
    | otherwise = case traverse liveCount langs of
        Left err -> Lang False $ Left err
        Right counts -> frequencyLang [(count, lang) | (Just count, lang) <- zip counts langs]
  where
    liveCount (Lang _ (Left EmptyGenerator)) = Right Nothing
    liveCount (Lang _ (Left err)) = Left err
    liveCount (Lang _ (Right model')) = Right $ fst <$> modelFinite model'

atomicLang :: Lang a -> Lang a
atomicLang = \case
    Lang _ (Left err) -> Lang False $ Left err
    Lang False (Right model') -> finiteLang $ atomicModel 1 model'
    Lang True (Right model')
        | not $ IntSet.null $ modelReaches model' -> Lang False $ Left BoundedRecursiveOccurrence
        -- A recursive language that holds no tied recursion has sizes that end.
        | Just largest <- modelLargest model' -> atomicLang $ boundLang largest $ Lang True $ Right model'
        | otherwise -> Lang False $ Left UnboundedGenerator

-- | Close a finite language as one atomic choice of the given size.
atomicModel :: Integer -> Model a -> Model a
atomicModel atomSize model' = case modelFinite model' of
    Just (_, finite) -> leafModel atomSize True [(memberValue member, memberMass member) | member <- finite]
    Nothing -> error "Data.CFTA.Gen.Reference.atomicModel: a finite language without members"

boundLang :: Integer -> Lang a -> Lang a
boundLang _ (Lang _ (Left err)) = Lang False $ Left err
boundLang bound (Lang recursive (Right model'))
    | recursive && not (IntSet.null $ modelReaches model') = Lang False $ Left BoundedRecursiveOccurrence
    | total <= 0 = Lang False $ Left EmptyGenerator
    | otherwise =
        finiteLang
            Model
                { modelFinite =
                    Just
                        ( total
                        , [ Member value size (count * mass / fromInteger total) (count * mass)
                          | size <- sizes
                          , let count = fromInteger $ modelCount model' size
                          , (value, mass) <- modelClass model' size
                          ]
                        )
                , modelAtomic = False
                , modelCount = \size -> if size <= bound then modelCount model' size else 0
                , modelClass = \size -> if size <= bound then modelClass model' size else []
                , modelMinimum = listToMaybe sizes
                , modelLargest = Just $ last sizes
                , modelReaches = IntSet.empty
                , modelUnguarded = IntSet.empty
                , modelTermless = IntSet.empty
                }
  where
    sizes = [size | size <- [0 .. bound], modelCount model' size > 0]
    total = sum $ map (modelCount model') sizes

{- | A recursion, as the engine builds it. A probe with an assumed minimum
size for the occurrence decides whether the body reaches the occurrence,
whether a product guards it, and the minimum size. The assumption starts at
none and takes the minimum that the body gives, until the two agree. Then the
counts and the size classes tie through the occurrence.
-}
recurLang :: Env -> Desc -> Lang Value
recurLang env@(Env flat grouped) body = case langModel probed of
    Left err -> Lang False $ Left err
    Right probedModel
        | not $ IntSet.member token $ modelReaches probedModel -> probed
        | IntSet.member token $ IntSet.union (modelUnguarded probedModel) (modelTermless probedModel) ->
            Lang True $ Left UnguardedRecursion
        | Nothing <- modelMinimum probedModel -> Lang True $ Left EmptyGenerator
        | otherwise -> Lang True $ Right $ tied $ modelMinimum probedModel
  where
    token = nextToken env
    withOccurrence occurrence = interpret (Env (occurrence : flat) grouped) body

    probed = converge Nothing
    converge assumed
        | next == assumed = probedBody
        | otherwise = converge next
      where
        probedBody = withOccurrence $ Occurrence token assumed (const probeError) (const probeError)
        next = minimumOf [assumed, either (const Nothing) modelMinimum $ langModel probedBody]

    tied minimum' = knot
      where
        knot = case langModel $ withOccurrence $ Occurrence token minimum' countAt classAt of
            Right model' -> closeToken token model'
            Left err -> error $ "Data.CFTA.Gen.Reference.recurLang: the tied body failed with " <> show err
        countAt = memo 0 $ modelCount knot
        classAt = memo [] $ modelClass knot

-- | A tied recursion: recursive, and no longer reaching its own occurrence.
closeToken :: Int -> Model a -> Model a
closeToken token model' =
    model'
        { modelFinite = Nothing
        , modelLargest = Nothing
        , modelReaches = IntSet.delete token $ modelReaches model'
        , modelUnguarded = IntSet.delete token $ modelUnguarded model'
        , modelTermless = IntSet.delete token $ modelTermless model'
        }

-- | Remember a function of the sizes from zero, with the given answer below zero.
memo :: b -> (Integer -> b) -> Integer -> b
memo below function = \size -> if size < 0 then below else table !! fromInteger size
  where
    table = map function [0 ..]

probeError :: a
probeError = error "Data.CFTA.Gen.Reference: a probe counts nothing"

interpretGrouped :: Env -> GDesc -> Family Int Value
interpretGrouped env@(Env _ grouped) = \case
    Keyed key inner -> keyedFamily key $ flatten inner
    GroupOn n inner -> groupOnFamily (groupKey n) $ flatten inner
    Regroup n family -> regroupFamily (`mod` max 1 n) $ go family
    MapWithKey family -> mapWithKeyFamily Tagged $ go family
    GNode _ family -> nodeFamily $ go family
    Frequencies alternatives -> frequenciesFamily [(weight, go alternative) | (weight, alternative) <- alternatives]
    Apply1 operations argument ->
        applyFamily
            ( frequenciesFamily
                [ (1, keyedFamily ([argumentKey], resultKey) $ unary <$> flatten operation)
                | (argumentKey, resultKey, operation) <- operations
                ]
            )
            [go argument]
    Apply2 operations first second ->
        applyFamily
            ( frequenciesFamily
                [ (1, keyedFamily ([firstKey, secondKey], resultKey) $ binary <$> flatten operation)
                | (firstKey, secondKey, resultKey, operation) <- operations
                ]
            )
            [go first, go second]
    RecurGrouped body -> recurGroupedFamily env body
    GVar index -> Family True $ Right $ grouped !! index
  where
    flatten = interpret env
    go = interpretGrouped env
    unary v = \case
        [a] -> Paired v a
        _ -> error "Data.CFTA.Gen.Reference.interpretGrouped: a unary operation without one argument"
    binary v = \case
        [a, b] -> Paired v (Paired a b)
        _ -> error "Data.CFTA.Gen.Reference.interpretGrouped: a binary operation without two arguments"

atKeyLang :: (Ord key) => key -> Family key a -> Lang a
atKeyLang key (Family recursive groups) =
    Lang recursive $ groups >>= maybe (Left EmptyGenerator) (Right . groupModel) . Map.lookup key

keyedFamily :: key -> Lang a -> Family key a
keyedFamily key (Lang recursive result) = Family recursive $ Map.singleton key . group <$> result
  where
    group model'
        | recursive = Group model' 0 (byCount model')
        | otherwise = Group model' 1 noMassBySize

noMassBySize :: Integer -> Rational
noMassBySize = error "Data.CFTA.Gen.Reference: a finite group has no mass by size"

{- | Group the members of a finite language by a key. Every member of a group
has size one. The group keeps the weights of its members in their size
classes, and the atomic marker of the language.
-}
groupOnFamily :: (Ord key) => (a -> key) -> Lang a -> Family key a
groupOnFamily _ (Lang False (Left err)) = Family False $ Left err
groupOnFamily _ (Lang True (Left err)) = Family False $ Left err
groupOnFamily _ (Lang True _) = Family False $ Left UnboundedGenerator
groupOnFamily key (Lang False (Right model')) = Family False $ Right $ fmap bucket grouped
  where
    grouped = Map.fromListWith (flip (<>)) [(key $ memberValue member, [member]) | member <- maybe [] snd $ modelFinite model']
    bucket bucketMembers = Group bucketModel mass noMassBySize
      where
        count = toInteger $ length bucketMembers
        mass = sum $ map memberMass bucketMembers
        weight = sum $ map memberWeight bucketMembers
        bucketModel =
            (atomModel (modelAtomic model') [(memberValue member, memberWeight member / weight) | member <- bucketMembers])
                { modelFinite =
                    Just
                        ( count
                        , [ Member (memberValue member) 1 (memberMass member / mass) (fromInteger count * memberWeight member / weight)
                          | member <- bucketMembers
                          ]
                        )
                }

-- | Merge the groups that the new key puts together, in the order of their old keys.
regroupFamily :: (Ord newKey) => (key -> newKey) -> Family key a -> Family newKey a
regroupFamily regroup (Family recursive groups) =
    Family recursive $ do
        groups' <- groups
        let together = Map.fromListWith (flip (<>)) [(regroup key, [group]) | (key, group) <- Map.toAscList groups']
        if recursive
            then Right $ fmap mergeRecursive together
            else traverse (mergeFinite . map (\group -> (groupMass group, groupModel group))) together

{- | Merge finite groups: one choice weighted by their masses. Atomic groups of
one size merge to one atom of that size.
-}
mergeFinite :: [(Rational, Model a)] -> Either GenError (Group a)
mergeFinite [(mass, model')] | mass > 0 = Right $ Group model' mass noMassBySize
mergeFinite alternatives
    | null alternatives || any ((<= 0) . fst) alternatives = Left EmptyGenerator
    | otherwise =
        Right $
            Group
                (retainAtomic $ choiceModel [(mass, byCount model', model') | (mass, model') <- alternatives])
                (sum $ map fst alternatives)
                noMassBySize
  where
    retainAtomic
        | all (modelAtomic . snd) alternatives
        , Just atomSize : rest <- map (modelMinimum . snd) alternatives
        , all (== Just atomSize) rest =
            atomicModel atomSize
        | otherwise = id

-- | Merge recursive groups: one choice that selects by mass in a size class.
mergeRecursive :: [Group a] -> Group a
mergeRecursive [only] = only
mergeRecursive alternatives =
    Group
        (choiceModel [(0, groupMassAt group, groupModel group) | group <- alternatives])
        0
        (\size -> sum [groupMassAt group size | group <- alternatives])

mapWithKeyFamily :: (key -> a -> b) -> Family key a -> Family key b
mapWithKeyFamily transform (Family recursive groups) =
    Family recursive $ Map.mapWithKey (fmap . transform) <$> groups

frequenciesFamily :: (Ord key) => [(Integer, Family key a)] -> Family key a
frequenciesFamily weighted
    | weight : _ <- [weight | (weight, _) <- weighted, weight <= 0] =
        Family False $ Left $ NonPositiveWeight $ Weight weight
    | err : _ <- [err | (_, Family _ (Left err)) <- weighted, err /= EmptyGenerator] =
        Family False $ Left err
    | null live = Family False $ Left EmptyGenerator
    | any (familyRecursive . snd) live =
        Family True $
            if equalWeights $ map fst live
                then mergeByKey . concatMap Map.toAscList <$> traverse (recursiveGroups . snd) live
                else Left WeightedRecursiveAlternatives
    | otherwise =
        Family False
            $ traverse mergeFinite
            $ Map.fromListWith
                (flip (<>))
                [ (key, [(fromInteger weight / fromInteger totalWeight * groupMass group, groupModel group)])
                | (weight, Family _ (Right groups)) <- live
                , (key, group) <- Map.toAscList groups
                ]
  where
    live = [alternative | alternative@(_, Family _ result) <- weighted, not $ isEmpty result]
    totalWeight = sum $ map fst live

-- | Merge recursive groups that share a key, in their order.
mergeByKey :: (Ord key) => [(key, Group a)] -> Map.Map key (Group a)
mergeByKey entries = mergeRecursive <$> Map.fromListWith (flip (<>)) [(key, [group]) | (key, group) <- entries]

-- | The groups of a family as recursive groups.
recursiveGroups :: Family key a -> Either GenError (Map.Map key (Group a))
recursiveGroups (Family True groups) = groups
recursiveGroups (Family False groups) = fromBuckets <$> groups

{- | Finite groups as recursive ones. The mass of an ordinary group is its
member count at each size. An atomic group has its members at one size, and
its mass there is its key mass times the number of members of the family.
-}
fromBuckets :: Map.Map key (Group a) -> Map.Map key (Group a)
fromBuckets buckets = fmap fromBucket buckets
  where
    totalCount = sum [count | group <- Map.elems buckets, Just (count, _) <- [modelFinite $ groupModel group]]
    fromBucket group = Group model' 0 massAt
      where
        model' = (groupModel group){modelFinite = Nothing}
        atomMass = fromInteger totalCount * groupMass group
        -- The members of an atomic group have one size: one, or more under a pay.
        massAt
            | modelAtomic model' = \size -> if Just size == modelMinimum model' then atomMass else 0
            | otherwise = byCount model'

{- | Apply a finite operation family to argument families. The operations and
their argument keys give the components, in operation key order. A finite
application merges the components by result key and normalizes their masses. A
recursive one merges them as a recursive family.
-}
applyFamily :: Family ([Int], Int) ([a] -> b) -> [Family Int a] -> Family Int b
applyFamily (Family True (Left err)) _ = Family False $ Left err
applyFamily (Family True _) _ = Family False $ Left RecursiveOperationFamily
applyFamily (Family False (Left err)) _ = Family False $ Left err
applyFamily (Family False (Right operations)) arguments
    | any familyRecursive arguments = Family True $ do
        argumentGroups <- traverse recursiveGroups arguments
        pure $
            mergeByKey
                [ (resultKey, joinRecursive operation matched)
                | ((argumentKeys, resultKey), operation) <- Map.toAscList $ fromBuckets operations
                , Just matched <- [lookupArguments argumentKeys argumentGroups]
                ]
    | otherwise = Family False $ do
        argumentGroups <- traverse familyGroups arguments
        mergeComponents
            [ (resultKey, groupMass operation * product (map groupMass matched), joinFinite operation matched)
            | ((argumentKeys, resultKey), operation) <- Map.toAscList operations
            , Just matched <- [lookupArguments argumentKeys argumentGroups]
            ]
  where
    lookupArguments argumentKeys argumentGroups = traverse (uncurry Map.lookup) $ zip argumentKeys argumentGroups

-- | One finite component: the operation, then each argument, in mixed radix.
joinFinite :: Group ([a] -> b) -> [Group a] -> Model b
joinFinite operation arguments = ($ []) <$> foldl consume (groupModel operation) arguments
  where
    consume partial argument =
        pairModel
            (\function value rest -> function (value : rest))
            (byCount partial)
            partial
            (byCount $ groupModel argument)
            (groupModel argument)

-- | One recursive component: a product that selects the sizes of its parts by mass.
joinRecursive :: Group ([a] -> b) -> [Group a] -> Group b
joinRecursive operation arguments = ($ []) <$> foldl consume operation arguments
  where
    consume partial argument =
        Group
            ( pairModel
                (\function value rest -> function (value : rest))
                (groupMassAt partial)
                (groupModel partial)
                (groupMassAt argument)
                (groupModel argument)
            )
            0
            ( \size ->
                sum
                    [ groupMassAt partial leftSize * groupMassAt argument (size - leftSize)
                    | leftSize <- productSplits (modelMinimum $ groupModel partial) (modelMinimum $ groupModel argument) size
                    ]
            )

-- | Merge finite components by result key, in their order, and normalize the masses.
mergeComponents :: (Ord key) => [(key, Rational, Model a)] -> Either GenError (Map.Map key (Group a))
mergeComponents [] = Left EmptyGenerator
mergeComponents components = do
    merged <-
        traverse mergeFinite $ Map.fromListWith (flip (<>)) [(key, [(mass, model')]) | (key, mass, model') <- components]
    let total = sum $ map groupMass $ Map.elems merged
    pure $ fmap (\group -> group{groupMass = groupMass group / total}) merged

{- | A grouped recursion, as the engine builds it. The keys grow from none, and
the minimum of each key converges as the minimum of 'recurLang' does: each
pass builds the body around a probe of each key found so far, with the least
minimum found so far. A probe around the final minimums decides whether the
body reaches the family and whether a product guards it. Then the counts, the
masses, and the size classes of every key tie through the family.
-}
recurGroupedFamily :: Env -> GDesc -> Family Int Value
recurGroupedFamily env@(Env flat grouped) body = case familyGroups probed of
    Left err -> Family False $ Left err
    Right groups
        | not $ any (IntSet.member token . modelReaches . groupModel) groups -> probed
        | otherwise -> Family True result
  where
    token = nextToken env
    withFamily family = interpretGrouped (Env flat (family : grouped)) body
    placeholders groupAt = Map.fromList [(key, groupAt key) | key <- Map.keys keyMinimums]
    placeholder minimum' flags = flaggedPlaceholder minimum' (flags, flags, flags)
    flaggedPlaceholder minimum' (reaches, unguarded, termless) count classAt massAt =
        Group (Model Nothing False count classAt minimum' Nothing reaches unguarded termless) 0 massAt

    probe minimum' = placeholder minimum' (IntSet.singleton token) probeError probeError probeError
    probeWith minimumAt = withFamily $ placeholders $ probe . minimumAt

    keyMinimums = converge Map.empty
      where
        converge current
            | grown == current = current
            | otherwise = converge grown
          where
            reached =
                either (const Map.empty) (fmap $ modelMinimum . groupModel)
                    $ familyGroups
                    $ withFamily
                    $ fmap probe current
            grown = Map.unionWith (\left right -> minimumOf [left, right]) current reached
    minimumSizes = Map.mapMaybe id keyMinimums

    probed = probeWith (`Map.lookup` minimumSizes)

    result = do
        probedGroups <- familyGroups probed
        when (any (IntSet.member token . guardFlags . groupModel) probedGroups) $ Left UnguardedRecursion
        when (Map.null minimumSizes) $ Left EmptyGenerator
        pure $ Map.filterWithKey (\key _ -> Map.member key minimumSizes) tiedGroups

    tiedGroups = case familyGroups $ withFamily tiedPlaceholders of
        Right groups -> fmap (\group -> group{groupModel = closeToken token $ groupModel group}) groups
        Left err -> error $ "Data.CFTA.Gen.Reference.recurGroupedFamily: the tied body failed with " <> show err
    tiedPlaceholders = placeholders $ \key ->
        flaggedPlaceholder
            (Map.lookup key minimumSizes)
            (Map.findWithDefault (IntSet.empty, IntSet.empty, IntSet.empty) key keyFlags)
            (tiedAt key 0 $ modelCount . groupModel)
            (tiedAt key [] $ modelClass . groupModel)
            (tiedAt key 0 groupMassAt)
    -- The enclosing occurrences that the body of each key reaches, and those it
    -- leaves unguarded, also through other keys: each pass builds the body
    -- around occurrences that carry the flags of the pass before.
    keyFlags = converge Map.empty
      where
        converge previous
            | next == previous = previous
            | otherwise = converge next
          where
            next =
                either (const Map.empty) (fmap $ flagsOf . groupModel) $
                    familyGroups $
                        withFamily $
                            placeholders $
                                \key ->
                                    flaggedPlaceholder
                                        (Map.lookup key minimumSizes)
                                        (Map.findWithDefault (IntSet.empty, IntSet.empty, IntSet.empty) key previous)
                                        probeError
                                        probeError
                                        probeError
        flagsOf model' =
            ( IntSet.delete token $ modelReaches model'
            , IntSet.delete token $ modelUnguarded model'
            , IntSet.delete token $ modelTermless model'
            )
    guardFlags model' = IntSet.union (modelUnguarded model') (modelTermless model')
    tiedAt :: Int -> b -> (Group Value -> Integer -> b) -> Integer -> b
    tiedAt key below field = maybe (const below) (memo below . field) $ Map.lookup key tiedGroups
