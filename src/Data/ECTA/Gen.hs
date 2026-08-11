{-# LANGUAGE OverloadedStrings #-}

{- | Indexed generators whose transparent regions are represented as ECTAs.

An indexed source stores a finite cardinality and a function from indices to
values. Applicative composition tracks exact cardinalities and rank-based
selection alongside the ECTA, without materializing the product language.
Joins count matched group products and unrank directly within them.
-}
module Data.ECTA.Gen (
    Indexed (..),
    ECTAGen,
    ECTAGenBy,
    Sig (..),
    Keys (..),
    Args (..),
    ECTAGenError (..),
    GenBackend (..),
    fromIndexed,
    fromBackend,
    elements,
    elementsBy,
    regroupBy,
    sizeBy,
    atKey,
    apply,
    ungroup,
    frequency,
    On (..),
    match,
    support,
    cardinality,
    unrank,
    countBy,
    pmf,
    lower,
    lowerWithRank,
) where

import Data.Foldable (toList)
import Data.Kind (Type)
import qualified Data.Map.Strict as Map
import Data.Ratio (denominator, numerator)
import Data.Sequence (Seq)
import qualified Data.Sequence as Sequence
import qualified Data.Text as Text

import Data.ECTA (
    Edge (Edge),
    Node (EmptyNode, Node),
    mkEdge,
    reducePartially,
 )
import Data.ECTA.Paths (mkEqConstraints, path)
import Data.ECTA.Term (Symbol (Symbol), Term (Term))

{- | A finite source addressed by a stable integer index.

The selector is called only with an index in @[0, indexedCardinality)@.
-}
data Indexed a = Indexed
    { indexedCardinality :: !Integer
    -- ^ Number of selectable values.
    , indexedSelect :: Integer -> a
    -- ^ Decode one valid index.
    }

-- | Backend operations needed only when sampling or crossing an opaque region.
class (Applicative gen) => GenBackend gen where
    -- | Select an integer in @[0, bound)@.
    selectInteger :: Integer -> gen Integer

    -- | Select one backend generator with a positive relative weight.
    frequencyGen :: [(Integer, gen a)] -> gen a

    -- | Retry until the generated value satisfies a predicate.
    filterGen :: (a -> Bool) -> gen a -> gen a

-- | Backend-independent plans for sampling a value, with or without its rank.
data Sampler a = Sampler
    { runValueSampler :: forall gen. (GenBackend gen) => gen a
    , runRankSampler :: forall gen. (GenBackend gen) => gen (Integer, a)
    }

-- | Failure while constructing, inspecting, or sampling a generator.
data ECTAGenError
    = EmptyGenerator
    | NonPositiveWeight !Integer
    | CannotInspectOpaqueGenerator
    | SelectionOutOfRange !Integer !Integer
    deriving (Eq, Show)

-- | One term, its normalized probability mass, and its decoded value.
data Outcome a = Outcome
    { outcomeTerm :: Term
    , outcomeMass :: Rational
    , outcomeValue :: a
    }

-- | A finite language with exact cardinality and rank-based selection.
data OutcomeIndex a = OutcomeIndex
    { outcomeCardinality :: !Integer
    , outcomeUniformMass :: !(Maybe Rational)
    , outcomeSelect :: Integer -> Either ECTAGenError (Outcome a)
    , outcomeValueAt :: Integer -> a
    , outcomeSampler :: !(Sampler a)
    }

-- | One equality-key bucket used to count and unrank a conditioned product.
data JoinGroup left right = JoinGroup
    { joinGroupIndex :: !Int
    , joinGroupLeft :: !(Seq (Outcome left))
    , joinGroupRight :: !(Seq (Outcome right))
    }

-- | One transparent ECTA with a matching indexed outcome language.
data Static a = Static
    { staticSupport :: !Node
    , staticOutcomes :: !(OutcomeIndex a)
    }

-- | One compact conditional generator and its mass in the whole distribution.
data KeyedBucket a = KeyedBucket
    { keyedBucketMass :: !Rational
    , keyedBucketStatic :: !(Static a)
    }

{- | A transparent generator whose values are classified by a projected key.

The key is not part of the generated value. It classifies values into groups;
during a join, matching key values determine which groups receive equal internal
labels on constrained ECTA paths. Each key group retains compact ECTA support
and indexed selection without storing all outcomes.
-}
newtype ECTAGenBy (gen :: Type -> Type) key a
    = ECTAGenBy (Either ECTAGenError (Map.Map key (KeyedBucket a)))

{- | A heterogeneous list of group keys, one per generated operation argument.

Lists are compared lexicographically, element by element.
-}
data Keys (argKeys :: [Type]) where
    KNil :: Keys '[]
    (:*) :: argKey -> Keys argKeys -> Keys (argKey ': argKeys)

infixr 5 :*

instance Eq (Keys '[]) where
    KNil == KNil = True

instance (Eq argKey, Eq (Keys argKeys)) => Eq (Keys (argKey ': argKeys)) where
    (key :* keys) == (otherKey :* otherKeys) =
        key == otherKey && keys == otherKeys

instance Ord (Keys '[]) where
    compare KNil KNil = EQ

instance (Ord argKey, Ord (Keys argKeys)) => Ord (Keys (argKey ': argKeys)) where
    compare (key :* keys) (otherKey :* otherKeys) =
        compare key otherKey <> compare keys otherKeys

instance Show (Keys '[]) where
    showsPrec _ KNil = showString "KNil"

instance (Show argKey, Show (Keys argKeys)) => Show (Keys (argKey ': argKeys)) where
    showsPrec depth (key :* keys) =
        showParen (depth > 5) $
            showsPrec 6 key . showString " :* " . showsPrec 5 keys

{- | The input and result group keys for a generated operation of any arity.

The constructor makes the argument and result roles explicit at construction
sites and distinguishes operation signatures from unrelated keys.
-}
data Sig (argKeys :: [Type]) result = Keys argKeys :-> result

infixr 0 :->

deriving instance (Eq (Keys argKeys), Eq result) => Eq (Sig argKeys result)
deriving instance (Ord (Keys argKeys), Ord result) => Ord (Sig argKeys result)
deriving instance (Show (Keys argKeys), Show result) => Show (Sig argKeys result)

{- | Argument families for 'apply', one per signature component, in order.

Each link requires the family key type named by the corresponding signature
component and consumes the corresponding argument of the generated operation.
-}
data Args gen (argKeys :: [Type]) operation result where
    ANil :: Args gen '[] result result
    (:&) ::
        (Ord argKey) =>
        ECTAGenBy gen argKey arg ->
        Args gen argKeys operation result ->
        Args gen (argKey ': argKeys) (arg -> operation) result

infixr 5 :&

{- | Reified key equalities between one value of each side.

@leftKey ':==:' rightKey@ requires the two projected keys to agree, and
':&&:' conjoins equalities. Keeping the projections as data lets a match
group each input by its own key instead of testing sampled pairs.
-}
data On left right where
    (:==:) :: (Ord key) => (left -> key) -> (right -> key) -> On left right
    (:&&:) :: On left right -> On left right -> On left right

infix 4 :==:
infixr 3 :&&:

-- | Interpret a reified condition as one key projection per side.
withKeys ::
    On left right ->
    (forall key. (Ord key) => (left -> key) -> (right -> key) -> t) ->
    t
withKeys (leftKey :==: rightKey) continue = continue leftKey rightKey
withKeys (first :&&: second) continue =
    withKeys first $ \leftKey rightKey ->
        withKeys second $ \otherLeftKey otherRightKey ->
            continue
                (\left -> (leftKey left, otherLeftKey left))
                (\right -> (rightKey right, otherRightKey right))

-- | A generator is either inspectable ECTA structure or an opaque backend action.
data ECTAGen gen a
    = Transparent !(Either ECTAGenError (Static a))
    | Opaque !(gen (Either ECTAGenError a))

instance Functor (ECTAGenBy gen key) where
    fmap transform (ECTAGenBy result) =
        ECTAGenBy $ fmap (fmap mapBucket) result
      where
        mapBucket bucket =
            KeyedBucket
                (keyedBucketMass bucket)
                (mapStatic transform $ keyedBucketStatic bucket)

instance (Functor gen) => Functor (ECTAGen gen) where
    fmap transform (Transparent result) = Transparent $ fmap (mapStatic transform) result
    fmap transform (Opaque generated) = Opaque $ fmap (fmap transform) generated

instance (GenBackend gen) => Applicative (ECTAGen gen) where
    pure value = Transparent $ Right $ pureStatic value

    Transparent (Left err) <*> _ = Transparent $ Left err
    _ <*> Transparent (Left err) = Transparent $ Left err
    Transparent (Right functions) <*> Transparent (Right values) =
        Transparent $ Right $ applyStatic functions values
    functions <*> values =
        Opaque $ liftA2 (<*>) (lower functions) (lower values)

-- | Lift one finite indexed source into transparent ECTA structure.
fromIndexed :: Indexed a -> ECTAGen gen a
fromIndexed indexed
    | indexedCardinality indexed <= 0 = Transparent $ Left EmptyGenerator
    | otherwise = Transparent $ Right $ indexedStatic indexed

-- | Embed an opaque backend generator.
fromBackend :: (Functor gen) => gen a -> ECTAGen gen a
fromBackend generated = Opaque $ Right <$> generated

-- | Choose uniformly from a finite non-empty list.
elements :: [a] -> ECTAGen gen a
elements values =
    fromIndexed $
        Indexed
            (toInteger $ length values)
            (\index -> atIndex "elements" index values)

{- | Uniformly choose from a finite source while retaining the projected keys
used to match groups in later path equalities.

Keys are ordered by their 'Ord' instance. Values within each key retain their
source order.
-}
elementsBy :: (Ord key) => (a -> key) -> [a] -> ECTAGenBy gen key a
elementsBy _ [] = ECTAGenBy $ Left EmptyGenerator
elementsBy key values =
    ECTAGenBy $
        Right $
            Map.map makeBucket $
                foldl' insertValue Map.empty values
  where
    totalOutcomes = toInteger $ length values

    insertValue buckets value =
        Map.insertWith (flip (<>)) (key value) [value] buckets

    makeBucket bucketValues =
        let bucketCardinality = toInteger $ length bucketValues
         in KeyedBucket
                (fromInteger bucketCardinality / fromInteger totalOutcomes)
                ( indexedStatic $
                    Indexed
                        bucketCardinality
                        (\index -> atIndex "elementsBy" index bucketValues)
                )

{- | Reclassify the groups without enumerating their values.

When several old keys map to one new key, their compact supports are merged and
their probability masses are preserved.
-}
regroupBy :: (Ord newKey) => (oldKey -> newKey) -> ECTAGenBy gen oldKey a -> ECTAGenBy gen newKey a
regroupBy _ (ECTAGenBy (Left err)) = ECTAGenBy $ Left err
regroupBy regroup (ECTAGenBy (Right buckets)) =
    ECTAGenBy $ traverse mergeBucketGroup grouped
  where
    grouped =
        Map.foldlWithKey'
            ( \groups oldKey bucket ->
                Map.insertWith
                    (flip (<>))
                    (regroup oldKey)
                    [(keyedBucketMass bucket, keyedBucketStatic bucket)]
                    groups
            )
            Map.empty
            buckets

-- | Return the exact cardinality of each retained group in O(number of groups).
sizeBy :: ECTAGenBy gen key a -> Either ECTAGenError (Map.Map key Integer)
sizeBy (ECTAGenBy result) =
    fmap (fmap $ outcomeCardinality . staticOutcomes . keyedBucketStatic) result

{- | Select one retained group as an ordinary conditional generator.

A missing key produces 'EmptyGenerator'.
-}
atKey :: (Ord key) => key -> ECTAGenBy gen key a -> ECTAGen gen a
atKey _ (ECTAGenBy (Left err)) = Transparent $ Left err
atKey key (ECTAGenBy (Right buckets)) =
    Transparent $
        maybe
            (Left EmptyGenerator)
            (Right . keyedBucketStatic)
            (Map.lookup key buckets)

{- | Apply a generated operation of any arity to one argument family per
signature component, retaining the operation's result group.

The operation family must already hold functions consuming the 'Args' chain
left to right; use 'fmap' to attach a compiling function. Every matched
component joins the operation group and all
argument groups in one ECTA edge holding one equality constraint per argument.
Ranks are ordered by result key, then signature, then operation rank, then
argument ranks left to right.
-}
apply ::
    (Ord resultKey) =>
    ECTAGenBy gen (Sig argKeys resultKey) operation ->
    Args gen argKeys operation result ->
    ECTAGenBy gen resultKey result
apply (ECTAGenBy (Left err)) _ = ECTAGenBy $ Left err
apply (ECTAGenBy (Right operations)) arguments = ECTAGenBy $ do
    argumentMaps <- argsMaps arguments
    let matchingBuckets =
            [ (componentIndex, resultKey, operationBucket, mass, argumentBuckets)
            | (componentIndex, (argKeys :-> resultKey, operationBucket)) <-
                zip [0 :: Int ..] $ Map.toAscList operations
            , Just (mass, argumentBuckets) <- [lookupArgs argKeys argumentMaps]
            ]
    components <- traverse buildComponent matchingBuckets
    mergeComponentsByKey components
  where
    buildComponent (componentIndex, resultKey, operationBucket, argumentsMass, argumentBuckets) = do
        joined <-
            joinNBucketStatic
                componentIndex
                (keyedBucketStatic operationBucket)
                argumentBuckets
        pure
            ( resultKey
            , keyedBucketMass operationBucket * argumentsMass
            , joined
            )

-- | Bucket maps of every argument family, threaded through the operation type.
data ArgMaps (argKeys :: [Type]) operation result where
    MapsNil :: ArgMaps '[] result result
    MapsCons ::
        (Ord argKey) =>
        Map.Map argKey (KeyedBucket arg) ->
        ArgMaps argKeys operation result ->
        ArgMaps (argKey ': argKeys) (arg -> operation) result

argsMaps :: Args gen argKeys operation result -> Either ECTAGenError (ArgMaps argKeys operation result)
argsMaps ANil = Right MapsNil
argsMaps (ECTAGenBy family :& rest) = MapsCons <$> family <*> argsMaps rest

-- | The matched group of every argument family, in signature order.
data ArgStatics operation result where
    StaticsNil :: ArgStatics result result
    StaticsCons ::
        Static arg ->
        ArgStatics operation result ->
        ArgStatics (arg -> operation) result

lookupArgs ::
    Keys argKeys ->
    ArgMaps argKeys operation result ->
    Maybe (Rational, ArgStatics operation result)
lookupArgs KNil MapsNil = Just (1, StaticsNil)
lookupArgs (key :* keys) (MapsCons buckets rest) = do
    bucket <- Map.lookup key buckets
    (mass, statics) <- lookupArgs keys rest
    Just
        ( keyedBucketMass bucket * mass
        , StaticsCons (keyedBucketStatic bucket) statics
        )

-- | Merge all retained groups while preserving their probability masses.
ungroup :: ECTAGenBy gen key a -> ECTAGen gen a
ungroup (ECTAGenBy (Left err)) = Transparent $ Left err
ungroup (ECTAGenBy (Right buckets)) =
    Transparent $ mergeKeyedBuckets buckets

-- | Choose one generator with the supplied positive relative weight.
frequency ::
    (GenBackend gen) =>
    [(Integer, ECTAGen gen a)] ->
    ECTAGen gen a
frequency [] = Transparent $ Left EmptyGenerator
frequency alternatives
    | Just badWeight <- firstNonPositive alternatives =
        Transparent $ Left $ NonPositiveWeight badWeight
    | Just err <- firstError alternatives = Transparent $ Left err
    | Just staticAlternatives <- traverse getStatic alternatives =
        Transparent $ Right $ frequencyStatic staticAlternatives
    | otherwise =
        Opaque $
            frequencyGen
                [(weight, lower generator) | (weight, generator) <- alternatives]
  where
    firstNonPositive = go
      where
        go [] = Nothing
        go ((weight, _) : rest)
            | weight <= 0 = Just weight
            | otherwise = go rest

    firstError = go
      where
        go [] = Nothing
        go ((_, Transparent (Left err)) : _) = Just err
        go (_ : rest) = go rest

    getStatic (weight, Transparent (Right static)) = Just (weight, static)
    getStatic _ = Nothing

-- | Generate two values whose projected keys agree.
match ::
    (GenBackend gen) =>
    On left right ->
    ECTAGen gen left ->
    ECTAGen gen right ->
    ECTAGen gen (left, right)
match _ (Transparent (Left err)) _ = Transparent $ Left err
match _ _ (Transparent (Left err)) = Transparent $ Left err
match condition (Transparent (Right left)) (Transparent (Right right)) =
    withKeys condition $ \leftKey rightKey ->
        Transparent $ joinStatic leftKey rightKey left right
match condition left right =
    withKeys condition $ \leftKey rightKey ->
        let generatedPairs = liftA2 (liftA2 (,)) (lower left) (lower right)
            matches (Left _) = True
            matches (Right (leftValue, rightValue)) =
                leftKey leftValue == rightKey rightValue
         in Opaque $ filterGen matches generatedPairs

-- | Return the ECTA support of a fully transparent generator.
support :: ECTAGen gen a -> Either ECTAGenError Node
support (Transparent result) = staticSupport <$> result
support (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Return the exact number of ranks in a transparent generator.
cardinality :: ECTAGen gen a -> Either ECTAGenError Integer
cardinality (Transparent result) =
    outcomeCardinality . staticOutcomes <$> result
cardinality (Opaque _) = Left CannotInspectOpaqueGenerator

{- | Decode one stable rank from a transparent generator.

Ranks are stable while the generator definition and the ordering of its finite
sources remain unchanged.
-}
unrank :: ECTAGen gen a -> Integer -> Either ECTAGenError a
unrank (Transparent result) index = do
    static <- result
    let outcomes = staticOutcomes static
    checkIndex (outcomeCardinality outcomes) index
    pure $ outcomeValueAt outcomes index
unrank (Opaque _) _ = Left CannotInspectOpaqueGenerator

-- | Count ranked outcomes by a projected key without aggregating equal values.
countBy :: (Ord key) => (a -> key) -> ECTAGen gen a -> Either ECTAGenError (Map.Map key Integer)
countBy key (Transparent result) = do
    static <- result
    outcomes <- enumerateOutcomeIndex $ staticOutcomes static
    pure $
        Map.fromListWith
            (+)
            [(key $ outcomeValue outcome, 1) | outcome <- outcomes]
countBy _ (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Aggregate the exact probability mass of every transparent result.
pmf :: (Ord a) => ECTAGen gen a -> Either ECTAGenError [(a, Rational)]
pmf (Transparent result) = do
    static <- result
    outcomes <- compileOutcomes static
    pure $
        Map.toAscList $
            Map.fromListWith (+) [(value, mass) | (mass, value) <- outcomes]
pmf (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Lower to the backend, preserving construction and decoding errors.
lower :: (GenBackend gen) => ECTAGen gen a -> gen (Either ECTAGenError a)
lower (Transparent (Left err)) = pure $ Left err
lower (Transparent (Right static)) = sampleStatic static
lower (Opaque generated) = generated

-- | Lower a transparent generator while retaining the sampled rank.
lowerWithRank ::
    (GenBackend gen) =>
    ECTAGen gen a ->
    gen (Either ECTAGenError (Integer, a))
lowerWithRank (Transparent (Left err)) = pure $ Left err
lowerWithRank (Transparent (Right static)) = sampleStaticWithRank static
lowerWithRank (Opaque _) = pure $ Left CannotInspectOpaqueGenerator

mapStatic :: (a -> b) -> Static a -> Static b
mapStatic transform static =
    Static
        (staticSupport static)
        (mapOutcomeIndex transform $ staticOutcomes static)

pureStatic :: a -> Static a
pureStatic value =
    Static
        (Node [Edge pureSymbol []])
        ( OutcomeIndex
            1
            (Just 1)
            ( \index -> do
                checkIndex 1 index
                pure $ Outcome (Term pureSymbol []) 1 value
            )
            (\_ -> value)
            (uniformSampler 1 $ const value)
        )

indexedStatic :: Indexed a -> Static a
indexedStatic indexed =
    Static
        (Node [Edge (indexedSymbol index) [] | index <- [0 .. totalOutcomes - 1]])
        ( OutcomeIndex
            totalOutcomes
            (Just $ 1 / fromInteger totalOutcomes)
            select
            (indexedSelect indexed)
            (uniformSampler totalOutcomes $ indexedSelect indexed)
        )
  where
    totalOutcomes = indexedCardinality indexed
    select index = do
        checkIndex totalOutcomes index
        pure $
            Outcome
                (Term (indexedSymbol index) [])
                (1 / fromInteger totalOutcomes)
                (indexedSelect indexed index)

applyStatic :: Static (a -> b) -> Static a -> Static b
applyStatic functions values =
    Static
        ( Node
            [ Edge
                applySymbol
                [staticSupport functions, staticSupport values]
            ]
        )
        ( OutcomeIndex
            totalOutcomes
            ((*) <$> outcomeUniformMass functionOutcomes <*> outcomeUniformMass valueOutcomes)
            select
            selectValue
            ( productSampler
                valueCardinality
                (outcomeSampler functionOutcomes)
                (outcomeSampler valueOutcomes)
            )
        )
  where
    functionOutcomes = staticOutcomes functions
    valueOutcomes = staticOutcomes values
    valueCardinality = outcomeCardinality valueOutcomes
    totalOutcomes = outcomeCardinality functionOutcomes * valueCardinality

    select index = do
        checkIndex totalOutcomes index
        let (functionIndex, valueIndex) = splitIndex index
        functionOutcome <- outcomeSelect functionOutcomes functionIndex
        valueOutcome <- outcomeSelect valueOutcomes valueIndex
        pure $
            Outcome
                ( Term
                    applySymbol
                    [outcomeTerm functionOutcome, outcomeTerm valueOutcome]
                )
                (outcomeMass functionOutcome * outcomeMass valueOutcome)
                (outcomeValue functionOutcome $ outcomeValue valueOutcome)

    selectValue index =
        let (functionIndex, valueIndex) = splitIndex index
         in outcomeValueAt functionOutcomes functionIndex $
                outcomeValueAt valueOutcomes valueIndex

    splitIndex index = index `quotRem` valueCardinality

frequencyStatic :: [(Integer, Static a)] -> Static a
frequencyStatic alternatives =
    Static
        ( Node
            [ Edge (frequencySymbol index) [staticSupport static]
            | (index, (_, static)) <- numbered
            ]
        )
        ( OutcomeIndex
            totalOutcomes
            uniformMass
            select
            selectValue
            sampler
        )
  where
    totalWeight = sum $ map fst alternatives
    numbered = zip [0 :: Int ..] alternatives
    rankedBranches =
        [ ( offset + outcomeCardinality (staticOutcomes static)
          , offset
          , branchIndex
          , weight
          , static
          )
        | (branchIndex, (offset, (weight, static))) <-
            zip [0 :: Int ..] $ offsetAlternatives alternatives
        ]
    totalOutcomes = sum [outcomeCardinality $ staticOutcomes static | (_, static) <- alternatives]
    uniformMass = commonValue $ map branchUniformMass alternatives
    sampler = case uniformMass of
        Just _ -> uniformSampler totalOutcomes selectValue
        Nothing -> frequencySampler alternatives

    branchUniformMass (weight, static) =
        (fromInteger weight / fromInteger totalWeight *)
            <$> outcomeUniformMass (staticOutcomes static)

    select index = do
        checkIndex totalOutcomes index
        let (branchIndex, weight, static, childIndex) = selectBranch index rankedBranches
        child <- outcomeSelect (staticOutcomes static) childIndex
        pure $
            Outcome
                (Term (frequencySymbol branchIndex) [outcomeTerm child])
                ( fromInteger weight
                    / fromInteger totalWeight
                    * outcomeMass child
                )
                (outcomeValue child)

    selectValue index =
        let (_, _, static, childIndex) = selectBranch index rankedBranches
         in outcomeValueAt (staticOutcomes static) childIndex

    selectBranch _ [] = error "frequencyStatic: rank outside alternatives"
    selectBranch index ((upperBound, offset, branchIndex, weight, static) : remaining)
        | index < upperBound = (branchIndex, weight, static, index - offset)
        | otherwise = selectBranch index remaining

joinStatic ::
    (Ord key) =>
    (left -> key) ->
    (right -> key) ->
    Static left ->
    Static right ->
    Either ECTAGenError (Static (left, right))
joinStatic leftKey rightKey left right = do
    leftEntries <- keyedOutcomes leftKey left
    rightEntries <- keyedOutcomes rightKey right
    let shared =
            Map.intersectionWith
                (,)
                (groupOutcomes leftEntries)
                (groupOutcomes rightEntries)
    if Map.null shared
        then Left EmptyGenerator
        else
            let groups =
                    [ JoinGroup
                        keyIndex
                        (Sequence.fromList leftOutcomes)
                        (Sequence.fromList rightOutcomes)
                    | (keyIndex, (_, (leftOutcomes, rightOutcomes))) <-
                        zip [0 :: Int ..] $ Map.toAscList shared
                    ]
                leftNode =
                    Node
                        [ Edge
                            leftKeyedSymbol
                            [ keyNode $ joinGroupIndex group
                            , singletonNode $ outcomeTerm outcome
                            ]
                        | group <- groups
                        , outcome <- toList $ joinGroupLeft group
                        ]
                rightNode =
                    Node
                        [ Edge
                            rightKeyedSymbol
                            [ keyNode $ joinGroupIndex group
                            , singletonNode $ outcomeTerm outcome
                            ]
                        | group <- groups
                        , outcome <- toList $ joinGroupRight group
                        ]
                joined =
                    reducePartially $
                        Node
                            [ mkEdge
                                joinSymbol
                                [leftNode, rightNode]
                                (mkEqConstraints [[path [0, 0], path [1, 0]]])
                            ]
             in if joined == EmptyNode
                    then Left EmptyGenerator
                    else Static joined <$> joinOutcomeIndex left right groups

keyedOutcomes ::
    (value -> key) ->
    Static value ->
    Either ECTAGenError [(key, Outcome value)]
keyedOutcomes key static =
    map (\outcome -> (key $ outcomeValue outcome, outcome))
        <$> enumerateOutcomeIndex (staticOutcomes static)

groupOutcomes :: (Ord key) => [(key, Outcome value)] -> Map.Map key [Outcome value]
groupOutcomes = Map.fromListWith (<>) . map (fmap pure)

joinOutcomeIndex ::
    Static left ->
    Static right ->
    [JoinGroup left right] ->
    Either ECTAGenError (OutcomeIndex (left, right))
joinOutcomeIndex left right groups = do
    rankSampler <- case uniformMass of
        Just _ -> pure $ uniformSampler totalOutcomes selectValue
        Nothing -> joinSampler groups
    pure $
        OutcomeIndex
            totalOutcomes
            uniformMass
            select
            selectValue
            rankSampler
  where
    totalOutcomes = sum $ map joinGroupCardinality groups
    uniformMass = case (outcomeUniformMass $ staticOutcomes left, outcomeUniformMass $ staticOutcomes right) of
        (Just _, Just _) -> Just $ 1 / fromInteger totalOutcomes
        _ -> Nothing
    totalMass = sum $ map joinGroupMass groups

    select index = do
        checkIndex totalOutcomes index
        let (group, leftOutcome, rightOutcome) = selectPair index
            keyTerm = Term (keySymbol $ joinGroupIndex group) []
            leftTerm =
                Term leftKeyedSymbol [keyTerm, outcomeTerm leftOutcome]
            rightTerm =
                Term rightKeyedSymbol [keyTerm, outcomeTerm rightOutcome]
        pure $
            Outcome
                (Term joinSymbol [leftTerm, rightTerm])
                ( outcomeMass leftOutcome
                    * outcomeMass rightOutcome
                    / totalMass
                )
                (outcomeValue leftOutcome, outcomeValue rightOutcome)

    selectValue index =
        let (_, leftOutcome, rightOutcome) = selectPair index
         in (outcomeValue leftOutcome, outcomeValue rightOutcome)

    selectPair index =
        let (group, groupIndex) = selectJoinGroup index groups
            rightCardinality = toInteger $ Sequence.length $ joinGroupRight group
            (leftIndex, rightIndex) = groupIndex `quotRem` rightCardinality
            leftOutcome = Sequence.index (joinGroupLeft group) $ fromInteger leftIndex
            rightOutcome = Sequence.index (joinGroupRight group) $ fromInteger rightIndex
         in (group, leftOutcome, rightOutcome)

joinGroupCardinality :: JoinGroup left right -> Integer
joinGroupCardinality group =
    toInteger (Sequence.length $ joinGroupLeft group)
        * toInteger (Sequence.length $ joinGroupRight group)

joinGroupMass :: JoinGroup left right -> Rational
joinGroupMass group =
    sum (outcomeMass <$> joinGroupLeft group)
        * sum (outcomeMass <$> joinGroupRight group)

selectJoinGroup ::
    Integer ->
    [JoinGroup left right] ->
    (JoinGroup left right, Integer)
selectJoinGroup _ [] = error "selectJoinGroup: rank outside groups"
selectJoinGroup index (group : remaining)
    | index < groupSize = (group, index)
    | otherwise = selectJoinGroup (index - groupSize) remaining
  where
    groupSize = joinGroupCardinality group

joinSampler ::
    [JoinGroup left right] ->
    Either ECTAGenError (Sampler (left, right))
joinSampler groups = do
    weightedGroups <-
        integerOutcomes
            [ (joinGroupMass group, (offset, group))
            | (offset, group) <- offsetJoinGroups groups
            ]
    plans <- traverse branchPlan weightedGroups
    pure $
        Sampler
            ( frequencyGen
                [ ( weight
                  , liftA2
                        (,)
                        (runValueSampler leftSampler)
                        (runValueSampler rightSampler)
                  )
                | (weight, _, _, leftSampler, rightSampler) <- plans
                ]
            )
            ( frequencyGen
                [ ( weight
                  , liftA2
                        ( \(leftIndex, leftValue) (rightIndex, rightValue) ->
                            ( offset + leftIndex * rightCardinality + rightIndex
                            , (leftValue, rightValue)
                            )
                        )
                        (runRankSampler leftSampler)
                        (runRankSampler rightSampler)
                  )
                | (weight, offset, rightCardinality, leftSampler, rightSampler) <- plans
                ]
            )
  where
    branchPlan (weight, (offset, group)) = do
        leftSampler <- sequenceSampler $ joinGroupLeft group
        rightSampler <- sequenceSampler $ joinGroupRight group
        let rightCardinality = toInteger $ Sequence.length $ joinGroupRight group
        pure (weight, offset, rightCardinality, leftSampler, rightSampler)

offsetJoinGroups :: [JoinGroup left right] -> [(Integer, JoinGroup left right)]
offsetJoinGroups = go 0
  where
    go _ [] = []
    go offset (group : remaining) =
        (offset, group) : go (offset + joinGroupCardinality group) remaining

mergeKeyedBuckets :: Map.Map key (KeyedBucket a) -> Either ECTAGenError (Static a)
mergeKeyedBuckets buckets = do
    weightedBuckets <-
        integerOutcomes
            [ (keyedBucketMass bucket, keyedBucketStatic bucket)
            | bucket <- Map.elems buckets
            ]
    pure $ frequencyStatic weightedBuckets

mergeBucketGroup :: [(Rational, Static a)] -> Either ECTAGenError (KeyedBucket a)
mergeBucketGroup alternatives = do
    weightedAlternatives <- integerOutcomes alternatives
    pure $
        KeyedBucket
            (sum $ map fst alternatives)
            (frequencyStatic weightedAlternatives)

-- | Merge weighted joined components into normalized result-key groups.
mergeComponentsByKey ::
    (Ord resultKey) =>
    [(resultKey, Rational, Static a)] ->
    Either ECTAGenError (Map.Map resultKey (KeyedBucket a))
mergeComponentsByKey [] = Left EmptyGenerator
mergeComponentsByKey components = do
    unnormalized <- traverse mergeBucketGroup grouped
    let totalAcceptedMass = sum $ keyedBucketMass <$> unnormalized
    pure $ fmap (normalizeBucket totalAcceptedMass) unnormalized
  where
    grouped =
        foldl'
            ( \groups (resultKey, mass, static) ->
                Map.insertWith
                    (flip (<>))
                    resultKey
                    [(mass, static)]
                    groups
            )
            Map.empty
            components

    normalizeBucket totalAcceptedMass bucket =
        bucket
            { keyedBucketMass =
                keyedBucketMass bucket / totalAcceptedMass
            }

joinNBucketStatic ::
    Int ->
    Static operation ->
    ArgStatics operation result ->
    Either ECTAGenError (Static result)
joinNBucketStatic componentIndex operation arguments =
    if joined == EmptyNode
        then Left EmptyGenerator
        else
            Right $
                Static
                    joined
                    ( OutcomeIndex
                        totalOutcomes
                        uniformMass
                        select
                        selectValue
                        rankSampler
                    )
  where
    keyTerms =
        [ Term (argKeySymbol componentIndex position) []
        | position <- [0 .. chainLength arguments - 1]
        ]
    keyNodes = map singletonNode keyTerms
    operationNode =
        Node
            [ Edge
                centerKeyedSymbol
                (keyNodes <> [staticSupport operation])
            ]
    argumentNodes =
        [ Node [Edge argKeyedSymbol [argKeyNode, support]]
        | (argKeyNode, support) <- zip keyNodes (chainSupports arguments)
        ]
    joined =
        reducePartially $
            Node
                [ mkEdge
                    joinNSymbol
                    (operationNode : argumentNodes)
                    ( mkEqConstraints
                        [ [path [0, position], path [position + 1, 0]]
                        | position <- [0 .. chainLength arguments - 1]
                        ]
                    )
                ]
    operationOutcomes = staticOutcomes operation
    argumentsCardinality = chainCardinality arguments
    totalOutcomes = outcomeCardinality operationOutcomes * argumentsCardinality
    uniformMass =
        (*)
            <$> outcomeUniformMass operationOutcomes
            <*> chainUniformMass arguments
    rankSampler = chainSampler (outcomeSampler operationOutcomes) arguments
    decodeArguments = chainDecoder arguments

    select index = do
        checkIndex totalOutcomes index
        let (operationIndex, argumentIndex) = index `quotRem` argumentsCardinality
        operationOutcome <- outcomeSelect operationOutcomes operationIndex
        (argumentTerms, argumentsMass, value) <-
            selectChain (outcomeValue operationOutcome) arguments keyTerms argumentIndex
        let operationTerm =
                Term centerKeyedSymbol (keyTerms <> [outcomeTerm operationOutcome])
        pure $
            Outcome
                (Term joinNSymbol (operationTerm : argumentTerms))
                (outcomeMass operationOutcome * argumentsMass)
                value

    selectValue index =
        let (operationIndex, argumentIndex) = index `quotRem` argumentsCardinality
         in decodeArguments (outcomeValueAt operationOutcomes operationIndex) argumentIndex

chainLength :: ArgStatics operation result -> Int
chainLength StaticsNil = 0
chainLength (StaticsCons _ rest) = 1 + chainLength rest

chainSupports :: ArgStatics operation result -> [Node]
chainSupports StaticsNil = []
chainSupports (StaticsCons static rest) = staticSupport static : chainSupports rest

chainCardinality :: ArgStatics operation result -> Integer
chainCardinality StaticsNil = 1
chainCardinality (StaticsCons static rest) =
    outcomeCardinality (staticOutcomes static) * chainCardinality rest

chainUniformMass :: ArgStatics operation result -> Maybe Rational
chainUniformMass StaticsNil = Just 1
chainUniformMass (StaticsCons static rest) =
    (*)
        <$> outcomeUniformMass (staticOutcomes static)
        <*> chainUniformMass rest

{- | Compose the mixed-radix rank sampler as a left 'productSampler' fold.

The composed rank is @operationRank@ most significant, then argument ranks
left to right, matching 'chainDecoder'.
-}
chainSampler :: Sampler operation -> ArgStatics operation result -> Sampler result
chainSampler sampler StaticsNil = sampler
chainSampler sampler (StaticsCons static rest) =
    chainSampler
        ( productSampler
            (outcomeCardinality $ staticOutcomes static)
            sampler
            (outcomeSampler $ staticOutcomes static)
        )
        rest

-- | Build a rank decoder once, capturing every suffix cardinality.
chainDecoder :: ArgStatics operation result -> operation -> Integer -> result
chainDecoder StaticsNil = \value _ -> value
chainDecoder (StaticsCons static rest) =
    let decodeRest = chainDecoder rest
        suffixCardinality = chainCardinality rest
        valueAt = outcomeValueAt $ staticOutcomes static
     in \apply index ->
            let (here, there) = index `quotRem` suffixCardinality
             in decodeRest (apply $ valueAt here) there

selectChain ::
    operation ->
    ArgStatics operation result ->
    [Term] ->
    Integer ->
    Either ECTAGenError ([Term], Rational, result)
selectChain value StaticsNil _ _ = Right ([], 1, value)
selectChain apply (StaticsCons static rest) (keyTerm : keyTerms) index = do
    let (here, there) = index `quotRem` chainCardinality rest
    outcome <- outcomeSelect (staticOutcomes static) here
    (terms, mass, value) <- selectChain (apply $ outcomeValue outcome) rest keyTerms there
    pure
        ( Term argKeyedSymbol [keyTerm, outcomeTerm outcome] : terms
        , outcomeMass outcome * mass
        , value
        )
selectChain _ (StaticsCons _ _) [] _ = error "selectChain: missing key terms"

sequenceSampler :: Seq (Outcome a) -> Either ECTAGenError (Sampler a)
sequenceSampler outcomes
    | Just _ <- commonValue $ Just . outcomeMass <$> toList outcomes =
        pure $ uniformSampler totalOutcomes selectValue
    | otherwise = do
        weightedRanks <-
            integerOutcomes
                [ (outcomeMass outcome, (index, outcomeValue outcome))
                | (index, outcome) <- zip [0 ..] $ toList outcomes
                ]
        pure $
            Sampler
                (frequencyGen [(weight, pure value) | (weight, (_, value)) <- weightedRanks])
                (frequencyGen [(weight, pure rankedValue) | (weight, rankedValue) <- weightedRanks])
  where
    totalOutcomes = toInteger $ Sequence.length outcomes
    selectValue = outcomeValue . Sequence.index outcomes . fromInteger

keyNode :: Int -> Node
keyNode index = Node [Edge (keySymbol index) []]

singletonNode :: Term -> Node
singletonNode (Term symbol children) =
    Node [Edge symbol $ map singletonNode children]

compileOutcomes :: Static a -> Either ECTAGenError [(Rational, a)]
compileOutcomes static = do
    outcomes <- enumerateOutcomeIndex $ staticOutcomes static
    normalize [(outcomeMass outcome, outcomeValue outcome) | outcome <- outcomes]

sampleStatic ::
    (GenBackend gen) =>
    Static a ->
    gen (Either ECTAGenError a)
sampleStatic static =
    Right <$> runValueSampler (outcomeSampler $ staticOutcomes static)

sampleStaticWithRank ::
    (GenBackend gen) =>
    Static a ->
    gen (Either ECTAGenError (Integer, a))
sampleStaticWithRank static =
    Right <$> runRankSampler (outcomeSampler $ staticOutcomes static)

uniformSampler :: Integer -> (Integer -> a) -> Sampler a
uniformSampler 1 valueAt = Sampler (pure $ valueAt 0) (pure (0, valueAt 0))
uniformSampler totalOutcomes valueAt =
    Sampler
        (valueAt <$> selectInteger totalOutcomes)
        ((\index -> (index, valueAt index)) <$> selectInteger totalOutcomes)

productSampler :: Integer -> Sampler (a -> b) -> Sampler a -> Sampler b
productSampler rightCardinality leftSampler rightSampler =
    Sampler
        (runValueSampler leftSampler <*> runValueSampler rightSampler)
        ( liftA2
            ( \(leftIndex, apply) (rightIndex, value) ->
                (leftIndex * rightCardinality + rightIndex, apply value)
            )
            (runRankSampler leftSampler)
            (runRankSampler rightSampler)
        )

frequencySampler :: [(Integer, Static a)] -> Sampler a
frequencySampler alternatives =
    Sampler
        ( frequencyGen
            [ (weight, runValueSampler $ outcomeSampler $ staticOutcomes static)
            | (weight, static) <- alternatives
            ]
        )
        ( frequencyGen
            [ ( weight
              , (\(rank, value) -> (offset + rank, value))
                    <$> runRankSampler (outcomeSampler $ staticOutcomes static)
              )
            | (offset, (weight, static)) <- offsetAlternatives alternatives
            ]
        )

offsetAlternatives :: [(Integer, Static a)] -> [(Integer, (Integer, Static a))]
offsetAlternatives = go 0
  where
    go _ [] = []
    go offset (alternative@(_, static) : remaining) =
        (offset, alternative)
            : go
                (offset + outcomeCardinality (staticOutcomes static))
                remaining

mapOutcomeIndex :: (a -> b) -> OutcomeIndex a -> OutcomeIndex b
mapOutcomeIndex transform outcomes =
    OutcomeIndex
        (outcomeCardinality outcomes)
        (outcomeUniformMass outcomes)
        (\index -> mapOutcome transform <$> outcomeSelect outcomes index)
        (transform . outcomeValueAt outcomes)
        ( Sampler
            (transform <$> runValueSampler (outcomeSampler outcomes))
            ( (\(rank, value) -> (rank, transform value))
                <$> runRankSampler (outcomeSampler outcomes)
            )
        )

mapOutcome :: (a -> b) -> Outcome a -> Outcome b
mapOutcome transform outcome =
    Outcome
        (outcomeTerm outcome)
        (outcomeMass outcome)
        (transform $ outcomeValue outcome)

enumerateOutcomeIndex :: OutcomeIndex a -> Either ECTAGenError [Outcome a]
enumerateOutcomeIndex outcomes =
    traverse
        (outcomeSelect outcomes)
        [0 .. outcomeCardinality outcomes - 1]

commonValue :: (Eq a) => [Maybe a] -> Maybe a
commonValue [] = Nothing
commonValue (Just value : remaining)
    | all (== Just value) remaining = Just value
commonValue _ = Nothing

checkIndex :: Integer -> Integer -> Either ECTAGenError ()
checkIndex totalOutcomes index
    | index < 0 || index >= totalOutcomes =
        Left $ SelectionOutOfRange index totalOutcomes
    | otherwise = Right ()

normalize :: [(Rational, a)] -> Either ECTAGenError [(Rational, a)]
normalize [] = Left EmptyGenerator
normalize outcomes =
    let total = sum $ map fst outcomes
     in if total <= 0
            then Left EmptyGenerator
            else Right [(mass / total, value) | (mass, value) <- outcomes]

integerOutcomes ::
    [(Rational, a)] ->
    Either ECTAGenError [(Integer, a)]
integerOutcomes [] = Left EmptyGenerator
integerOutcomes outcomes =
    let masses = map fst outcomes
        commonDenominator = foldl lcm 1 $ map denominator masses
        unscaled =
            [ numerator mass * (commonDenominator `div` denominator mass)
            | mass <- masses
            ]
        commonFactor = foldl gcd 0 unscaled
     in if any (<= 0) unscaled
            then Left EmptyGenerator
            else
                Right $
                    zip
                        (map (`div` commonFactor) unscaled)
                        (map snd outcomes)

atIndex :: String -> Integer -> [a] -> a
atIndex label index values
    | index < 0 = error $ label <> ": negative index"
    | otherwise = case drop (fromInteger index) values of
        value : _ -> value
        [] -> error $ label <> ": index out of range"

pureSymbol, applySymbol, joinSymbol, joinNSymbol, centerKeyedSymbol, leftKeyedSymbol, rightKeyedSymbol, argKeyedSymbol :: Symbol
pureSymbol = "$ecta-gen/pure"
applySymbol = "$ecta-gen/apply"
joinSymbol = "$ecta-gen/join"
centerKeyedSymbol = "$ecta-gen/center-keyed"
leftKeyedSymbol = "$ecta-gen/left-keyed"
rightKeyedSymbol = "$ecta-gen/right-keyed"
joinNSymbol = "$ecta-gen/join-n"
argKeyedSymbol = "$ecta-gen/arg-keyed"

indexedSymbol :: Integer -> Symbol
indexedSymbol index = Symbol $ Text.pack $ "$ecta-gen/index/" <> show index

frequencySymbol :: Int -> Symbol
frequencySymbol index = Symbol $ Text.pack $ "$ecta-gen/frequency/" <> show index

keySymbol :: Int -> Symbol
keySymbol index = Symbol $ Text.pack $ "$ecta-gen/key/" <> show index

argKeySymbol :: Int -> Int -> Symbol
argKeySymbol componentIndex position =
    Symbol $
        Text.pack $
            "$ecta-gen/key/" <> show componentIndex <> "/" <> show position
