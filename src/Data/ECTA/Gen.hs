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
    Grouped,
    Sig (..),
    sigResult,
    Args (..),
    ECTAGenError (..),
    GenBackend (..),
    fromIndexed,
    fromBackend,
    elements,
    groupBy,
    regroupBy,
    mapWithKey,
    sizes,
    atKey,
    apply,
    frequencies,
    ungroup,
    frequency,
    On (..),
    match,
    support,
    cardinality,
    unrank,
    shrinkRank,
    smallerMembers,
    sizeOfRank,
    countBy,
    pmf,
    lower,
    lowerWithRank,
    lowerUniform,
    lowerUniformWithRank,
) where

import Data.Kind (Type)
import qualified Data.Map.Strict as Map

import Data.ECTA (Node)
import Data.ECTA.Gen.Internal
import Data.ECTA.Gen.Internal.Decoder (
    RankDecoder (..),
    planMemberSize,
    shrinkPlanRank,
    smallerPlanMembers,
 )
import Data.ECTA.Gen.Sig (On (..), Sig (..), sigResult)

{- | A transparent generator whose values are classified by a projected key.

The key is not part of the generated value. It classifies values into groups;
during a join, matching key values determine which groups receive equal internal
labels on constrained ECTA paths. Each key group retains compact ECTA support
and indexed selection without storing all outcomes.
-}
newtype Grouped (gen :: Type -> Type) key a
    = Grouped (Either ECTAGenError (Map.Map key (KeyedBucket a)))

{- | Argument families for 'apply', one per signature component, in order.

Each link requires the family key type named by the corresponding signature
component and consumes the corresponding argument of the generated operation.
-}
data Args gen (argKeys :: [Type]) operation result where
    ANil :: Args gen '[] result result
    (:&) ::
        (Ord argKey) =>
        Grouped gen argKey arg ->
        Args gen argKeys operation result ->
        Args gen (argKey ': argKeys) (arg -> operation) result

infixr 5 :&

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

instance Functor (Grouped gen key) where
    fmap transform (Grouped result) =
        Grouped $ fmap (fmap mapBucket) result
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

{- | Classify a transparent generator's outcomes by a projected key.

This is the boundary from flat to grouped generation: any transparent
generator can be grouped, including 'frequency'-weighted sources and 'match'
results. Building the groups enumerates the generator's outcomes once. Keys
are ordered by their 'Ord' instance; outcomes within each key retain their
rank order. Opaque generators cannot be grouped.
-}
groupBy :: (Ord key) => (a -> key) -> ECTAGen gen a -> Grouped gen key a
groupBy _ (Transparent (Left err)) = Grouped $ Left err
groupBy key (Transparent (Right static)) =
    Grouped $ do
        outcomes <- enumerateOutcomeIndex $ staticOutcomes static
        traverse bucketFromOutcomes $
            foldl'
                ( \buckets outcome ->
                    Map.insertWith
                        (flip (<>))
                        (key $ outcomeValue outcome)
                        [outcome]
                        buckets
                )
                Map.empty
                outcomes
groupBy _ (Opaque _) = Grouped $ Left CannotInspectOpaqueGenerator

{- | Reclassify the groups without enumerating their values.

When several old keys map to one new key, their compact supports are merged and
their probability masses are preserved.
-}
regroupBy :: (Ord newKey) => (oldKey -> newKey) -> Grouped gen oldKey a -> Grouped gen newKey a
regroupBy _ (Grouped (Left err)) = Grouped $ Left err
regroupBy regroup (Grouped (Right buckets)) =
    Grouped $ traverse mergeBucketGroup grouped
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

-- | Map group values with access to their retained key.
mapWithKey :: (key -> a -> b) -> Grouped gen key a -> Grouped gen key b
mapWithKey transform (Grouped result) =
    Grouped $ fmap (Map.mapWithKey mapBucket) result
  where
    mapBucket key bucket =
        KeyedBucket
            (keyedBucketMass bucket)
            (mapStatic (transform key) $ keyedBucketStatic bucket)

-- | Return the exact cardinality of each retained group in O(number of groups).
sizes :: Grouped gen key a -> Either ECTAGenError (Map.Map key Integer)
sizes (Grouped result) =
    fmap (fmap $ outcomeCardinality . staticOutcomes . keyedBucketStatic) result

{- | Select one retained group as an ordinary conditional generator.

A missing key produces 'EmptyGenerator'.
-}
atKey :: (Ord key) => key -> Grouped gen key a -> ECTAGen gen a
atKey _ (Grouped (Left err)) = Transparent $ Left err
atKey key (Grouped (Right buckets)) =
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
    Grouped gen (Sig argKeys resultKey) operation ->
    Args gen argKeys operation result ->
    Grouped gen resultKey result
apply (Grouped (Left err)) _ = Grouped $ Left err
apply (Grouped (Right operations)) arguments = Grouped $ do
    argumentMaps <- argsMaps arguments
    let matchingBuckets =
            [ (componentIndex, resultKey, operationBucket, mass, argumentBuckets)
            | (componentIndex, (signature, operationBucket)) <-
                zip [0 :: Int ..] $ Map.toAscList operations
            , let resultKey = sigResult signature
            , Just (mass, argumentBuckets) <- [lookupArgs signature argumentMaps]
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

argsMaps :: Args gen argKeys operation result -> Either ECTAGenError (ArgMaps argKeys operation result)
argsMaps ANil = Right MapsNil
argsMaps (Grouped family :& rest) = MapsCons <$> family <*> argsMaps rest

{- | Choose among grouped generators with positive relative weights,
group by group.

Every key present in any alternative is retained. Within one key, the group
is the weighted mixture of that key's groups across the alternatives; a key
missing from an alternative simply contributes nothing to it. Ranks within a
merged group are ordered by alternative order, then by the inner rank.
-}
frequencies ::
    (Ord key) =>
    [(Integer, Grouped gen key a)] ->
    Grouped gen key a
frequencies [] = Grouped $ Left EmptyGenerator
frequencies alternatives
    | Just badWeight <- firstNonPositive alternatives =
        Grouped $ Left $ NonPositiveWeight badWeight
    | Just err <- firstError alternatives = Grouped $ Left err
    | otherwise = Grouped $ traverse mergeBucketGroup grouped
  where
    totalWeight = sum $ map fst alternatives

    firstNonPositive = go
      where
        go [] = Nothing
        go ((weight, _) : rest)
            | weight <= 0 = Just weight
            | otherwise = go rest

    firstError = go
      where
        go [] = Nothing
        go ((_, Grouped (Left err)) : _) = Just err
        go (_ : rest) = go rest

    grouped =
        foldl'
            ( \groups (weight, buckets) ->
                Map.foldlWithKey'
                    ( \keyGroups key bucket ->
                        Map.insertWith
                            (flip (<>))
                            key
                            [
                                ( fromInteger weight
                                    / fromInteger totalWeight
                                    * keyedBucketMass bucket
                                , keyedBucketStatic bucket
                                )
                            ]
                            keyGroups
                    )
                    groups
                    buckets
            )
            Map.empty
            [(weight, buckets) | (weight, Grouped (Right buckets)) <- alternatives]

-- | Merge all retained groups while preserving their probability masses.
ungroup :: Grouped gen key a -> ECTAGen gen a
ungroup (Grouped (Left err)) = Transparent $ Left err
ungroup (Grouped (Right buckets)) =
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

{- | Structural shrink candidates for one rank of a transparent generator.

Candidates decode to values from the same language: earlier alternatives at
their minimal ranks come first, then each product component shrinks
independently. Opaque generators and out-of-range ranks have no candidates.
-}
shrinkRank :: ECTAGen gen a -> Integer -> [Integer]
shrinkRank (Transparent (Right static)) rank
    | rank > 0
    , rank < outcomeCardinality outcomes =
        shrinkPlanRank (outcomePlan outcomes) rank
  where
    outcomes = staticOutcomes static
shrinkRank _ _ = []

{- | Every member structurally smaller than the given rank's member, in size
order, as replayable rank and value.

Size is the number of source choices in a member. The stream is lazy, so cap
it before use; a smallest failing member found in it is globally minimal.
Opaque generators and out-of-range ranks have no smaller members.
-}
smallerMembers :: ECTAGen gen a -> Integer -> [(Integer, a)]
smallerMembers (Transparent (Right static)) rank
    | rank >= 0
    , rank < outcomeCardinality outcomes =
        smallerPlanMembers (outcomePlan outcomes) rank
  where
    outcomes = staticOutcomes static
smallerMembers _ _ = []

{- | The number of source choices in the member a rank decodes to.

'Nothing' for opaque generators and out-of-range ranks.
-}
sizeOfRank :: ECTAGen gen a -> Integer -> Maybe Int
sizeOfRank (Transparent (Right static)) rank
    | rank >= 0
    , rank < outcomeCardinality outcomes =
        Just $ planMemberSize (outcomePlan outcomes) rank
  where
    outcomes = staticOutcomes static
sizeOfRank _ _ = Nothing

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

{- | Lower a transparent uniform generator to a direct backend action.

The action carries no per-sample error wrapping; construction errors and the
non-uniform and opaque cases return 'Nothing' and must go through 'lower'.
-}
lowerUniform :: (GenBackend gen) => ECTAGen gen a -> Maybe (gen a)
lowerUniform (Transparent (Right static))
    | Just _ <- outcomeUniformMass outcomes =
        Just $ case compiledDecoder outcomes of
            SmallDecoder bound decode -> decode <$> selectInt bound
            LargeDecoder bound decode -> decode <$> selectInteger bound
  where
    outcomes = staticOutcomes static
lowerUniform _ = Nothing

-- | Like 'lowerUniform', retaining the sampled replay rank.
lowerUniformWithRank :: (GenBackend gen) => ECTAGen gen a -> Maybe (gen (Integer, a))
lowerUniformWithRank (Transparent (Right static))
    | Just _ <- outcomeUniformMass outcomes =
        Just $ case compiledDecoder outcomes of
            SmallDecoder bound decode ->
                (\index -> (toInteger index, decode index)) <$> selectInt bound
            LargeDecoder bound decode ->
                (\index -> (index, decode index)) <$> selectInteger bound
  where
    outcomes = staticOutcomes static
lowerUniformWithRank _ = Nothing
