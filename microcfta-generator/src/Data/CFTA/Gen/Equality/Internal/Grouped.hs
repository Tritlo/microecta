{- | The grouped layer: generators whose members carry a projected key.

A group keeps its own compact support and indexed selection, so joining,
merging, and counting groups never enumerates their members. The key itself is
not part of a generated value; it decides which groups a join relates.
-}
module Data.CFTA.Gen.Equality.Internal.Grouped (
    -- * Entering and leaving the layer
    keyed,
    groupBy,
    regroupBy,
    mapWithKey,
    nameGroups,
    atKey,
    ungroup,

    -- * Composing groups
    apply,
    frequencies,
    oneofGrouped,
    uniformlyGrouped,

    -- * Relating groups
    relateGroupsM,
    relateN,
    filterGroupsM,

    -- * Inspection
    sizes,
    countsAtSize,
    massesAtSize,
) where

import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Data.Typeable (Typeable)

import Data.CFTA.Gen.Equality.Internal.Bucket
import Data.CFTA.Gen.Equality.Internal.Chain
import Data.CFTA.Gen.Equality.Internal.Inspection
import Data.CFTA.Gen.Equality.Internal.Join
import Data.CFTA.Gen.Equality.Internal.Recursive
import Data.CFTA.Gen.Equality.Internal.Static
import Data.CFTA.Gen.Equality.Internal.Types
import Data.CFTA.Gen.Equality.Sig (Sig, sigResult)
import Data.CFTA.Gen.Error
import Data.CFTA.Ranked.Internal.Sampler
import Data.CFTA.Ranked.Internal.Shrink (planMemberSize)
import Data.CFTA.Ranked.Internal.Size (mapIndex)
import qualified Data.CFTA.Ranked.Internal.Size as Size

-- | Declare that every member of an inspectable generator has one key.
keyed :: key -> Gen symbol a -> Grouped symbol key a
keyed key (Transparent result) =
    Grouped $ fmap (Map.singleton key . KeyedBucket 1) result
keyed key (Cyclic result) =
    CyclicGrouped $ fmap (Map.singleton key . keyedRecursive) result
keyed _ (Opaque _) = Grouped $ Left CannotInspectOpaqueGenerator

-- | Classify a transparent generator's outcomes by a projected key.
groupBy :: (Ord key, Hashable symbol, Typeable symbol) => (a -> key) -> Gen symbol a -> Grouped symbol key a
groupBy _ (Transparent (Left err)) = Grouped $ Left err
groupBy key (Transparent (Right static)) =
    Grouped $ do
        outcomes <- enumerateOutcomeIndex $ staticOutcomes static
        traverse (bucketFromOutcomes $ staticAtomic static) $
            groupOutcomes
                [ (key $ outcomeValue outcome, outcome)
                | outcome <- outcomes
                ]
groupBy _ (Cyclic _) = Grouped $ Left UnboundedGenerator
groupBy _ (Opaque _) = Grouped $ Left CannotInspectOpaqueGenerator

-- | Reclassify the groups without enumerating their values.
regroupBy ::
    (Ord newKey, Hashable symbol, Typeable symbol) =>
    (oldKey -> newKey) -> Grouped symbol oldKey a -> Grouped symbol newKey a
regroupBy regroup (CyclicGrouped result) =
    CyclicGrouped $ do
        groups <- result
        pure
            $ Map.map clearRecursiveName
            $ Map.mapMaybe mergeRecursiveGroups
            $ Map.foldlWithKey'
                ( \regrouped oldKey group ->
                    Map.insertWith (flip (<>)) (regroup oldKey) [group] regrouped
                )
                Map.empty
                groups
  where
    clearRecursiveName group = group{keyedRecursiveLanguage = named}
      where
        recursive = keyedRecursiveLanguage group
        named = recursive{recursiveInspection = (recursiveInspection recursive){inspectionName = Nothing}}
regroupBy _ (Grouped (Left err)) = Grouped $ Left err
regroupBy regroup (Grouped (Right buckets)) =
    Grouped $ fmap (fmap clearName) $ traverse mergeBucketGroup grouped
  where
    clearName bucket = bucket{keyedBucketStatic = named}
      where
        static = keyedBucketStatic bucket
        named = static{staticInspection = (staticInspection static){inspectionName = Nothing}}
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
mapWithKey :: (key -> a -> b) -> Grouped symbol key a -> Grouped symbol key b
mapWithKey transform (CyclicGrouped result) =
    CyclicGrouped $ fmap (Map.mapWithKey mapGroup) result
  where
    mapGroup key group =
        KeyedRecursive
            ( Recursive
                (recursiveSupport recursive)
                (mapIndex (transform key) $ recursiveIndex recursive)
                (mapSampleIndex (transform key) $ recursiveSampling recursive)
                (recursiveWeighted recursive)
                (recursiveOccurrence recursive)
                Nothing
                (recursiveInspection recursive)
            )
            (keyedRecursiveMasses group)
            (keyedRecursiveMassWeighted group)
      where
        recursive = keyedRecursiveLanguage group
mapWithKey transform (Grouped result) =
    Grouped $ fmap (Map.mapWithKey mapBucket) result
  where
    mapBucket key bucket =
        KeyedBucket
            (keyedBucketMass bucket)
            (mapStatic (transform key) $ keyedBucketStatic bucket)

-- | Retain a display name for each group without inspecting its members.
nameGroups :: (key -> Text) -> Grouped symbol key a -> Grouped symbol key a
nameGroups render (Grouped result) = Grouped $ fmap (Map.mapWithKey nameBucket) result
  where
    nameBucket key bucket = bucket{keyedBucketStatic = named}
      where
        static = keyedBucketStatic bucket
        named = static{staticInspection = (staticInspection static){inspectionName = Just $ render key}}
nameGroups render (CyclicGrouped result) = CyclicGrouped $ fmap (Map.mapWithKey nameGroup) result
  where
    nameGroup key group = group{keyedRecursiveLanguage = named}
      where
        recursive = keyedRecursiveLanguage group
        named = recursive{recursiveInspection = (recursiveInspection recursive){inspectionName = Just $ render key}}

-- | Select one retained group as an ordinary conditional generator.
atKey :: (Ord key) => key -> Grouped symbol key a -> Gen symbol a
atKey key (CyclicGrouped result) =
    Cyclic $ do
        groups <- result
        maybe
            (Left EmptyGenerator)
            (Right . keyedRecursiveLanguage)
            (Map.lookup key groups)
atKey _ (Grouped (Left err)) = Transparent $ Left err
atKey key (Grouped (Right buckets)) =
    Transparent $
        maybe
            (Left EmptyGenerator)
            (Right . keyedBucketStatic)
            (Map.lookup key buckets)

-- | Merge all retained groups while preserving their probability masses.
ungroup :: (Hashable symbol, Typeable symbol) => Grouped symbol key a -> Gen symbol a
ungroup = atKey () . regroupBy (const ())

-- | Apply a generated operation of any arity to one argument family per signature component, retaining the operation's result group.
apply ::
    (Ord resultKey, Hashable symbol, Typeable symbol) =>
    Grouped symbol (Sig argKeys resultKey) operation ->
    Args symbol argKeys operation result ->
    Grouped symbol resultKey result
-- Which components an application has is decided by the operation signatures,
-- so the operation family has to be finite; only arguments may recurse.
apply (CyclicGrouped _) _ = Grouped $ Left RecursiveOperationFamily
apply (Grouped (Left err)) _ = Grouped $ Left err
apply (Grouped (Right operations)) arguments
    | anyRecursiveArgument arguments = applyRecursive operations arguments
    | otherwise = Grouped $ do
        argumentMaps <- argsMaps arguments
        let matchingBuckets =
                [ (componentIndex, resultKey, operationBucket, mass, argumentBuckets)
                | (componentIndex, (signature, operationBucket)) <-
                    zip [0 :: Int ..] $ Map.toAscList operations
                , let resultKey = sigResult signature
                , Just argumentBuckets <- [lookupArgs signature argumentMaps]
                , let mass = chainMass argumentBuckets
                ]
        mergeComponentsByKey $ map buildComponent matchingBuckets
  where
    buildComponent (componentIndex, resultKey, operationBucket, argumentsMass, argumentBuckets) =
        ( resultKey
        , keyedBucketMass operationBucket * argumentsMass
        , joinNBucketStatic
            componentIndex
            (keyedBucketStatic operationBucket)
            (mapChain keyedBucketStatic argumentBuckets)
        )

argsMaps ::
    Args symbol argKeys operation result -> Either GenError (ArgMaps (KeyedBucket symbol) argKeys operation result)
argsMaps ANil = Right MapsNil
argsMaps (Grouped family :& rest) = MapsCons <$> family <*> argsMaps rest
argsMaps (CyclicGrouped _ :& _) = Left UnboundedGenerator

{- | Apply an operation family to argument families of which at least one is
recursive.

The operation family stays finite — its signatures are what decide which
components exist — and each component becomes one joined edge over the
argument families' recursive supports, counted as the operation choice
followed by its arguments. Ranks and sizes match the finite join.
-}
applyRecursive ::
    (Ord resultKey, Hashable symbol, Typeable symbol) =>
    Map.Map (Sig argKeys resultKey) (KeyedBucket symbol operation) ->
    Args symbol argKeys operation result ->
    Grouped symbol resultKey result
applyRecursive operationBuckets arguments =
    CyclicGrouped $ do
        argumentMaps <- argsRecursiveMaps arguments
        let operationGroups = keyedRecursiveFromBuckets operationBuckets
        let components =
                [ (sigResult signature, recursiveJoin componentIndex operationGroup argumentGroups)
                | (componentIndex, (signature, operationGroup)) <-
                    zip [0 ..] $ Map.toAscList operationGroups
                , Just argumentGroups <- [lookupArgs signature argumentMaps]
                ]
        -- No matching component is an empty family, not an error: while the
        -- key set of a recursive family is still being solved, every
        -- application starts out with nothing to match.
        Right $ mergeByKey components

-- | The recursive view of every argument family, in signature order.
argsRecursiveMaps ::
    Args symbol argKeys operation result ->
    Either GenError (ArgMaps (KeyedRecursive symbol) argKeys operation result)
argsRecursiveMaps ANil = Right MapsNil
argsRecursiveMaps (family :& rest) =
    MapsCons <$> recursiveGroups family <*> argsRecursiveMaps rest

-- | Whether any argument family is recursive.
anyRecursiveArgument :: Args symbol argKeys operation result -> Bool
anyRecursiveArgument ANil = False
anyRecursiveArgument (family :& rest) =
    isRecursiveGrouped family || anyRecursiveArgument rest

-- | Collect keyed recursive languages into one alternative per key, in order.
mergeByKey ::
    (Ord key, Hashable symbol, Typeable symbol) => [(key, KeyedRecursive symbol a)] -> Map.Map key (KeyedRecursive symbol a)
mergeByKey entries =
    Map.mapMaybe mergeRecursiveGroups $
        foldl'
            (\groups (key, group) -> Map.insertWith (flip (<>)) key [group] groups)
            Map.empty
            entries

-- | Choose among grouped generators with positive relative weights, group by group.
frequencies ::
    (Ord key, Hashable symbol, Typeable symbol) =>
    [(Integer, Grouped symbol key a)] ->
    Grouped symbol key a
frequencies [] = Grouped $ Left EmptyGenerator
frequencies alternatives
    | Just badWeight <- firstNonPositiveWeight alternatives =
        Grouped $ Left $ NonPositiveWeight badWeight
    | Just err <- firstError alternatives = Grouped $ Left err
    | any (isRecursiveGrouped . snd) alternatives =
        CyclicGrouped $
            if allWeightsEqual alternatives
                then
                    mergeByKey
                        . concatMap Map.toAscList
                        <$> traverse (recursiveGroups . snd) alternatives
                else Left WeightedRecursiveAlternatives
    | otherwise = Grouped $ traverse mergeBucketGroup grouped
  where
    totalWeight = sum $ map fst alternatives

    firstError = go
      where
        go [] = Nothing
        go ((_, Grouped (Left err)) : _) = Just err
        go ((_, CyclicGrouped (Left err)) : _) = Just err
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

-- | Choose uniformly among grouped generators, group by group.
oneofGrouped :: (Ord key, Hashable symbol, Typeable symbol) => [Grouped symbol key a] -> Grouped symbol key a
oneofGrouped alternatives = frequencies [(1, alternative) | alternative <- alternatives]

-- | Choose among grouped generators so that every member of the combined language is equally likely.
uniformlyGrouped :: (Ord key, Hashable symbol, Typeable symbol) => [Grouped symbol key a] -> Grouped symbol key a
uniformlyGrouped alternatives
    | any isRecursiveGrouped alternatives = oneofGrouped alternatives
    | otherwise = case traverse liveCardinality alternatives of
        Left err -> Grouped $ Left err
        Right counts ->
            frequencies
                [ (count, alternative)
                | (Just count, alternative) <- zip counts alternatives
                ]
  where
    liveCardinality alternative = case sizes alternative of
        Left EmptyGenerator -> Right Nothing
        Left err -> Left err
        Right groups ->
            let total = sum groups
             in Right $ if total > 0 then Just total else Nothing

-- | Compile an effectful relation directly over two grouped languages.
relateGroupsM ::
    (Ord resultKey, Hashable symbol, Typeable symbol) =>
    (leftKey -> rightKey -> IO (Either relationError Bool)) ->
    (leftKey -> rightKey -> resultKey) ->
    Grouped symbol leftKey left ->
    Grouped symbol rightKey right ->
    IO (Either relationError (Grouped symbol resultKey (left, right)))
relateGroupsM relation resultKey left right =
    case (left, right) of
        (Grouped (Left err), _) -> pure $ Right $ Grouped $ Left err
        (_, Grouped (Left err)) -> pure $ Right $ Grouped $ Left err
        (CyclicGrouped _, _) -> pure $ Right $ Grouped $ Left UnboundedGenerator
        (_, CyclicGrouped _) -> pure $ Right $ Grouped $ Left UnboundedGenerator
        (Grouped (Right leftBuckets), Grouped (Right rightBuckets)) -> do
            related <- decidePairs 0 [] $ Map.toAscList leftBuckets
            pure $ fmap (Grouped . mergeComponentsByKey . reverse) related
          where
            rightEntries = Map.toAscList rightBuckets

            decidePairs _ accepted [] = pure $ Right accepted
            decidePairs componentIndex accepted ((leftGroupKey, leftBucket) : rest) = do
                decided <- decideRights componentIndex accepted leftGroupKey leftBucket rightEntries
                case decided of
                    Left err -> pure $ Left err
                    Right (nextIndex, retained) -> decidePairs nextIndex retained rest

            decideRights componentIndex accepted _ _ [] =
                pure $ Right (componentIndex, accepted)
            decideRights componentIndex accepted leftGroupKey leftBucket ((rightGroupKey, rightBucket) : rest) = do
                decision <- relation leftGroupKey rightGroupKey
                case decision of
                    Left err -> pure $ Left err
                    Right keep ->
                        let retained =
                                if keep
                                    then
                                        ( resultKey leftGroupKey rightGroupKey
                                        , keyedBucketMass leftBucket * keyedBucketMass rightBucket
                                        , joinNBucketStatic
                                            componentIndex
                                            (pureStatic (,))
                                            ( ChainCons
                                                (keyedBucketStatic leftBucket)
                                                (ChainCons (keyedBucketStatic rightBucket) ChainNil)
                                            )
                                        )
                                            : accepted
                                    else accepted
                            nextIndex = if keep then componentIndex + 1 else componentIndex
                         in decideRights nextIndex retained leftGroupKey leftBucket rest

-- | Compile one relation over a homogeneous list of grouped arguments.
relateN ::
    (Ord key, Hashable symbol, Typeable symbol) =>
    ([key] -> IO (Either relationError Bool)) ->
    [Grouped symbol key a] ->
    IO (Either relationError (Grouped symbol [key] [a]))
relateN _ [] = pure $ Right $ Grouped $ Left EmptyGenerator
relateN relation (first : rest) = do
    combined <- combine (regroupBy pure $ mapWithKey (\_ value -> [value]) first) rest
    case combined of
        Left err -> pure $ Left err
        Right grouped -> filterGroupsM relation grouped
  where
    combine grouped [] = pure $ Right grouped
    combine grouped (next : remaining) = do
        paired <-
            relateGroupsM
                (\_ _ -> pure $ Right True)
                (\keys key -> keys <> [key])
                grouped
                next
        case paired of
            Left err -> pure $ Left err
            Right joined ->
                combine
                    (mapWithKey (\_ (values, value) -> values <> [value]) joined)
                    remaining

-- | Retain complete groups selected by one effectful key predicate.
filterGroupsM ::
    (Ord key, Hashable symbol, Typeable symbol) =>
    (key -> IO (Either relationError Bool)) ->
    Grouped symbol key a ->
    IO (Either relationError (Grouped symbol key a))
filterGroupsM _ (Grouped (Left err)) = pure $ Right $ Grouped $ Left err
filterGroupsM _ (CyclicGrouped _) = pure $ Right $ Grouped $ Left UnboundedGenerator
filterGroupsM predicate (Grouped (Right buckets)) = do
    retained <- go [] $ Map.toAscList buckets
    pure $ fmap (Grouped . mergeComponentsByKey . reverse) retained
  where
    go accepted [] = pure $ Right accepted
    go accepted ((key, bucket) : rest) = do
        decision <- predicate key
        case decision of
            Left err -> pure $ Left err
            Right keep ->
                go
                    ( if keep
                        then (key, keyedBucketMass bucket, keyedBucketStatic bucket) : accepted
                        else accepted
                    )
                    rest

-- | Return the exact cardinality of each retained group in O(number of groups).
sizes :: Grouped symbol key a -> Either GenError (Map.Map key Integer)
sizes (CyclicGrouped _) = Left UnboundedGenerator
sizes (Grouped result) =
    fmap (fmap $ outcomeCardinality . staticOutcomes . keyedBucketStatic) result

-- | Return the exact number of retained members in every live key at one structural size.
countsAtSize :: Grouped symbol key a -> Int -> Either GenError (Map.Map key Integer)
countsAtSize (CyclicGrouped result) size = do
    groups <- result
    if size < 1
        then pure Map.empty
        else
            pure
                $ Map.filter (> 0)
                $ fmap
                    ( \group ->
                        Size.countAtSize
                            (recursiveIndex $ keyedRecursiveLanguage group)
                            size
                    )
                    groups
countsAtSize (Grouped result) size = do
    buckets <- result
    if size < 1
        then pure Map.empty
        else
            pure
                $ Map.filter (> 0)
                $ fmap
                    ( \bucket ->
                        Size.countAtSize
                            (outcomeSizeIndex $ staticOutcomes $ keyedBucketStatic bucket)
                            size
                    )
                    buckets

-- | Return the exact distribution of retained keys conditional on one structural size.
massesAtSize :: Grouped symbol key a -> Int -> Either GenError (Map.Map key Rational)
massesAtSize (CyclicGrouped result) size = do
    groups <- result
    if size < 1
        then pure Map.empty
        else do
            let positive = Map.filter (> 0) $ fmap (`keyedRecursiveMassAtSize` size) groups
                total = sum positive
            pure $
                if total <= 0
                    then Map.empty
                    else fmap (/ total) positive
massesAtSize (Grouped result) size = do
    buckets <- result
    if size < 1
        then pure Map.empty
        else do
            masses <- traverse bucketMassAtSize buckets
            let positive = Map.filter (> 0) masses
                total = sum positive
            pure $
                if total <= 0
                    then Map.empty
                    else fmap (/ total) positive
  where
    bucketMassAtSize bucket = do
        let static = keyedBucketStatic bucket
            outcomes = staticOutcomes static
            plan = outcomePlan outcomes
        enumerated <- enumerateOutcomeIndex outcomes
        pure $
            keyedBucketMass bucket
                * sum
                    [ outcomeMass outcome
                    | (rank, outcome) <- zip [0 ..] enumerated
                    , planMemberSize plan rank == size
                    ]
