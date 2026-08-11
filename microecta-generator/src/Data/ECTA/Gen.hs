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
    fromECTA,
    recur,
    recurGrouped,
    upToSize,
    isRecursive,
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
    countAtSize,
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

import Data.ECTA (Edge (Edge), Node (EmptyNode, Node), createMu)
import Data.ECTA.Gen.Internal
import Data.ECTA.Gen.Internal.Automaton (automatonIndex)
import Data.ECTA.Gen.Internal.Decoder (RankDecoder (..))
import Data.ECTA.Gen.Internal.Shrink (
    planMemberSize,
    shrinkPlanRank,
    smallerPlanMembers,
 )
import Data.ECTA.Gen.Internal.Size (
    SizeIndex (SizeIndex, sizeClassCounts, sizeClassSelect),
    choiceIndex,
    fixIndex,
    mapIndex,
    productIndex,
    sizeClassOf,
    sizeIndex,
 )
import qualified Data.ECTA.Gen.Internal.Size as Size
import Data.ECTA.Gen.Sig (On (..), Sig (..), sigResult)
import Data.ECTA.Term (Term)

{- | A transparent generator whose values are classified by a projected key.

The key is not part of the generated value. It classifies values into groups;
during a join, matching key values determine which groups receive equal internal
labels on constrained ECTA paths. Each key group retains compact ECTA support
and indexed selection without storing all outcomes.
-}
data Grouped (gen :: Type -> Type) key a
    = Grouped !(Either ECTAGenError (Map.Map key (KeyedBucket a)))
    | -- | A recursive family: one language per key, all sharing one @Mu@.
      CyclicGrouped !(Either ECTAGenError (Map.Map key (Recursive a)))

{- | View a grouped generator as a recursive family, one language per key.

A finite family is a recursive one that happens to stop, so this is how the
recursive builders accept either.
-}
recursiveGroups ::
    Grouped gen key a ->
    Either ECTAGenError (Map.Map key (Recursive a))
recursiveGroups (CyclicGrouped result) = result
recursiveGroups (Grouped result) = fmap (fmap ofBucket) result
  where
    ofBucket bucket =
        Recursive
            (staticSupport $ keyedBucketStatic bucket)
            (sizeIndex $ outcomePlan $ staticOutcomes $ keyedBucketStatic bucket)
            Nothing

-- | Whether a grouped generator stands for a recursive family.
isRecursiveGrouped :: Grouped gen key a -> Bool
isRecursiveGrouped (CyclicGrouped _) = True
isRecursiveGrouped _ = False

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

{- | A generator is inspectable ECTA structure — finite or recursive — or an
opaque backend action.
-}
data ECTAGen gen a
    = Transparent !(Either ECTAGenError (Static a))
    | Cyclic !(Either ECTAGenError (Recursive a))
    | Opaque !(gen (Either ECTAGenError a))

{- | View any inspectable generator as a recursive one.

A finite generator is a recursive language that happens to stop: its plan
already counts by size, and its support is already its automaton.
-}
recursiveView :: ECTAGen gen a -> Either ECTAGenError (Recursive a)
recursiveView (Transparent result) = do
    static <- result
    pure $
        Recursive
            (staticSupport static)
            (sizeIndex $ outcomePlan $ staticOutcomes static)
            Nothing
recursiveView (Cyclic result) = result
recursiveView (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Whether a generator stands for a recursive language.
isRecursive :: ECTAGen gen a -> Bool
isRecursive (Cyclic _) = True
isRecursive _ = False

instance Functor (Grouped gen key) where
    fmap transform (Grouped result) =
        Grouped $ fmap (fmap mapBucket) result
      where
        mapBucket bucket =
            KeyedBucket
                (keyedBucketMass bucket)
                (mapStatic transform $ keyedBucketStatic bucket)
    fmap transform (CyclicGrouped result) =
        CyclicGrouped $ fmap (fmap mapGroup) result
      where
        mapGroup group =
            Recursive
                (recursiveSupport group)
                (mapIndex transform $ recursiveIndex group)
                Nothing

instance (Functor gen) => Functor (ECTAGen gen) where
    fmap transform (Transparent result) = Transparent $ fmap (mapStatic transform) result
    fmap transform (Cyclic result) = Cyclic $ fmap mapRecursive result
      where
        mapRecursive recursive =
            Recursive
                (recursiveSupport recursive)
                (mapIndex transform $ recursiveIndex recursive)
                Nothing
    fmap transform (Opaque generated) = Opaque $ fmap (fmap transform) generated

instance (GenBackend gen) => Applicative (ECTAGen gen) where
    pure value = Transparent $ Right $ pureStatic value

    Transparent (Left err) <*> _ = Transparent $ Left err
    _ <*> Transparent (Left err) = Transparent $ Left err
    Transparent (Right functions) <*> Transparent (Right values) =
        Transparent $ Right $ applyStatic functions values
    functions <*> values
        | isRecursive functions || isRecursive values =
            Cyclic $ do
                left <- recursiveView functions
                right <- recursiveView values
                pure $
                    Recursive
                        ( Node
                            [ Edge
                                applySymbol
                                [recursiveSupport left, recursiveSupport right]
                            ]
                        )
                        (productIndex (recursiveIndex left) (recursiveIndex right))
                        Nothing
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

{- | Build a recursive generator from its own language.

The argument receives the generator being defined and returns its body, so
a language can refer to itself:

@
tree = ECTAGen.recur $ \\self ->
    ECTAGen.frequency
        [ (1, Leaf '<$>' ECTAGen.elements [0 .. 3])
        , (1, Branch '<$>' self '<*>' self)
        ]
@

The result stands for the whole unbounded language: it has size classes and
size-major ranks instead of a cardinality, and its ECTA support is a @Mu@
node. 'upToSize' bounds it back to an ordinary finite generator, and the
QuickCheck adapter does that automatically from the size parameter.

Two rules apply inside the knot. The recursion must be guarded — every
occurrence of the argument under at least one '<*>' — or the language has
no smallest member and counting it diverges, exactly as @let x = x@ does.
And a recursive language is uniform over each size class, so 'frequency'
alternatives around a recursive occurrence must carry equal weights; use
the size bound, not weights, to control how large members get.
-}
recur :: (ECTAGen gen a -> ECTAGen gen a) -> ECTAGen gen a
recur build = Cyclic result
  where
    -- The body is built three times against three placeholders: once to tie
    -- the counts, once to learn whether it is well formed, and once inside
    -- 'createMu' where the recursive node is in scope. Each is one pass over
    -- the generator definition, not over its language.
    bodyOf placeholder = recursiveView $ build placeholder

    tied = fixIndex $ \self ->
        either (const emptyIndex) recursiveIndex $
            bodyOf (Cyclic $ Right $ Recursive EmptyNode self Nothing)
    emptyIndex = SizeIndex [] $ \_ _ -> error "recur: no members"

    automaton = createMu $ \self ->
        either (const EmptyNode) recursiveSupport $
            bodyOf (Cyclic $ Right $ Recursive self tied Nothing)

    result = do
        _ <- bodyOf (Cyclic $ Right $ Recursive EmptyNode tied Nothing)
        pure $ Recursive automaton tied Nothing

{- | Read an ECTA as a generator of the terms it accepts.

The automaton is the support, unchanged, and members are counted by size —
the number of term nodes — so the generator draws uniformly from the terms
of at most a given size, recursive @Mu@ nodes included. Because the values
are the accepted terms, a bounded generator keeps full inspection: 'pmf',
'countBy', and 'groupBy' all work on it.

Equality constraints are not counted: they correlate an edge's children, so
its count is the size of an intersection rather than a product, and an
automaton carrying them is rejected with 'CannotCountConstrainedEdges'
rather than miscounted.
-}
fromECTA :: Node -> ECTAGen gen Term
fromECTA node =
    Cyclic $ do
        index <- automatonIndex node
        pure $ Recursive node index $ Just id

{- | Build a recursive grouped family from its own languages.

The argument receives the family being defined, so a keyed language can
refer to itself — which is what a recursively typed expression language
needs:

@
expressions = ECTAGen.recurGrouped $ \self ->
    ECTAGen.frequencies
        [ (1, atomsByType)
        , (1, ECTAGen.apply (compile '<$>' functionsBySignature) (self ':&' self ':&' 'ANil'))
        ]
@

Which keys the family has is itself part of the fixpoint, so it is solved
first, from the empty family upward: each pass adds the result keys of the
operations whose argument keys are already present, and the set can only
grow, so it converges in at most one pass per key. The languages are then
tied lazily over that fixed set.

All the keys share one @Mu@ node, whose edges carry their key as a first
child. An occurrence at one key is that node under an edge holding the
key's label, with an equality constraint tying the two — so a recursive
family is one recursive automaton whose cycle carries equality constraints,
and the keyed joins inside it keep the constraints they always had. The
joined edges are not reduced, since propagating constraints through a
recursive node is not sound.

'ungroup' and 'atKey' are the exits into an ordinary recursive generator.
The rules of 'recur' apply here too: the recursion must be guarded by an
'apply', and 'frequencies' alternatives around a recursive occurrence must
carry equal weights.
-}
recurGrouped ::
    (Ord key) =>
    (Grouped gen key a -> Grouped gen key a) ->
    Grouped gen key a
recurGrouped build = CyclicGrouped result
  where
    bodyGroups placeholders = recursiveGroups $ build $ CyclicGrouped $ Right placeholders

    -- The key set, from the empty family upward: monotone, so the first
    -- pass that adds nothing is the fixpoint.
    keySet = converge Map.empty
    converge current =
        let reached =
                either (const Map.empty) (fmap $ const ()) $
                    bodyGroups $
                        fmap (const emptyGroup) current
            grown = Map.union current reached
         in if Map.keys grown == Map.keys current then current else converge grown
    keys = Map.keys keySet
    positions = Map.fromList $ zip keys [0 ..]
    positionOf key = Map.findWithDefault 0 key positions
    emptyGroup = Recursive EmptyNode (choiceIndex []) Nothing

    -- The languages, tied over the settled key set. Supports are irrelevant
    -- here and are filled in against the family node below.
    indexPlaceholders =
        Map.fromList [(key, Recursive EmptyNode (indexAt key) Nothing) | key <- keys]
    tiedIndexes =
        either (const Map.empty) (fmap recursiveIndex) $ bodyGroups indexPlaceholders
    indexAt key = Map.findWithDefault (choiceIndex []) key tiedIndexes

    -- One node for the whole family: one key-labelled edge per key, and
    -- every occurrence inside restricted to its own key by a constraint.
    family = createMu $ \self ->
        let bodies = either (const Map.empty) id $ bodyGroups $ occurrences self
         in familyNode
                [ (positionOf key, maybe EmptyNode recursiveSupport $ Map.lookup key bodies)
                | key <- keys
                ]
    occurrences self =
        Map.fromList
            [ (key, Recursive (restrictToKey (positionOf key) self) (indexAt key) Nothing)
            | key <- keys
            ]

    result = do
        bodies <- bodyGroups indexPlaceholders
        pure $
            Map.fromList
                [ (key, Recursive (restrictToKey (positionOf key) family) (indexAt key) Nothing)
                | key <- keys
                , Map.member key bodies
                ]

{- | Bound a generator to the members of size at most the given bound.

Size is the number of source choices in a member. A recursive generator
becomes an ordinary finite one, uniform over exactly those members and
keeping the ranks it already had, so a rank found under one bound replays
under any larger bound and through the unbounded generator itself. A
generator that is not recursive is already finite and is returned
unchanged.
-}
upToSize :: Int -> ECTAGen gen a -> ECTAGen gen a
upToSize bound (Cyclic result) = Transparent $ result >>= boundedStatic bound
upToSize _ generator = generator

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
groupBy _ (Cyclic _) = Grouped $ Left UnboundedGenerator
groupBy _ (Opaque _) = Grouped $ Left CannotInspectOpaqueGenerator

{- | Reclassify the groups without enumerating their values.

When several old keys map to one new key, their compact supports are merged and
their probability masses are preserved.
-}
regroupBy :: (Ord newKey) => (oldKey -> newKey) -> Grouped gen oldKey a -> Grouped gen newKey a
regroupBy regroup (CyclicGrouped result) =
    CyclicGrouped $ do
        groups <- result
        pure $
            Map.mapMaybe mergeRecursiveGroups $
                Map.foldlWithKey'
                    ( \regrouped oldKey group ->
                        Map.insertWith (flip (<>)) (regroup oldKey) [group] regrouped
                    )
                    Map.empty
                    groups
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
mapWithKey transform (CyclicGrouped result) =
    CyclicGrouped $ fmap (Map.mapWithKey mapGroup) result
  where
    mapGroup key group =
        Recursive
            (recursiveSupport group)
            (mapIndex (transform key) $ recursiveIndex group)
            Nothing
mapWithKey transform (Grouped result) =
    Grouped $ fmap (Map.mapWithKey mapBucket) result
  where
    mapBucket key bucket =
        KeyedBucket
            (keyedBucketMass bucket)
            (mapStatic (transform key) $ keyedBucketStatic bucket)

-- | Return the exact cardinality of each retained group in O(number of groups).
sizes :: Grouped gen key a -> Either ECTAGenError (Map.Map key Integer)
sizes (CyclicGrouped _) = Left UnboundedGenerator
sizes (Grouped result) =
    fmap (fmap $ outcomeCardinality . staticOutcomes . keyedBucketStatic) result

{- | Select one retained group as an ordinary conditional generator.

A missing key produces 'EmptyGenerator'.
-}
atKey :: (Ord key) => key -> Grouped gen key a -> ECTAGen gen a
atKey key (CyclicGrouped result) =
    Cyclic $ do
        groups <- result
        maybe (Left EmptyGenerator) Right $ Map.lookup key groups
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
apply operations arguments
    | isRecursiveGrouped operations = Grouped $ Left UnboundedGenerator
    | anyRecursiveArgument arguments = applyRecursive operations arguments
apply (Grouped (Left err)) _ = Grouped $ Left err
apply (CyclicGrouped _) _ = Grouped $ Left UnboundedGenerator
apply (Grouped (Right operations)) arguments = Grouped $ do
    argumentMaps <- argsMaps arguments
    let matchingBuckets =
            [ (componentIndex, resultKey, operationBucket, mass, argumentBuckets)
            | (componentIndex, (signature, operationBucket)) <-
                zip [0 :: Int ..] $ Map.toAscList operations
            , let resultKey = sigResult signature
            , Just argumentBuckets <- [lookupArgs signature argumentMaps]
            , let mass = chainMass argumentBuckets
            ]
    components <- traverse buildComponent matchingBuckets
    mergeComponentsByKey components
  where
    buildComponent (componentIndex, resultKey, operationBucket, argumentsMass, argumentBuckets) = do
        joined <-
            joinNBucketStatic
                componentIndex
                (keyedBucketStatic operationBucket)
                (mapChain keyedBucketStatic argumentBuckets)
        pure
            ( resultKey
            , keyedBucketMass operationBucket * argumentsMass
            , joined
            )

argsMaps :: Args gen argKeys operation result -> Either ECTAGenError (ArgMaps KeyedBucket argKeys operation result)
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
    (Ord resultKey) =>
    Grouped gen (Sig argKeys resultKey) operation ->
    Args gen argKeys operation result ->
    Grouped gen resultKey result
applyRecursive (Grouped (Left err)) _ = CyclicGrouped $ Left err
applyRecursive (CyclicGrouped _) _ = CyclicGrouped $ Left UnboundedGenerator
applyRecursive (Grouped (Right operations)) arguments =
    CyclicGrouped $ do
        argumentMaps <- argsRecursiveMaps arguments
        let components =
                [ (sigResult signature, recursiveJoin componentIndex operationStatic argumentGroups)
                | (componentIndex, (signature, operationBucket)) <-
                    zip [0 ..] $ Map.toAscList operations
                , let operationStatic = keyedBucketStatic operationBucket
                , Just argumentGroups <- [lookupArgs signature argumentMaps]
                ]
        -- No matching component is an empty family, not an error: while the
        -- key set of a recursive family is still being solved, every
        -- application starts out with nothing to match.
        Right $ mergeByKey components

-- | The recursive view of every argument family, in signature order.
argsRecursiveMaps ::
    Args gen argKeys operation result ->
    Either ECTAGenError (ArgMaps Recursive argKeys operation result)
argsRecursiveMaps ANil = Right MapsNil
argsRecursiveMaps (family :& rest) =
    MapsCons <$> recursiveGroups family <*> argsRecursiveMaps rest

-- | Whether any argument family is recursive.
anyRecursiveArgument :: Args gen argKeys operation result -> Bool
anyRecursiveArgument ANil = False
anyRecursiveArgument (family :& rest) =
    isRecursiveGrouped family || anyRecursiveArgument rest

-- | Collect keyed recursive languages into one alternative per key, in order.
mergeByKey :: (Ord key) => [(key, Recursive a)] -> Map.Map key (Recursive a)
mergeByKey keyed =
    Map.mapMaybe mergeRecursiveGroups $
        foldl'
            (\groups (key, group) -> Map.insertWith (flip (<>)) key [group] groups)
            Map.empty
            keyed

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
    | any (isRecursiveGrouped . snd) alternatives =
        CyclicGrouped $
            if sameWeights
                then
                    mergeByKey
                        . concatMap Map.toAscList
                        <$> traverse (recursiveGroups . snd) alternatives
                else Left WeightedRecursiveAlternatives
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
        go ((_, CyclicGrouped (Left err)) : _) = Just err
        go (_ : rest) = go rest

    sameWeights = case map fst alternatives of
        [] -> True
        firstWeight : rest -> all (== firstWeight) rest

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
ungroup (CyclicGrouped result) =
    Cyclic $ do
        groups <- result
        maybe (Left EmptyGenerator) Right $ mergeRecursiveGroups $ Map.elems groups
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
    | any (isRecursive . snd) alternatives =
        Cyclic $ do
            views <- traverse (recursiveView . snd) alternatives
            if sameWeights
                then
                    pure $
                        Recursive
                            ( Node
                                [ Edge (frequencySymbol index) [recursiveSupport view]
                                | (index, view) <- zip [0 ..] views
                                ]
                            )
                            (choiceIndex $ map recursiveIndex views)
                            Nothing
                else Left WeightedRecursiveAlternatives
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

    sameWeights = case map fst alternatives of
        [] -> True
        firstWeight : rest -> all (== firstWeight) rest

-- | Generate two values whose projected keys agree.
match ::
    (GenBackend gen) =>
    On left right ->
    ECTAGen gen left ->
    ECTAGen gen right ->
    ECTAGen gen (left, right)
match _ (Transparent (Left err)) _ = Transparent $ Left err
match _ _ (Transparent (Left err)) = Transparent $ Left err
match _ (Cyclic _) _ = Transparent $ Left UnboundedGenerator
match _ _ (Cyclic _) = Transparent $ Left UnboundedGenerator
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

{- | Return the ECTA support of an inspectable generator.

A recursive generator's support is its @Mu@ node, which accepts members of
every size: a size bound restricts the rank space, not the automaton.
-}
support :: ECTAGen gen a -> Either ECTAGenError Node
support (Transparent result) = staticSupport <$> result
support (Cyclic result) = recursiveSupport <$> result
support (Opaque _) = Left CannotInspectOpaqueGenerator

{- | Return the exact number of ranks in a transparent generator.

A recursive generator has no cardinality; bound it with 'upToSize', or ask
for one size class with 'countAtSize'.
-}
cardinality :: ECTAGen gen a -> Either ECTAGenError Integer
cardinality (Transparent result) =
    outcomeCardinality . staticOutcomes <$> result
cardinality (Cyclic _) = Left UnboundedGenerator
cardinality (Opaque _) = Left CannotInspectOpaqueGenerator

{- | The number of members of one size, for any inspectable generator.

Size is the number of source choices in a member. This is the counting a
recursive generator supports in place of a cardinality: every class is
finite even when the language is not.
-}
countAtSize :: ECTAGen gen a -> Int -> Either ECTAGenError Integer
countAtSize generator size =
    flip Size.countAtSize size . recursiveIndex <$> recursiveView generator

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
unrank (Cyclic result) index = do
    recursive <- result
    let recursiveIndex' = recursiveIndex recursive
    case sizeClassOf recursiveIndex' index of
        Just (size, position) ->
            pure $ snd $ sizeClassSelect recursiveIndex' size position
        Nothing ->
            Left $
                SelectionOutOfRange index $
                    sum $
                        sizeClassCounts recursiveIndex'
unrank (Opaque _) _ = Left CannotInspectOpaqueGenerator

{- | Structural shrink candidates for one rank of a transparent generator.

Candidates decode to values from the same language: earlier alternatives at
their minimal ranks come first, then each product component shrinks
independently. Opaque generators and out-of-range ranks have no candidates.
-}
shrinkRank :: ECTAGen gen a -> Integer -> [Integer]
shrinkRank (Cyclic _) _ = []
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
-- Recursive ranks are size-major, so every smaller rank already decodes to
-- a member of at most the same size, and the members of strictly smaller
-- size are exactly the ranks below the current size class.
smallerMembers (Cyclic (Right recursive)) rank
    | Just (size, _) <- sizeClassOf index rank =
        [ sizeClassSelect index smallerSize position
        | smallerSize <- [1 .. size - 1]
        , position <- [0 .. Size.countAtSize index smallerSize - 1]
        ]
  where
    index = recursiveIndex recursive
smallerMembers _ _ = []

{- | The number of source choices in the member a rank decodes to.

'Nothing' for opaque generators and out-of-range ranks.
-}
sizeOfRank :: ECTAGen gen a -> Integer -> Maybe Int
sizeOfRank (Cyclic (Right recursive)) rank =
    fst <$> sizeClassOf (recursiveIndex recursive) rank
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
countBy _ (Cyclic _) = Left UnboundedGenerator
countBy _ (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Aggregate the exact probability mass of every transparent result.
pmf :: (Ord a) => ECTAGen gen a -> Either ECTAGenError [(a, Rational)]
pmf (Transparent result) = do
    static <- result
    outcomes <- compileOutcomes static
    pure $
        Map.toAscList $
            Map.fromListWith (+) [(value, mass) | (mass, value) <- outcomes]
pmf (Cyclic _) = Left UnboundedGenerator
pmf (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Lower to the backend, preserving construction and decoding errors.
lower :: (GenBackend gen) => ECTAGen gen a -> gen (Either ECTAGenError a)
lower (Transparent (Left err)) = pure $ Left err
lower (Transparent (Right static)) = sampleStatic static
lower (Cyclic _) = pure $ Left UnboundedGenerator
lower (Opaque generated) = generated

-- | Lower a transparent generator while retaining the sampled rank.
lowerWithRank ::
    (GenBackend gen) =>
    ECTAGen gen a ->
    gen (Either ECTAGenError (Integer, a))
lowerWithRank (Transparent (Left err)) = pure $ Left err
lowerWithRank (Transparent (Right static)) = sampleStaticWithRank static
lowerWithRank (Cyclic _) = pure $ Left UnboundedGenerator
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
