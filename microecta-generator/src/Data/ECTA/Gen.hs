{- | Indexed generators whose transparent regions are represented as ECTAs.

An indexed source stores a finite cardinality and a function from indices to
values. Applicative composition tracks exact cardinalities and rank-based
selection alongside the ECTA, without materializing the product language.
Joins count matched group products and unrank directly within them.
-}
module Data.ECTA.Gen (
    -- * Generators
    ECTAGen,
    Grouped,
    ECTAGenError (..),
    explain,
    GenBackend (..),

    -- * Sources
    Indexed (..),
    fromIndexed,
    elements,
    fromECTA,
    fromBackend,

    -- * Composing
    frequency,
    oneof,
    On (..),
    match,
    relate,

    -- * The grouped layer
    Sig (..),
    sigResult,
    Args (..),
    keyed,
    groupBy,
    regroupBy,
    mapWithKey,
    atKey,
    apply,
    frequencies,
    oneofGrouped,
    ungroup,

    -- * Recursion
    atomic,
    recur,
    recurGrouped,
    upToSize,
    isRecursive,
    isOpaque,

    -- * Inspection
    support,
    cardinality,
    sizes,
    countsAtSize,
    massesAtSize,
    countAtSize,
    minimumSize,
    countBy,
    pmf,
    pmfAtSize,
    smallest,
    unrank,
    sizeOfRank,
    smallerMembers,
    shrinkRank,

    -- * Lowering
    lower,
    lowerWithRank,
    lowerUniform,
    lowerUniformWithRank,
) where

import qualified Data.Array as Array
import Data.Kind (Type)
import qualified Data.Map.Strict as Map

import Data.ECTA (Edge (Edge), Node (EmptyNode, Node), createMu, numNestedMu)
import Data.ECTA.Gen.Internal
import Data.ECTA.Gen.Internal.Automaton (automatonIndex)
import Data.ECTA.Gen.Internal.Decoder (RankDecoder (..))
import Data.ECTA.Gen.Internal.Sampler
import Data.ECTA.Gen.Internal.Shrink (
    planMemberSize,
    shrinkPlanRank,
    smallerPlanMembers,
    smallestPlanRank,
 )
import Data.ECTA.Gen.Internal.Size (
    SizeIndex (sizeClassCounts, sizeClassSelect),
    choiceIndex,
    fixIndex,
    isUnguarded,
    mapIndex,
    minimumMemberSize,
    probeIndex,
    probeIndexWithMinimum,
    productIndex,
    sizeClassOf,
    usesOccurrence,
    withMinimumMemberSize,
 )
import qualified Data.ECTA.Gen.Internal.Size as Size
import Data.ECTA.Gen.Sig (On (..), Sig (..), sigResult)
import Data.ECTA.Term (Symbol, Term)

{- | A transparent generator whose values are classified by a projected key.

The key is not part of the generated value. It classifies values into groups;
during a join, matching key values determine which groups receive equal internal
labels on constrained ECTA paths. Each key group retains compact ECTA support
and indexed selection without storing all outcomes.
-}
data Grouped (gen :: Type -> Type) key a
    = Grouped !(Either ECTAGenError (Map.Map key (KeyedBucket a)))
    | -- | A recursive family: one language per key, all sharing one @Mu@.
      CyclicGrouped !(Either ECTAGenError (Map.Map key (KeyedRecursive a)))

{- | View a grouped generator as a recursive family, one language per key.

A finite family is a recursive one that happens to stop, so this is how the
recursive builders accept either.
-}
recursiveGroups ::
    Grouped gen key a ->
    Either ECTAGenError (Map.Map key (KeyedRecursive a))
recursiveGroups (CyclicGrouped result) = result
recursiveGroups (Grouped result) = keyedRecursiveFromBuckets <$> result

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
recursiveView (Transparent result) = recursiveFromStatic <$> result
recursiveView (Cyclic result) = result
recursiveView (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Whether a generator stands for a recursive language.
isRecursive :: ECTAGen gen a -> Bool
isRecursive (Cyclic _) = True
isRecursive _ = False

-- | Whether a generator is an opaque region, which cannot be inspected.
isOpaque :: ECTAGen gen a -> Bool
isOpaque (Opaque _) = True
isOpaque _ = False

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
            KeyedRecursive
                ( Recursive
                    (recursiveSupport recursive)
                    (mapIndex transform $ recursiveIndex recursive)
                    (mapSampleIndex transform $ recursiveSampling recursive)
                    (recursiveWeighted recursive)
                    (recursiveOccurrence recursive)
                    Nothing
                )
                (keyedRecursiveMasses group)
                (keyedRecursiveMassWeighted group)
          where
            recursive = keyedRecursiveLanguage group

instance (Functor gen) => Functor (ECTAGen gen) where
    fmap transform (Transparent result) = Transparent $ fmap (mapStatic transform) result
    fmap transform (Cyclic result) = Cyclic $ fmap mapRecursive result
      where
        mapRecursive recursive =
            Recursive
                (recursiveSupport recursive)
                (mapIndex transform $ recursiveIndex recursive)
                (mapSampleIndex transform $ recursiveSampling recursive)
                (recursiveWeighted recursive)
                (recursiveOccurrence recursive)
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
                        ( productSampleIndex
                            (recursiveIndex left)
                            (recursiveSampling left)
                            (recursiveIndex right)
                            (recursiveSampling right)
                        )
                        (recursiveWeighted left || recursiveWeighted right)
                        (recursiveOccurrence left || recursiveOccurrence right)
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

{- | Treat every member of a finite generator as one atomic source choice.

An already finite generator keeps its support, cardinality, ranks, values,
and distribution. Only size changes: every complete member has size one when
it is used inside 'recur'. Its finite distribution is also used when sampling
that recursive language. Put 'atomic' around the complete finite choice that
enters recursion; a finite composition outside the boundary is a new choice
and needs its own boundary. An acyclic automaton read with 'fromECTA' closes
its whole finite language without enumerating its terms, rather than taking
an inner prefix from the QuickCheck size. Bound a recursive language with
'upToSize' before making it atomic, /outside/ the recursive definition:
@atomic (upToSize n self)@ inside a 'recur' body asks for an atom whose
cardinality depends on itself, and is rejected with
'BoundedRecursiveOccurrence'. Opaque generators have no size structure to
change.
-}
atomic :: ECTAGen gen a -> ECTAGen gen a
atomic (Transparent result) = Transparent $ atomicStatic <$> result
atomic (Cyclic result) =
    Transparent $ do
        recursive <- result
        if recursiveOccurrence recursive
            then Left BoundedRecursiveOccurrence
            else
                if numNestedMu (recursiveSupport recursive) == 0
                    -- No Mu means the size vector ends. This consumes that whole
                    -- finite vector without asking the caller for its largest size.
                    then atomicStatic <$> boundedStatic maxBound recursive
                    else Left UnboundedGenerator
atomic (Opaque _) = Transparent $ Left CannotInspectOpaqueGenerator

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
QuickCheck adapter does that automatically from the size parameter. A keyed
language recurses with 'recurGrouped' instead.

The self-reference has to go through this combinator. A generator that
names itself directly, as in @tree = Branch '<$>' tree '<*>' tree@, is an
infinite Haskell value: building it never finishes, and the failure is a
hang or @\<\<loop\>\>@ rather than anything this library can report. In the
other direction, a body that never uses the argument is not recursive, and
is returned as it is: a finite body stays a finite generator, with the
cardinality and the inspection that come with it. A body that could not be
built at all is returned with its own error, not as a recursive language.

'upToSize' and 'atomic' cannot be applied to the argument, or to anything
built from it: the bound would need the size classes this definition is still
computing, and an atom over them would have a cardinality depending on itself.
Both shapes are rejected with 'BoundedRecursiveOccurrence'. Bound the finished
language from outside instead, as in @upToSize n (recur ...)@, and keep only
finite atomic choices inside the body.

Two rules apply inside the knot. The recursion must be guarded — every
occurrence of the argument under at least one '<*>' — or the language has no
smallest member; an unguarded definition is rejected with
'UnguardedRecursion' rather than left to diverge. The check is per definition,
so inside a nested 'recur' an occurrence of the /outer/ language must also sit
under an application within the inner body. 'pure' is one source choice, so
@pure f '<*>' self@ counts as guarded where @f '<$>' self@ does not - and
@pure f '<*>' x@ has one more choice than @f '<$>' x@, so the two have
different sizes and different ranks. A recursive language also
needs a finite base member; a guarded cycle with no base is an 'EmptyGenerator'.
Recursive structure is
chosen from its counted size classes, so 'frequency' alternatives around a
recursive occurrence must carry equal weights; 'oneof' is the combinator that
already reads that way, and the size bound controls how large members get. A
weighted finite choice closed with 'atomic' keeps its distribution inside
each recursive size class without changing counts, sizes, or ranks.
-}
recur :: (ECTAGen gen a -> ECTAGen gen a) -> ECTAGen gen a
recur build
    -- An opaque body cannot contain the occurrence, so it is not recursive.
    | Opaque _ <- probeBody = probeBody
    -- A body that failed to build reports its own error. Wrapping it in a
    -- Cyclic would make every finite inspector say UnboundedGenerator before
    -- looking inside, masking what actually went wrong.
    | Left err <- probed = Transparent $ Left err
    -- A body that never reaches its own occurrence is an ordinary language,
    -- and handing it back keeps everything a finite generator can do.
    | Right viewed <- probed
    , not $ usesOccurrence $ recursiveIndex viewed =
        probeBody
    | otherwise = Cyclic result
  where
    -- The body is built against placeholders to tie counts and sampling, to
    -- check its shape, and to create the recursive support. Each build is one
    -- pass over the definition, not over its language.
    bodyOf recursiveArgument = recursiveView $ build recursiveArgument

    -- The placeholders stand for the occurrence, so bounding one is bounding
    -- the language that is still being defined.
    placeholder node index sampling =
        Recursive node index sampling False True Nothing

    tied = fixIndex $ \self ->
        either (const emptyIndex) recursiveIndex $
            bodyOf (Cyclic $ Right $ placeholder EmptyNode self emptySampleIndex)
    emptyIndex = choiceIndex []

    tiedSampling = fixSampleIndex $ \self ->
        either (const emptySampleIndex) recursiveSampling $
            bodyOf (Cyclic $ Right $ placeholder EmptyNode tied self)

    automaton = createMu $ \self ->
        either (const EmptyNode) recursiveSupport $
            bodyOf (Cyclic $ Right $ placeholder self tied tiedSampling)

    -- Built against a probe rather than the knot: reading whether the
    -- occurrence is used, and whether it is guarded, must not count
    -- anything, or an unguarded definition would hang here instead of being
    -- reported.
    probeBody =
        build $
            Cyclic $
                Right $
                    placeholder EmptyNode probeIndex emptySampleIndex
    probed = recursiveView probeBody

    result = do
        body <- probed
        case (isUnguarded $ recursiveIndex body, minimumMemberSize $ recursiveIndex body) of
            (True, _) -> Left UnguardedRecursion
            (_, Nothing) -> Left EmptyGenerator
            _ ->
                pure $
                    Recursive
                        automaton
                        tied
                        tiedSampling
                        (recursiveWeighted body)
                        False
                        Nothing

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

Ambiguity is not counted either. A node's count sums over its edges, which
counts accepting runs, so a node with two edges accepting a common term would
count that term twice and report it at two ranks. Such an automaton is
rejected with 'AmbiguousAutomaton'.
-}
fromECTA :: Node Symbol -> ECTAGen gen (Term Symbol)
fromECTA node =
    Cyclic $ do
        index <- automatonIndex node
        pure $ Recursive node index (uniformSampleIndex index) False False $ Just id

{- | Build a recursive grouped family from its own languages.

The argument receives the family being defined, so a keyed language can
refer to itself — which is what a recursively typed expression language
needs:

@
expressions = ECTAGen.recurGrouped $ \self ->
    ECTAGen.frequencies
        [ (1, literalsByType)
        , (1, ECTAGen.apply (compileBinary '<$>' binaryFunctionsBySignature) (self ':&' self ':&' 'ANil'))
        ]
@

Which keys the family has is itself part of the fixpoint, so it is solved
first, from the empty family upward: each pass adds the result keys of the
operations whose argument keys are already present, and the set can only
grow, so it converges in at most one pass per key. The languages are then
tied lazily over that fixed set.

The reachable key set must be finite. For example,
@oneofGrouped [keyed 0 atom, regroupBy succ self]@ adds another key on every
pass and therefore cannot converge.

All the keys share one @Mu@ node, whose edges carry their key as a first
child. An occurrence at one key is that node under an edge holding the
key's label, with an equality constraint tying the two — so a recursive
family is one recursive automaton whose cycle carries equality constraints,
and the keyed joins inside it keep the constraints they always had. The
joined edges are not reduced, since propagating constraints through a
recursive node is not sound.

'ungroup' and 'atKey' are the exits into an ordinary recursive generator.
The rules of 'recur' apply here too: the recursion must be guarded by an
'apply', every live key must eventually reach a finite base member, and
alternatives around a recursive occurrence must carry equal weights, which is
what 'oneofGrouped' gives without asking for them.
-}
recurGrouped ::
    (Ord key) =>
    (Grouped gen key a -> Grouped gen key a) ->
    Grouped gen key a
recurGrouped build
    -- As in 'recur': a body that failed to build reports its own error rather
    -- than being wrapped in a family every finite inspector calls unbounded.
    | Left err <- probed = Grouped $ Left err
    | Right groups <- probed
    , not $ any (usesOccurrence . recursiveIndex . keyedRecursiveLanguage) groups =
        probeBody
    | otherwise = CyclicGrouped result
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
    -- The placeholders stand for the occurrence, so bounding one is bounding
    -- the family that is still being defined.
    placeholder node index sampling masses =
        KeyedRecursive
            (Recursive node index sampling False True Nothing)
            masses
            False
    noMass = emptyMassIndex
    emptyGroup = placeholder EmptyNode (choiceIndex []) emptySampleIndex noMass

    -- The languages, tied over the settled key set. Supports are irrelevant
    -- here and are filled in against the family node below.
    indexPlaceholders =
        Map.fromList
            [ (key, placeholder EmptyNode (indexAt key) emptySampleIndex noMass)
            | key <- keys
            ]
    rawIndexes =
        either (const Map.empty) (fmap $ recursiveIndex . keyedRecursiveLanguage) $
            bodyGroups indexPlaceholders
    rawIndexAt key = Map.findWithDefault (choiceIndex []) key rawIndexes
    indexAt key =
        withMinimumMemberSize
            (Map.lookup key minimumSizes)
            (rawIndexAt key)

    -- A key is live when its body can close using finite branches or keys
    -- already known to be live. Repeating this over the settled finite key set
    -- gives the least minimum for every mutually recursive language.
    minimumSizes = convergeMinimums Map.empty
    convergeMinimums current =
        let reached =
                either (const Map.empty) (Map.mapMaybe minimumOfGroup) $
                    bodyGroups $
                        Map.fromList
                            [ ( key
                              , placeholder
                                    EmptyNode
                                    (probeIndexWithMinimum $ Map.lookup key current)
                                    emptySampleIndex
                                    noMass
                              )
                            | key <- keys
                            ]
            grown = Map.unionWith min current reached
         in if grown == current then current else convergeMinimums grown
    minimumOfGroup = minimumMemberSize . recursiveIndex . keyedRecursiveLanguage

    -- Key masses form a guarded knot beside counts. Across all keys they sum
    -- to the structural member count at each size.
    massPlaceholders =
        Map.fromList
            [ (key, placeholder EmptyNode (indexAt key) emptySampleIndex $ massAt key)
            | key <- keys
            ]
    tiedMasses =
        either (const Map.empty) (fmap keyedRecursiveMasses) $
            bodyGroups massPlaceholders
    massAt key = Map.findWithDefault noMass key tiedMasses

    -- Sampling follows counts and masses through the same mutually recursive
    -- family. Products only ask occurrences for smaller sizes.
    samplingPlaceholders =
        Map.fromList
            [ ( key
              , placeholder
                    EmptyNode
                    (indexAt key)
                    (samplingAt key)
                    (massAt key)
              )
            | key <- keys
            ]
    tiedSamplings =
        either (const Map.empty) (fmap $ recursiveSampling . keyedRecursiveLanguage) $
            bodyGroups samplingPlaceholders
    samplingAt key = Map.findWithDefault emptySampleIndex key tiedSamplings

    -- One node for the whole family: one key-labelled edge per key, and
    -- every occurrence inside restricted to its own key by a constraint.
    family = createMu $ \self ->
        let bodies = either (const Map.empty) id $ bodyGroups $ occurrences self
         in familyNode
                [ ( positionOf key
                  , maybe
                        EmptyNode
                        (recursiveSupport . keyedRecursiveLanguage)
                        (Map.lookup key bodies)
                  )
                | key <- keys
                ]
    occurrences self =
        Map.fromList
            [ ( key
              , placeholder
                    (restrictToKey (positionOf key) self)
                    (indexAt key)
                    (samplingAt key)
                    (massAt key)
              )
            | key <- keys
            ]

    probeBody =
        build $
            CyclicGrouped $
                Right $
                    Map.fromList
                        [ (key, placeholder EmptyNode probeIndex emptySampleIndex noMass)
                        | key <- keys
                        ]
    probed = recursiveGroups probeBody

    result = do
        bodies <- bodyGroups samplingPlaceholders
        probedBodies <- probed
        if any (isUnguarded . recursiveIndex . keyedRecursiveLanguage) probedBodies
            then Left UnguardedRecursion
            else Right ()
        if Map.null minimumSizes
            then Left EmptyGenerator
            else Right ()
        let familyMassWeighted = any keyedRecursiveMassWeighted bodies
            familyWeighted =
                familyMassWeighted
                    || any (recursiveWeighted . keyedRecursiveLanguage) bodies
        pure $
            Map.fromList
                [ ( key
                  , KeyedRecursive
                        ( Recursive
                            (restrictToKey (positionOf key) family)
                            (indexAt key)
                            (samplingAt key)
                            familyWeighted
                            False
                            Nothing
                        )
                        (massAt key)
                        familyMassWeighted
                  )
                | key <- keys
                , Map.member key bodies
                , Map.member key minimumSizes
                ]

{- | Bound a generator to the members of size at most the given bound.

Size is the number of source choices in a member. A recursive generator
becomes an ordinary finite one and keeps the ranks it already had, so a rank
found under one bound replays under any larger bound and through the unbounded
generator itself. Size classes keep their count-based probability. Weighted
finite choices closed with 'atomic' keep their own distribution inside those
classes.

This bounds recursion; it does not filter a finite language. A generator
that is not recursive is returned unchanged, members larger than the bound
included.

Bounding the recursive occurrence inside the 'recur' or 'recurGrouped' body
that defines it is rejected with 'BoundedRecursiveOccurrence': the bound would
need the size classes the definition is still computing. Bound the finished
language instead, as in @upToSize n (recur ...)@.
-}
upToSize :: Int -> ECTAGen gen a -> ECTAGen gen a
upToSize bound (Cyclic result) =
    Transparent $ do
        recursive <- result
        if recursiveOccurrence recursive
            then Left BoundedRecursiveOccurrence
            else boundedStatic bound recursive
upToSize _ generator = generator

-- | Choose uniformly from a finite non-empty list.
elements :: [a] -> ECTAGen gen a
elements values =
    fromIndexed $
        Indexed
            (toInteger total)
            ((indexed Array.!) . fromInteger)
  where
    total = length values
    indexed = Array.listArray (0, total - 1) values

{- | Declare that every member of an inspectable generator has one key.

This enters the grouped layer without enumerating members. It preserves a
finite or recursive generator's support, ranks, and distribution unchanged.
Use 'groupBy' when the key must be computed from each member. Opaque generators
cannot be keyed because they have no inspectable support or rank index.
-}
keyed :: key -> ECTAGen gen a -> Grouped gen key a
keyed key (Transparent result) =
    Grouped $ fmap (Map.singleton key . KeyedBucket 1) result
keyed key (Cyclic result) =
    CyclicGrouped $ fmap (Map.singleton key . keyedRecursive) result
keyed _ (Opaque _) = Grouped $ Left CannotInspectOpaqueGenerator

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
        traverse (bucketFromOutcomes $ staticAtomic static) $
            groupOutcomes
                [ (key $ outcomeValue outcome, outcome)
                | outcome <- outcomes
                ]
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
        KeyedRecursive
            ( Recursive
                (recursiveSupport recursive)
                (mapIndex (transform key) $ recursiveIndex recursive)
                (mapSampleIndex (transform key) $ recursiveSampling recursive)
                (recursiveWeighted recursive)
                (recursiveOccurrence recursive)
                Nothing
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

-- | Return the exact cardinality of each retained group in O(number of groups).
sizes :: Grouped gen key a -> Either ECTAGenError (Map.Map key Integer)
sizes (CyclicGrouped _) = Left UnboundedGenerator
sizes (Grouped result) =
    fmap (fmap $ outcomeCardinality . staticOutcomes . keyedBucketStatic) result

{- | Return the exact number of retained members in every live key at one
structural size.

Counts describe the language, not the sampler. A declared atomic distribution
can therefore give two keys equal counts and unequal probability masses.
-}
countsAtSize :: Grouped gen key a -> Int -> Either ECTAGenError (Map.Map key Integer)
countsAtSize (CyclicGrouped result) size = do
    groups <- result
    if size < 1
        then pure Map.empty
        else
            pure $
                Map.filter (> 0) $
                    fmap
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
            pure $
                Map.filter (> 0) $
                    fmap
                        ( \bucket ->
                            Size.countAtSize
                                (Size.sizeIndex $ outcomePlan $ staticOutcomes $ keyedBucketStatic bucket)
                                size
                        )
                        buckets

{- | Return the exact distribution of retained keys conditional on one
structural size.

This is the distribution used by sampling that exact size. Weighted atomic
choices retain both their between-key and within-key distributions. Recursive
families memoize each key's mass series. A query extends that recurrence to the
requested size without enumerating members, then normalizes one mass per key.
A finite family may enumerate group outcomes to condition their stored masses
on size. A size with no members returns an empty map.
-}
massesAtSize :: Grouped gen key a -> Int -> Either ECTAGenError (Map.Map key Rational)
massesAtSize (CyclicGrouped result) size = do
    groups <- result
    if size < 1
        then pure Map.empty
        else do
            let positive = Map.filter (> 0) $ fmap (\group -> keyedRecursiveMassAtSize group size) groups
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

{- | Select one retained group as an ordinary conditional generator.

A missing key produces 'EmptyGenerator'.
-}
atKey :: (Ord key) => key -> Grouped gen key a -> ECTAGen gen a
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
    Map.Map (Sig argKeys resultKey) (KeyedBucket operation) ->
    Args gen argKeys operation result ->
    Grouped gen resultKey result
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
    Args gen argKeys operation result ->
    Either ECTAGenError (ArgMaps KeyedRecursive argKeys operation result)
argsRecursiveMaps ANil = Right MapsNil
argsRecursiveMaps (family :& rest) =
    MapsCons <$> recursiveGroups family <*> argsRecursiveMaps rest

-- | Whether any argument family is recursive.
anyRecursiveArgument :: Args gen argKeys operation result -> Bool
anyRecursiveArgument ANil = False
anyRecursiveArgument (family :& rest) =
    isRecursiveGrouped family || anyRecursiveArgument rest

-- | Collect keyed recursive languages into one alternative per key, in order.
mergeByKey :: (Ord key) => [(key, KeyedRecursive a)] -> Map.Map key (KeyedRecursive a)
mergeByKey entries =
    Map.mapMaybe mergeRecursiveGroups $
        foldl'
            (\groups (key, group) -> Map.insertWith (flip (<>)) key [group] groups)
            Map.empty
            entries

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

{- | Choose uniformly among grouped generators, group by group.

'frequencies' with equal weights, which is the only shape a recursive
family admits.
-}
oneofGrouped :: (Ord key) => [Grouped gen key a] -> Grouped gen key a
oneofGrouped alternatives = frequencies [(1, alternative) | alternative <- alternatives]

-- | Merge all retained groups while preserving their probability masses.
ungroup :: Grouped gen key a -> ECTAGen gen a
ungroup = atKey () . regroupBy (const ())

-- | Find the first invalid alternative weight.
firstNonPositiveWeight :: [(Integer, a)] -> Maybe Integer
firstNonPositiveWeight = go
  where
    go [] = Nothing
    go ((weight, _) : rest)
        | weight <= 0 = Just weight
        | otherwise = go rest

-- | Whether every alternative carries the same weight.
allWeightsEqual :: [(Integer, a)] -> Bool
allWeightsEqual [] = True
allWeightsEqual ((firstWeight, _) : rest) =
    all ((== firstWeight) . fst) rest

-- | Choose one generator with the supplied positive relative weight.
frequency ::
    (GenBackend gen) =>
    [(Integer, ECTAGen gen a)] ->
    ECTAGen gen a
frequency [] = Transparent $ Left EmptyGenerator
frequency alternatives
    | Just badWeight <- firstNonPositiveWeight alternatives =
        Transparent $ Left $ NonPositiveWeight badWeight
    | Just err <- firstError alternatives = Transparent $ Left err
    | Just staticAlternatives <- traverse getStatic alternatives =
        Transparent $ Right $ frequencyStatic staticAlternatives
    | any (isRecursive . snd) alternatives =
        Cyclic $ do
            views <- traverse (recursiveView . snd) alternatives
            if allWeightsEqual alternatives
                then
                    pure $
                        Recursive
                            ( Node
                                [ Edge (frequencySymbol index) [recursiveSupport view]
                                | (index, view) <- zip [0 ..] views
                                ]
                            )
                            (choiceIndex $ map recursiveIndex views)
                            ( choiceSampleIndex
                                [ (recursiveIndex view, recursiveSampling view)
                                | view <- views
                                ]
                            )
                            (any recursiveWeighted views)
                            (any recursiveOccurrence views)
                            Nothing
                else Left WeightedRecursiveAlternatives
    | otherwise =
        Opaque $
            frequencyGen
                [(weight, lower generator) | (weight, generator) <- alternatives]
  where
    firstError = go
      where
        go [] = Nothing
        go ((_, Transparent (Left err)) : _) = Just err
        go (_ : rest) = go rest

    getStatic (weight, Transparent (Right static)) = Just (weight, static)
    getStatic _ = Nothing

{- | Choose uniformly among generators.

Every alternative is equally likely, whatever the size of its language, as
in QuickCheck's own @oneof@. In a recursive definition this is the shape to
reach for: weights around a recursive occurrence are rejected, because such
a language uses structural counts for global size selection and rank offsets.
A finite choice closed with 'atomic' can still retain its own sampler mass
within the selected size.
-}
oneof :: (GenBackend gen) => [ECTAGen gen a] -> ECTAGen gen a
oneof alternatives = frequency [(1, alternative) | alternative <- alternatives]

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

{- | Generate two values whose projected keys satisfy a relation.

For finite inspectable inputs, the relation is evaluated once per live key
pair. The accepted group products are counted and sampled directly without
rejection. The key types may differ, and the relation need not be symmetric.
The relation must be total for every live key pair. An opaque input uses
backend rejection filtering instead.
-}
relate ::
    (GenBackend gen, Ord leftKey, Ord rightKey) =>
    (left -> leftKey) ->
    (right -> rightKey) ->
    (leftKey -> rightKey -> Bool) ->
    ECTAGen gen left ->
    ECTAGen gen right ->
    ECTAGen gen (left, right)
relate _ _ _ (Transparent (Left err)) _ = Transparent $ Left err
relate _ _ _ _ (Transparent (Left err)) = Transparent $ Left err
relate _ _ _ (Cyclic _) _ = Transparent $ Left UnboundedGenerator
relate _ _ _ _ (Cyclic _) = Transparent $ Left UnboundedGenerator
relate leftKey rightKey relation (Transparent (Right left)) (Transparent (Right right)) =
    Transparent $ relateStatic leftKey rightKey relation left right
relate leftKey rightKey relation left right =
    let generatedPairs = liftA2 (liftA2 (,)) (lower left) (lower right)
        related (Left _) = True
        related (Right (leftValue, rightValue)) =
            relation (leftKey leftValue) (rightKey rightValue)
     in Opaque $ filterGen related generatedPairs

{- | Return the ECTA support of an inspectable generator.

A recursive generator's support is its @Mu@ node, which accepts members of
every size: a size bound restricts the rank space, not the automaton.
-}
support :: ECTAGen gen a -> Either ECTAGenError (Node Symbol)
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

{- | The smallest structural size in an inspectable language.

Size is the number of source choices in a member. 'Nothing' means the language
is empty. Opaque generators cannot be inspected.
-}
minimumSize :: ECTAGen gen a -> Either ECTAGenError (Maybe Int)
minimumSize generator = case recursiveView generator of
    Left EmptyGenerator -> Right Nothing
    Left err -> Left err
    Right recursive -> Right $ minimumMemberSize $ recursiveIndex recursive

{- | Decode one stable rank from an inspectable generator.

Ranks are stable while the generator definition and the ordering of its finite
sources remain unchanged.
-}
unrank :: ECTAGen gen a -> Integer -> Either ECTAGenError a
unrank _ index | index < 0 = Left $ NegativeRank index
unrank (Transparent result) index = do
    static <- result
    let outcomes = staticOutcomes static
    checkIndex (outcomeCardinality outcomes) index
    pure $ outcomeValueAt outcomes index
unrank (Cyclic result) index = do
    recursive <- result
    let recursiveIndex' = recursiveIndex recursive
    case (minimumMemberSize recursiveIndex', sizeClassOf recursiveIndex' index) of
        (Nothing, _) -> Left $ SelectionOutOfRange index 0
        (_, Just (size, position)) ->
            pure $ snd $ sizeClassSelect recursiveIndex' size position
        (_, Nothing) ->
            Left $
                SelectionOutOfRange index $
                    sum $
                        sizeClassCounts recursiveIndex'
unrank (Opaque _) _ = Left CannotInspectOpaqueGenerator

{- | Return the first member in structural size and rank order.

For recursive generators this is a globally smallest member. 'Nothing' means
the language is empty; other construction or inspection failures stay explicit.
-}
smallest :: ECTAGen gen a -> Either ECTAGenError (Maybe a)
smallest (Transparent result) =
    case result of
        Left EmptyGenerator -> Right Nothing
        Left err -> Left err
        Right static ->
            case smallestPlanRank $ outcomePlan $ staticOutcomes static of
                Nothing -> Right Nothing
                Just rank -> Right $ Just $ outcomeValueAt (staticOutcomes static) rank
smallest generator@(Cyclic _) =
    case unrank generator 0 of
        Left EmptyGenerator -> Right Nothing
        Left (SelectionOutOfRange 0 0) -> Right Nothing
        Left err -> Left err
        Right value -> Right $ Just value
smallest (Opaque _) = Left CannotInspectOpaqueGenerator

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

{- | Every member of strictly smaller size than the given rank's member, in
size order, as replayable rank and value.

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
-- Recursive ranks are size-major, so the members of strictly smaller size are
-- exactly the ranks below the current size class. The rank is that class's
-- offset plus the position, which is what 'unrank' reads back; the rank
-- 'sizeClassSelect' reports is the plan's own, and the two differ whenever a
-- size class came from a finite bucket.
smallerMembers (Cyclic (Right recursive)) rank
    | Just (size, _) <- sizeClassOf index rank =
        [ (offset + position, snd $ sizeClassSelect index smallerSize position)
        | (smallerSize, offset) <- zip [1 .. size - 1] (scanl (+) 0 (sizeClassCounts index))
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

-- | Aggregate the exact probability mass of every finite transparent result.
pmf :: (Ord a) => ECTAGen gen a -> Either ECTAGenError [(a, Rational)]
pmf (Transparent result) = do
    static <- result
    outcomes <- compileOutcomes static
    pure $
        Map.toAscList $
            Map.fromListWith (+) [(value, mass) | (mass, value) <- outcomes]
pmf (Cyclic _) = Left UnboundedGenerator
pmf (Opaque _) = Left CannotInspectOpaqueGenerator

{- | Aggregate the exact result distribution conditional on one structural
size.

For a recursive generator this interprets its size-indexed sampler, so a
weighted finite choice closed with 'atomic' retains its declared probability.
For a finite generator it conditions the retained outcome masses on the
requested size. A size with no members returns an empty distribution.

This enumerates every result in the selected size class before equal results
are aggregated. A language can therefore be cheap to count and too large for
this observer. Use 'countAtSize' for cardinality, or 'massesAtSize' when a
retained-key distribution answers the question.
-}
pmfAtSize :: (Ord a) => ECTAGen gen a -> Int -> Either ECTAGenError [(a, Rational)]
pmfAtSize (Transparent result) size = do
    static <- result
    if size < 1
        then Right []
        else do
            outcomes <- enumerateOutcomeIndex $ staticOutcomes static
            let plan = outcomePlan $ staticOutcomes static
                selected =
                    [ (outcomeMass outcome, outcomeValue outcome)
                    | (rank, outcome) <- zip [0 ..] outcomes
                    , planMemberSize plan rank == size
                    ]
            if null selected
                then Right []
                else do
                    normalized <- normalize selected
                    pure $
                        Map.toAscList $
                            Map.fromListWith (+) [(value, mass) | (mass, value) <- normalized]
pmfAtSize (Cyclic result) size = do
    recursive <- result
    if Size.countAtSize (recursiveIndex recursive) size <= 0
        then Right []
        else Right $ exactPmfAtSize (recursiveSampling recursive) size
pmfAtSize (Opaque _) _ = Left CannotInspectOpaqueGenerator

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
