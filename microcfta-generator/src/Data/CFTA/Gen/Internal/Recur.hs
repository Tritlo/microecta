{- | The recursive generator builders and the bound that closes them.

Each builder ties its own language through a fixpoint: counts, masses,
sampling, and the @Mu@ support are solved together, and each pass reads the
definition rather than its language. 'upToSize' turns the result back into a
finite generator with the ranks the recursive language already gave it.
-}
module Data.CFTA.Gen.Internal.Recur (
    atomic,
    recur,
    recurGrouped,
    upToSize,
) where

import Control.Monad (void, when)
import Data.CFTA.Constraint (Constraint (..), HasEqualities (..))
import Data.Either (fromRight)
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import Data.Typeable (Typeable)

import Data.CFTA.Equality (Node (EmptyNode), createMu, numNestedMu)
import Data.CFTA.Gen.Error
import Data.CFTA.Gen.Internal.Inspection
import Data.CFTA.Gen.Internal.Recursive
import Data.CFTA.Gen.Internal.Static
import Data.CFTA.Gen.Internal.Support
import Data.CFTA.Gen.Internal.Types
import Data.CFTA.Gen.Label (Label (..))
import Data.CFTA.Ranked.Internal.Sampler
import Data.CFTA.Ranked.Internal.Size (
    SizeIndex (sizeClassSelect),
    choiceIndex,
    fixIndex,
    isUnguarded,
    minimumMemberSize,
    probeIndex,
    probeIndexWithMinimum,
    sizeClassOf,
    usesOccurrence,
    withMinimumMemberSize,
 )

-- | Treat every member of a finite generator as one atomic source choice.
atomic :: Gen symbol constraint a -> Gen symbol constraint a
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

-- | Build a recursive generator from its own language.
recur ::
    (Constraint constraint, Hashable symbol, Typeable symbol) =>
    (Gen symbol constraint a -> Gen symbol constraint a) -> Gen symbol constraint a
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
    placeholder supportNode index sampling =
        Recursive supportNode index sampling False True Nothing (plainInspection supportNode)

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

    inspection = Inspection name graph
      where
        name = either (const Nothing) (inspectionName . recursiveInspection) probed
        graph = createMu $ \self ->
            either (const EmptyNode) (inspectionGraph . recursiveInspection)
                $ bodyOf
                $ Cyclic
                $ Right
                $ (placeholder EmptyNode tied tiedSampling)
                    { recursiveInspection = Inspection name self
                    }

    -- Built against a probe rather than the knot: reading whether the
    -- occurrence is used, and whether it is guarded, must not count
    -- anything, or an unguarded definition would hang here instead of being
    -- reported.
    probeBody =
        build
            $ Cyclic
            $ Right
            $ placeholder EmptyNode probeIndex emptySampleIndex
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
                        inspection

-- | Build a recursive grouped family from its own languages.
recurGrouped ::
    (HasEqualities constraint, Ord key, Hashable symbol, Typeable symbol) =>
    (Grouped symbol constraint key a -> Grouped symbol constraint key a) ->
    Grouped symbol constraint key a
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
                either (const Map.empty) (void)
                    $ bodyGroups
                    $ fmap (const emptyGroup) current
            grown = Map.union current reached
         in if Map.keys grown == Map.keys current then current else converge grown
    keys = Map.keys keySet
    positions = Map.fromList $ zip keys [0 ..]
    positionOf key = Map.findWithDefault 0 key positions
    -- The placeholders stand for the occurrence, so bounding one is bounding
    -- the family that is still being defined.
    placeholder supportNode index sampling masses =
        KeyedRecursive
            (Recursive supportNode index sampling False True Nothing $ plainInspection supportNode)
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
                either (const Map.empty) (Map.mapMaybe minimumOfGroup)
                    $ bodyGroups
                    $ Map.fromList
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
        let bodies = fromRight Map.empty $ bodyGroups $ occurrences self
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

    -- Diagnostic labels use a separate knot. Counts, masses, and sampling do
    -- not need to build this graph or evaluate its retained labels.
    inspectionNames =
        either
            (const Map.empty)
            (fmap $ inspectionName . recursiveInspection . keyedRecursiveLanguage)
            probed
    nameForKey key = Map.findWithDefault Nothing key inspectionNames
    namesByPosition = Map.fromList [(positionOf key, nameForKey key) | key <- keys]
    labelKey symbol@(Key position) = InspectionSymbol symbol $ Map.findWithDefault Nothing position namesByPosition
    labelKey symbol = plainSymbol symbol
    inspectionFamily = createMu $ \self ->
        let bodies = fromRight Map.empty $ bodyGroups $ inspectionOccurrences self
         in familyNodeWith
                labelKey
                [ ( positionOf key
                  , maybe
                        EmptyNode
                        (inspectionGraph . recursiveInspection . keyedRecursiveLanguage)
                        (Map.lookup key bodies)
                  )
                | key <- keys
                ]
    inspectionOccurrences self =
        Map.fromList
            [ ( key
              , let group = placeholder EmptyNode (indexAt key) (samplingAt key) (massAt key)
                 in group
                        { keyedRecursiveLanguage =
                            (keyedRecursiveLanguage group)
                                { recursiveInspection =
                                    Inspection
                                        (nameForKey key)
                                        (restrictToKeyWith labelKey (positionOf key) self)
                                }
                        }
              )
            | key <- keys
            ]

    probeBody =
        build
            $ CyclicGrouped
            $ Right
            $ Map.fromList
                [ (key, placeholder EmptyNode probeIndex emptySampleIndex noMass)
                | key <- keys
                ]
    probed = recursiveGroups probeBody

    result = do
        bodies <- bodyGroups samplingPlaceholders
        probedBodies <- probed
        when (any (isUnguarded . recursiveIndex . keyedRecursiveLanguage) probedBodies) $
            Left UnguardedRecursion
        when (Map.null minimumSizes) $ Left EmptyGenerator
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
                            ( Inspection
                                (nameForKey key)
                                (restrictToKeyWith labelKey (positionOf key) inspectionFamily)
                            )
                        )
                        (massAt key)
                        familyMassWeighted
                  )
                | key <- keys
                , Map.member key bodies
                , Map.member key minimumSizes
                ]

{- | Bound a generator to the members of size at most the given bound.

The result is finite, with size-major ranks. A recursive language keeps the
ranks it gives its members. A finite language is re-ranked by size and keeps
its terms. An opaque generator has no sizes and is unchanged.
-}
upToSize :: Int -> Gen symbol constraint a -> Gen symbol constraint a
upToSize bound (Cyclic result) =
    Transparent $ do
        recursive <- result
        if recursiveOccurrence recursive
            then Left BoundedRecursiveOccurrence
            else boundedStatic bound recursive
upToSize bound (Transparent result) = Transparent $ result >>= boundedFinite bound
upToSize _ opaque = opaque

-- | Restrict a finite language to its members of size at most the bound.
boundedFinite :: Int -> Static symbol constraint a -> Either GenError (Static symbol constraint a)
boundedFinite bound static = do
    bounded <- boundedStatic bound $ recursiveFromStatic static
    let outcomes = staticOutcomes bounded
        total = outcomeCardinality outcomes
        -- Size-major ranks are a prefix of the unbounded size-major order, so
        -- the original size index maps a bounded rank to its original rank.
        select rank = do
            checkIndex total rank
            case sizeClassOf index rank of
                Nothing -> Left $ SelectionOutOfRange rank total
                Just (size, position) -> do
                    outcome <- outcomeSelect original $ fst $ sizeClassSelect index size position
                    pure outcome{outcomeMass = 1 / fromInteger total}
    pure bounded{staticOutcomes = outcomes{outcomeSelect = select}}
  where
    original = staticOutcomes static
    index = outcomeSizeIndex original
