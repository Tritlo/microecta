{- | The recursive generator builders and the bound that closes them.

Each builder ties its own language through a fixpoint: counts, masses,
sampling, terms, inspection, and the @Mu@ support are tied in separate passes,
and each pass reads the definition rather than its language. 'upToSize' turns
the result back into a finite generator with the ranks the recursive language
already gave it.
-}
module Data.CFTA.Gen.Internal.Recur (
    atomic,
    recur,
    recurGrouped,
    upToSize,
) where

import Control.Monad (when)
import Data.Either (fromRight)
import Data.Hashable (Hashable)
import Data.IORef (IORef, atomicModifyIORef', newIORef)
import qualified Data.Map.Strict as Map
import Data.Typeable (Typeable)
import System.IO.Unsafe (unsafePerformIO)

import Data.CFTA.Equality (Node (EmptyNode), createMu)
import Data.CFTA.Gen.Error
import Data.CFTA.Gen.Internal.Inspection
import Data.CFTA.Gen.Internal.Recursive
import Data.CFTA.Gen.Internal.Static
import Data.CFTA.Gen.Internal.Support
import Data.CFTA.Gen.Internal.Types
import Data.CFTA.Gen.Label (Label (..))
import Data.CFTA.Index (Size (..))
import Data.CFTA.Ranked.Internal.Decoder (RankedValue (..))
import Data.CFTA.Ranked.Internal.Sampler
import Data.CFTA.Ranked.Internal.Size (
    LargestSize (..),
    MinimumSize (..),
    Occurrence (..),
    SizeIndex (largestMemberSize, sizeClassSelect),
    SizedRank (..),
    choiceIndex,
    closedOccurrence,
    closedProbe,
    closedProbeWithOccurrencesOf,
    fixIndex,
    isUnguarded,
    minimumMemberSize,
    minimumOf,
    probeIndexWithMinimum,
    reachesOccurrence,
    sameOccurrences,
    sizeClassOf,
    usesOccurrence,
    withKnotMetadata,
 )

-- | Treat every member of a finite generator as one atomic source choice.
atomic :: Gen symbol a -> Gen symbol a
atomic (Transparent result) = Transparent $ atomicStatic <$> result
atomic (Cyclic result) =
    Transparent $ do
        recursive <- result
        if reachesOccurrence $ recursiveIndex recursive
            then Left BoundedRecursiveOccurrence
            else case largestMemberSize $ recursiveIndex recursive of
                -- The sizes end, so the bound keeps every member. A bounded
                -- recursion keeps its Mu in the support, so the support cannot
                -- tell whether the sizes end.
                LargestSize _ -> atomicStatic <$> boundedStatic (Size $ toInteger (maxBound :: Int)) recursive
                SizesDoNotEnd -> Left UnboundedGenerator
atomic (Opaque _) = Transparent $ Left CannotInspectOpaqueGenerator

-- | Build a recursive generator from its own language.
recur ::
    (Hashable symbol, Typeable symbol) =>
    (Gen symbol a -> Gen symbol a) -> Gen symbol a
recur build
    -- An opaque body cannot contain the occurrence, so it is not recursive.
    | Opaque _ <- probeBody = probeBody
    -- A body that failed to build reports its own error. Wrapping it in a
    -- Cyclic would make every finite inspector say UnboundedGenerator before
    -- looking inside, masking the error that occurred.
    | Left err <- probed = Transparent $ Left err
    -- A body that never reaches its own occurrence is an ordinary language,
    -- and handing it back keeps everything a finite generator can do.
    | Right viewed <- probed
    , not $ usesOccurrence token $ recursiveIndex viewed =
        probeBody
    | otherwise = Cyclic result
  where
    token = freshToken build

    -- The body is built against placeholders to tie counts and sampling, to
    -- check its shape, and to create the recursive support. Each build is one
    -- pass over the definition, not over its language.
    bodyOf recursiveArgument = recursiveView $ build recursiveArgument

    -- The placeholders stand for the occurrence, so bounding one is bounding
    -- the language that is still being defined.
    placeholder supportNode index sampling =
        Recursive supportNode index sampling False Nothing (plainInspection supportNode)

    tied = fixIndex occurrenceMinimum $ \self ->
        either (const emptyIndex) recursiveIndex $
            bodyOf (Cyclic $ Right $ placeholder EmptyNode self emptySampleIndex)
      where
        emptyIndex = choiceIndex []
    tiedSampling = fixSampleIndex $ \self ->
        either (const emptySampleIndex) recursiveSampling $
            bodyOf (Cyclic $ Right $ placeholder EmptyNode tied self)

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
    -- reported. The probe assumes a smallest member for the occurrence,
    -- first none, then the one the body gives, until the two agree. A nested
    -- definition whose finite members all go through the occurrence is empty
    -- under the first assumption, and the body would drop it and look as if
    -- it did not use the occurrence.
    probeBody = converge NoFiniteMember
      where
        converge assumed =
            let body = build $ Cyclic $ Right $ placeholder EmptyNode (probeIndexWithMinimum token assumed) emptySampleIndex
                reached = either (const NoFiniteMember) (minimumMemberSize . recursiveIndex) $ recursiveView body
                next = case (assumed, reached) of
                    (MinimumSize smallest, MinimumSize size) -> MinimumSize $ min smallest size
                    (NoFiniteMember, size) -> size
                    (smallest, NoFiniteMember) -> smallest
             in if next == assumed then body else converge next
    probed = recursiveView probeBody

    -- The smallest member of the occurrence: the minimum that the probe
    -- converged to. The knots read their flags from a build around a closed
    -- occurrence of this size, so that build has the shape of the probe.
    occurrenceMinimum = either (const NoFiniteMember) (minimumMemberSize . recursiveIndex) probed

    result = do
        body <- probed
        case (isUnguarded token $ recursiveIndex body, minimumMemberSize $ recursiveIndex body) of
            (True, _) -> Left UnguardedRecursion
            (_, NoFiniteMember) -> Left EmptyGenerator
            _ ->
                pure $
                    Recursive
                        automaton
                        tied
                        tiedSampling
                        (recursiveWeighted body)
                        Nothing
                        inspection
      where
        automaton = createMu $ \self ->
            either (const EmptyNode) recursiveSupport $
                bodyOf (Cyclic $ Right $ placeholder self tied tiedSampling)

{- | Build a recursive grouped family from its own languages.

The family has the keys that the body reaches from the keys it already has,
starting from no keys. Each pass builds the body around the keys found so
far, each with the least size of its members found so far, so a nested
'recur' whose members all read the family reaches its keys too. The body
must reach finitely many keys. A key function that makes a new key from each
key, such as @regroupOn (+ 1)@ on the occurrence, makes the key set infinite,
and then 'recurGrouped' does not return.
-}
recurGrouped ::
    (Ord key, Hashable symbol, Typeable symbol) =>
    (Grouped symbol key a -> Grouped symbol key a) ->
    Grouped symbol key a
recurGrouped build
    -- As in 'recur': a body that failed to build reports its own error rather
    -- than being wrapped in a family every finite inspector calls unbounded.
    | Left err <- probed = Grouped $ Left err
    | Right groups <- probed
    , not $ any (usesOccurrence token . recursiveIndex . keyedRecursiveLanguage) groups =
        probeBody
    | otherwise = CyclicGrouped result
  where
    token = freshToken build

    bodyGroups placeholders = recursiveGroups $ build $ CyclicGrouped $ Right placeholders

    keys = Map.keys keyMinimums
    -- The placeholders stand for the occurrence, so bounding one is bounding
    -- the family that is still being defined.
    placeholder supportNode index sampling masses =
        KeyedRecursive
            (Recursive supportNode index sampling False Nothing $ plainInspection supportNode)
            masses
            False
    noMass = emptyMassIndex
    rawIndexes =
        either (const Map.empty) (fmap $ recursiveIndex . keyedRecursiveLanguage) $
            bodyGroups indexPlaceholders
      where
        -- The languages, tied over the settled key set. Supports are irrelevant
        -- here and are filled in against the family node below.
        indexPlaceholders =
            Map.fromList
                [ (key, placeholder EmptyNode (indexAt key) emptySampleIndex noMass)
                | key <- keys
                ]
    rawIndexAt key = Map.findWithDefault (choiceIndex []) key rawIndexes
    indexAt key =
        withKnotMetadata
            (minimumAt key)
            (Map.findWithDefault (choiceIndex []) key closedIndexes)
            (rawIndexAt key)
    -- The family built around tied occurrences, which gives the flags of each
    -- key without reading the knot. Each occurrence has the least minimum of
    -- its key, as in the probe, so a nested definition whose finite members
    -- all go through the family is not empty in this build. An occurrence
    -- carries the flags that the body of its key had in the build before,
    -- until they stop changing: a key that reaches the probe of an enclosing
    -- recursion only through another key reaches it too.
    closedIndexes = converge Map.empty
      where
        converge previous =
            let built =
                    either (const Map.empty) (fmap $ recursiveIndex . keyedRecursiveLanguage)
                        $ bodyGroups
                        $ Map.fromList
                            [ ( key
                              , placeholder EmptyNode (occurrence (Map.lookup key previous) (minimumAt key)) emptySampleIndex noMass
                              )
                            | key <- keys
                            ]
             in if Map.keys built == Map.keys previous && and (Map.intersectionWith sameOccurrences built previous)
                    then built
                    else converge built
        occurrence = maybe closedProbe closedProbeWithOccurrencesOf

    -- The keys and the least minimum of each, from the empty family upward.
    -- Each pass builds the body around a probe of each key found so far, with
    -- the least minimum found so far, and keeps the keys that the body reaches
    -- and their minimums. A key is live when its body can close using finite
    -- branches or keys already known to be live, and a nested definition whose
    -- finite members all go through a live key is live too. The key set only
    -- grows and the minimums only fall, so the loop ends when the body reaches
    -- finitely many keys, with the least minimum of every mutually recursive
    -- language.
    -- TODO: Investigate whether the loop can find an unbounded key set and
    -- report an error, instead of the requirement in the documentation of
    -- 'recurGrouped'.
    keyMinimums = converge Map.empty
      where
        converge current =
            let reached =
                    either (const Map.empty) (fmap minimumOfGroup)
                        $ bodyGroups
                        $ fmap (\minimum' -> placeholder EmptyNode (probeIndexWithMinimum token minimum') emptySampleIndex noMass) current
                grown = Map.unionWith (\left right -> minimumOf [left, right]) current reached
             in if grown == current then current else converge grown
    -- The keys with a finite member, with their least minimums.
    minimumSizes = Map.filter (/= NoFiniteMember) keyMinimums
    minimumAt key = Map.findWithDefault NoFiniteMember key minimumSizes
    minimumOfGroup = minimumMemberSize . recursiveIndex . keyedRecursiveLanguage

    tiedMasses =
        either (const Map.empty) (fmap keyedRecursiveMasses) $
            bodyGroups massPlaceholders
      where
        -- Key masses form a guarded knot beside counts. Across all keys they sum
        -- to the structural member count at each size.
        massPlaceholders =
            Map.fromList
                [ (key, placeholder EmptyNode (indexAt key) emptySampleIndex $ massAt key)
                | key <- keys
                ]
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

    probeBody =
        build
            $ CyclicGrouped
            $ Right
            $ Map.fromList
                [ (key, placeholder EmptyNode (probeIndexWithMinimum token $ minimumAt key) emptySampleIndex noMass)
                | key <- keys
                ]
    probed = recursiveGroups probeBody

    result = do
        bodies <- bodyGroups samplingPlaceholders
        probedBodies <- probed
        when (any (isUnguarded token . recursiveIndex . keyedRecursiveLanguage) probedBodies) $
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
      where
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

        labelKey symbol@(Key position) = InspectionSymbol symbol $ Map.findWithDefault Nothing position namesByPosition
        labelKey symbol = plainSymbol symbol

        namesByPosition = Map.fromList [(positionOf key, nameForKey key) | key <- keys]

        positionOf key = Map.findWithDefault 0 key positions

        positions = Map.fromList $ zip keys [0 ..]

        nameForKey key = Map.findWithDefault Nothing key inspectionNames

        -- Diagnostic labels use a separate knot. Counts, masses, and sampling do
        -- not need to build this graph or evaluate its retained labels.
        inspectionNames =
            either
                (const Map.empty)
                (fmap $ inspectionName . recursiveInspection . keyedRecursiveLanguage)
                probed

{- | Bound a generator to the members of size at most the given bound.

The result is finite, with size-major ranks. A recursive language keeps the
ranks it gives its members. A finite language is re-ranked by size and keeps
its terms. An opaque generator has no sizes and is unchanged.

The result selects a size class in proportion to its number of members.
Inside the size class, the weights of a finite choice become member counts.
This applies to a finite language and to the finite parts of a recursive
language. A choice that 'atomic' closes keeps its distribution inside every
size class.
-}
upToSize :: Size -> Gen symbol a -> Gen symbol a
upToSize bound (Cyclic result) =
    Transparent $ do
        recursive <- result
        if reachesOccurrence $ recursiveIndex recursive
            then Left BoundedRecursiveOccurrence
            else boundedStatic bound recursive
upToSize bound (Transparent result) = Transparent $ result >>= boundedFinite bound
upToSize _ opaque = opaque

-- | Restrict a finite language to its members of size at most the bound.
boundedFinite :: Size -> Static symbol a -> Either GenError (Static symbol a)
boundedFinite bound static = do
    bounded <- boundedStatic bound $ recursiveFromStatic static
    let outcomes = staticOutcomes bounded
        total = outcomeCardinality outcomes
        -- Size-major ranks are a prefix of the unbounded size-major order, so
        -- the original size index maps a bounded rank to its original rank.
        originalRank rank = do
            checkIndex total rank
            case sizeClassOf index rank of
                Nothing -> Left $ SelectionOutOfRange rank total
                Just (SizedRank size position) -> Right $ valueRank $ sizeClassSelect index size position
        -- A bounded rank keeps the weight of its original rank inside its
        -- size class.
        weight rank = do
            rank' <- originalRank rank
            maybe (Right 1) ($ rank') $ snd $ staticSampling static
        -- The bounded sampler gives a rank its weight divided by the number
        -- of members of the bounded language.
        select rank = do
            outcome <- outcomeSelect original =<< originalRank rank
            weight' <- weight rank
            pure outcome{outcomeMass = weight' / toRational total}
    pure
        bounded
            { staticOutcomes =
                outcomes
                    { outcomeSelect = select
                    , outcomeSizeSampling = (\(sampling, _) -> (sampling, weight)) <$> outcomeSizeSampling outcomes
                    }
            }
  where
    original = staticOutcomes static
    index = outcomeSizeIndex original

{- | A token that identifies one recursion in the probe flags.

A nested definition can reach the probe of an enclosing one, so each
recursion reads only its own token. Tokens need to differ only between
recursions that are nested in each other, and those have different body
functions. The result of a recursion does not depend on the value of its
token, only on which probes carry it.
-}
freshToken :: a -> Occurrence
freshToken body = unsafePerformIO $ body `seq` atomicModifyIORef' tokenSupply (\token -> (token + 1, Occurrence token))
{-# NOINLINE freshToken #-}

{- | The next free recursion token. The supply starts at the token after
'closedOccurrence', so no recursion gets the token of a closed probe.
-}
tokenSupply :: IORef Int
tokenSupply = unsafePerformIO $ newIORef $ closed + 1
  where
    Occurrence closed = closedOccurrence
{-# NOINLINE tokenSupply #-}
