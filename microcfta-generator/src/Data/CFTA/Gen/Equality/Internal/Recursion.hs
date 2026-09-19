{- | The recursive generator builders and the bound that closes them.

Each builder ties its own language through a fixpoint: counts, masses,
sampling, and the @Mu@ support are solved together, and each pass reads the
definition rather than its language. 'upToSize' turns the result back into a
finite generator with the ranks the recursive language already gave it.
-}
module Data.CFTA.Gen.Equality.Internal.Recursion (
    atomic,
    recur,
    recurGrouped,
    upToSize,
) where

import Control.Monad (void, when)
import Data.Either (fromRight)
import qualified Data.Map.Strict as Map

import Data.CFTA.Equality (Node (EmptyNode), createMu, numNestedMu)
import Data.CFTA.Gen.Equality.Internal
import Data.CFTA.Gen.Equality.Internal.Inspection
import Data.CFTA.Gen.Equality.Internal.Support (familyNodeWith, keySymbol, restrictToKeyWith)
import Data.CFTA.Gen.Equality.Internal.Types
import Data.CFTA.Ranked.Internal.Sampler
import Data.CFTA.Ranked.Internal.Size (
    choiceIndex,
    fixIndex,
    isUnguarded,
    minimumMemberSize,
    probeIndex,
    probeIndexWithMinimum,
    usesOccurrence,
    withMinimumMemberSize,
 )

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
atomic :: ECTAGen a -> ECTAGen a
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
recur :: (ECTAGen a -> ECTAGen a) -> ECTAGen a
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
    (Grouped key a -> Grouped key a) ->
    Grouped key a
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
    namesBySymbol = Map.fromList [(keySymbol $ positionOf key, nameForKey key) | key <- keys]
    labelKey symbol = InspectionSymbol symbol $ Map.findWithDefault Nothing symbol namesBySymbol
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
upToSize :: Int -> ECTAGen a -> ECTAGen a
upToSize bound (Cyclic result) =
    Transparent $ do
        recursive <- result
        if recursiveOccurrence recursive
            then Left BoundedRecursiveOccurrence
            else boundedStatic bound recursive
upToSize _ generator = generator
