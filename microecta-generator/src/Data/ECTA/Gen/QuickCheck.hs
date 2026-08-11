{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | QuickCheck integration for indexed ECTA generators.
module Data.ECTA.Gen.QuickCheck (
    Indexed (..),
    ECTAGen,
    Grouped,
    Sig (..),
    sigResult,
    Args (..),
    ECTAGenError (..),
    fromIndexed,
    elements,
    groupBy,
    regroupBy,
    mapWithKey,
    sizes,
    atKey,
    apply,
    frequencies,
    oneofGrouped,
    ungroup,
    frequency,
    oneof,
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
    fromECTA,
    recur,
    recurGrouped,
    upToSize,
    fromGen,
    toGen,
    toGenEither,
    toGenWithRank,
    toGenWithRankEither,
    forAll,
    forAllWithLimit,
    sized,

    -- * Qualified do-notation
    module Data.ECTA.Gen.Do,
) where

import Data.List (mapAccumL, sortOn)
import Data.Map.Strict (Map)
import Data.Ord (Down (..))
import qualified Test.QuickCheck as QC

import Data.ECTA (Node)
import Data.ECTA.Gen (
    Args (..),
    ECTAGenError (..),
    Indexed (..),
    On (..),
    Sig (..),
    sigResult,
 )
import qualified Data.ECTA.Gen as ECTA
import Data.ECTA.Gen.Do
import Data.ECTA.Term (Term)

-- | The private wrapper avoids an orphan backend instance for 'QC.Gen'.
newtype QuickCheckBackend a = QuickCheckBackend (QC.Gen a)
    deriving newtype (Functor, Applicative)

instance ECTA.GenBackend QuickCheckBackend where
    selectInteger bound =
        QuickCheckBackend $ QC.chooseInteger (0, bound - 1)

    selectInt bound =
        QuickCheckBackend $ QC.chooseInt (0, bound - 1)

    frequencyGen alternatives =
        -- Ranked branches already carry their offsets, so sampling can put
        -- likely branches first without changing rank order.
        let ordered = sortOn (Down . fst) alternatives
            (total, cumulative) = mapAccumL accumulateWeight 0 ordered
         in QuickCheckBackend $ do
                selected <- QC.chooseInteger (0, total - 1)
                pick selected cumulative
      where
        accumulateWeight total (weight, generated) =
            let upperBound = total + weight
             in (upperBound, (upperBound, generated))

        pick _ [] = error "frequencyGen: impossible empty alternatives"
        pick selected ((upperBound, QuickCheckBackend generated) : remaining)
            | selected < upperBound = generated
            | otherwise = pick selected remaining

    filterGen predicate (QuickCheckBackend generated) =
        QuickCheckBackend $ generated `QC.suchThat` predicate

-- | An indexed ECTA generator with QuickCheck as its opaque backend.
type ECTAGen = ECTA.ECTAGen QuickCheckBackend

-- | An ECTA generator classified by a projected key used to match ECTA paths.
type Grouped key = ECTA.Grouped QuickCheckBackend key

-- | Lift one finite indexed source into transparent ECTA structure.
fromIndexed :: Indexed a -> ECTAGen a
fromIndexed = ECTA.fromIndexed

-- | Choose uniformly from a finite non-empty list.
elements :: [a] -> ECTAGen a
elements = ECTA.elements

{- | Read an ECTA as a generator of the terms it accepts.

The automaton is the support and members are counted by size, so this draws
uniformly from the terms of at most the current QuickCheck size. Automata
whose edges carry equality constraints are rejected.
-}
fromECTA :: Node -> ECTAGen Term
fromECTA = ECTA.fromECTA

{- | Build a recursive generator from its own language.

The argument receives the generator being defined, so a language can refer
to itself. 'toGen' and 'forAll' bound it by QuickCheck's size parameter,
drawing uniformly from the members of at most that size; 'upToSize' bounds
it explicitly. Recursion must be guarded by '<*>', and 'frequency'
alternatives around a recursive occurrence must carry equal weights.
-}
recur :: (ECTAGen a -> ECTAGen a) -> ECTAGen a
recur = ECTA.recur

{- | Build a recursive grouped family from its own languages.

The key set is solved first, then the languages are tied over it. All keys
share one @Mu@ node whose cycle carries the keyed joins' equality
constraints; 'ungroup' and 'atKey' are the exits into an ordinary recursive
generator. Recursion must be guarded by 'apply', and 'frequencies'
alternatives around a recursive occurrence must carry equal weights.
-}
recurGrouped :: (Ord key) => (Grouped key a -> Grouped key a) -> Grouped key a
recurGrouped = ECTA.recurGrouped

{- | Bound a generator to the members of size at most the given bound.

Size is the number of source choices in a member. Ranks are unchanged, so a
counterexample found under one bound replays under any other.
-}
upToSize :: Int -> ECTAGen a -> ECTAGen a
upToSize = ECTA.upToSize

{- | Classify a transparent generator's outcomes by a projected key.

Building the groups enumerates the generator's outcomes once. Opaque
generators cannot be grouped.
-}
groupBy :: (Ord key) => (a -> key) -> ECTAGen a -> Grouped key a
groupBy = ECTA.groupBy

-- | Reclassify groups without enumerating their values.
regroupBy :: (Ord newKey) => (oldKey -> newKey) -> Grouped oldKey a -> Grouped newKey a
regroupBy = ECTA.regroupBy

-- | Map group values with access to their retained key.
mapWithKey :: (key -> a -> b) -> Grouped key a -> Grouped key b
mapWithKey = ECTA.mapWithKey

-- | Return the exact cardinality of each retained group.
sizes :: Grouped key a -> Either ECTAGenError (Map key Integer)
sizes = ECTA.sizes

-- | Select one retained group as an ordinary conditional generator.
atKey :: (Ord key) => key -> Grouped key a -> ECTAGen a
atKey = ECTA.atKey

{- | Apply a generated operation of any arity to one argument family per
signature component.

The operation family must already hold functions consuming the 'Args' chain
left to right; use 'fmap' to attach a compiling function.
-}
apply ::
    (Ord resultKey) =>
    Grouped (Sig argKeys resultKey) operation ->
    Args QuickCheckBackend argKeys operation result ->
    Grouped resultKey result
apply = ECTA.apply

{- | Choose among grouped generators with positive relative weights,
group by group.
-}
frequencies :: (Ord key) => [(Integer, Grouped key a)] -> Grouped key a
frequencies = ECTA.frequencies

{- | Choose uniformly among grouped generators, group by group.

'frequencies' with equal weights, which is the only shape a recursive
family admits.
-}
oneofGrouped :: (Ord key) => [Grouped key a] -> Grouped key a
oneofGrouped = ECTA.oneofGrouped

-- | Merge all retained groups while preserving their probability masses.
ungroup :: Grouped key a -> ECTAGen a
ungroup = ECTA.ungroup

-- | Choose one generator with the supplied positive relative weight.
frequency :: [(Integer, ECTAGen a)] -> ECTAGen a
frequency = ECTA.frequency

{- | Choose uniformly among generators.

Every alternative is equally likely, whatever the size of its language. In
a recursive definition this is the shape to reach for: weights around a
recursive occurrence are rejected.
-}
oneof :: [ECTAGen a] -> ECTAGen a
oneof = ECTA.oneof

-- | Generate two values whose projected keys agree.
match ::
    On left right ->
    ECTAGen left ->
    ECTAGen right ->
    ECTAGen (left, right)
match = ECTA.match

-- | Return the ECTA support of a fully transparent generator.
support :: ECTAGen a -> Either ECTAGenError Node
support = ECTA.support

-- | Return the exact number of ranks in a transparent generator.
cardinality :: ECTAGen a -> Either ECTAGenError Integer
cardinality = ECTA.cardinality

-- | The number of members of one size, for any inspectable generator.
countAtSize :: ECTAGen a -> Int -> Either ECTAGenError Integer
countAtSize = ECTA.countAtSize

-- | Decode one stable rank from a transparent generator.
unrank :: ECTAGen a -> Integer -> Either ECTAGenError a
unrank = ECTA.unrank

-- | Structural shrink candidates for one rank of a transparent generator.
shrinkRank :: ECTAGen a -> Integer -> [Integer]
shrinkRank = ECTA.shrinkRank

{- | Every member structurally smaller than the given rank's member, in size
order, as replayable rank and value. The stream is lazy; cap it before use.
-}
smallerMembers :: ECTAGen a -> Integer -> [(Integer, a)]
smallerMembers = ECTA.smallerMembers

-- | The number of source choices in the member a rank decodes to.
sizeOfRank :: ECTAGen a -> Integer -> Maybe Int
sizeOfRank = ECTA.sizeOfRank

-- | Count ranked outcomes by a projected key.
countBy :: (Ord key) => (a -> key) -> ECTAGen a -> Either ECTAGenError (Map key Integer)
countBy = ECTA.countBy

-- | Aggregate the exact PMF of a fully transparent generator.
pmf :: (Ord a) => ECTAGen a -> Either ECTAGenError [(a, Rational)]
pmf = ECTA.pmf

-- | Embed an ordinary QuickCheck generator as an opaque region.
fromGen :: QC.Gen a -> ECTAGen a
fromGen = ECTA.fromBackend . QuickCheckBackend

-- | Sample while retaining structured generator errors.
toGenEither :: ECTAGen a -> QC.Gen (Either ECTAGenError a)
toGenEither generator = case ECTA.lower generator of
    QuickCheckBackend generated -> generated

-- | Sample a transparent generator while retaining its stable rank and errors.
toGenWithRankEither :: ECTAGen a -> QC.Gen (Either ECTAGenError (Integer, a))
toGenWithRankEither generator = case ECTA.lowerWithRank generator of
    QuickCheckBackend generated -> generated

-- | Sample through the generator type expected by QuickCheck.
toGen :: ECTAGen a -> QC.Gen a
toGen generator
    | ECTA.isRecursive generator = QC.sized $ \size -> bounded !! max 0 size
    | Just (QuickCheckBackend direct) <- ECTA.lowerUniform generator = direct
    | otherwise =
        either (error . ("ECTAGen: " <>) . show) id <$> toGenEither generator
  where
    bounded = [toGen (ECTA.upToSize (max 1 size) generator) | size <- [0 ..]]

-- | Sample a transparent generator together with its stable replay rank.
toGenWithRank :: ECTAGen a -> QC.Gen (Integer, a)
toGenWithRank generator
    | ECTA.isRecursive generator = QC.sized $ \size -> bounded !! max 0 size
    | Just (QuickCheckBackend direct) <- ECTA.lowerUniformWithRank generator = direct
    | otherwise =
        either (error . ("ECTAGen: " <>) . show) id
            <$> toGenWithRankEither generator
  where
    bounded = [toGenWithRank (ECTA.upToSize (max 1 size) generator) | size <- [0 ..]]

{- | Check a property over a transparent generator, shrinking to the
smallest failing member.

Shrink candidates first search every structurally smaller member in size
order, capped at 'smallerMemberLimit', so the result is the globally
smallest failing member whenever the search reaches one. Structural
component shrinking through 'shrinkRank' follows as a fallback, restricted
to candidates of at most the current size so shrinking always terminates.
Every candidate is a member of the generated language, and the failing rank
is printed with the counterexample, so 'unrank' replays it
deterministically.
-}
forAll :: (QC.Testable prop, Show a) => ECTAGen a -> (a -> prop) -> QC.Property
forAll = forAllWithLimit smallerMemberLimit

{- | 'forAll' with an explicit cap on the smaller-member search per shrink
step.

The cap bounds the members tested when the current failing member is
already minimal. When the language holds more small members than
'smallerMemberLimit' — command sequences, for example, accumulate many
short members — the default search never reaches the failing sizes and
structural shrinking alone cannot remove members in the middle of a
product. Raising the cap past the number of passing smaller members
restores the globally smallest failing member at the cost of testing that
many members per shrink step.
-}
forAllWithLimit ::
    (QC.Testable prop, Show a) => Int -> ECTAGen a -> (a -> prop) -> QC.Property
forAllWithLimit limit generator prop =
    QC.forAllShrinkShow
        (toGenWithRank generator)
        shrinkCandidates
        showRanked
        (prop . snd)
  where
    shrinkCandidates (rank, _) = smaller <> structural
      where
        smaller = take limit (smallerMembers generator rank)
        currentSize = sizeOfRank generator rank
        structural =
            [ (candidate, value)
            | candidate <- shrinkRank generator rank
            , sizeOfRank generator candidate <= currentSize
            , Right value <- [unrank generator candidate]
            ]

    showRanked (rank, value) = "rank " <> show rank <> ": " <> show value

{- | 'forAll' tests at most this many structurally smaller members per shrink
step before falling back to component shrinking.
-}
smallerMemberLimit :: Int
smallerMemberLimit = 1000

{- | Build the generator from QuickCheck's size parameter.

The generators for every size are built once and shared across samples, so a
layered generator is not reconstructed on every draw.
-}
sized :: (Int -> ECTAGen a) -> QC.Gen a
sized build = QC.sized $ \size -> toGen $ towers !! max 0 size
  where
    towers = map build [0 ..]
