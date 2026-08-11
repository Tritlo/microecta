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
    fromGen,
    toGen,
    toGenEither,
    toGenWithRank,
    toGenWithRankEither,
    forAll,
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

-- | Merge all retained groups while preserving their probability masses.
ungroup :: Grouped key a -> ECTAGen a
ungroup = ECTA.ungroup

-- | Choose one generator with the supplied positive relative weight.
frequency :: [(Integer, ECTAGen a)] -> ECTAGen a
frequency = ECTA.frequency

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
    | Just (QuickCheckBackend direct) <- ECTA.lowerUniform generator = direct
    | otherwise =
        either (error . ("ECTAGen: " <>) . show) id <$> toGenEither generator

-- | Sample a transparent generator together with its stable replay rank.
toGenWithRank :: ECTAGen a -> QC.Gen (Integer, a)
toGenWithRank generator
    | Just (QuickCheckBackend direct) <- ECTA.lowerUniformWithRank generator = direct
    | otherwise =
        either (error . ("ECTAGen: " <>) . show) id
            <$> toGenWithRankEither generator

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
forAll generator prop =
    QC.forAllShrinkShow
        (toGenWithRank generator)
        shrinkCandidates
        showRanked
        (prop . snd)
  where
    shrinkCandidates (rank, _) = smaller <> structural
      where
        smaller = take smallerMemberLimit (smallerMembers generator rank)
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
