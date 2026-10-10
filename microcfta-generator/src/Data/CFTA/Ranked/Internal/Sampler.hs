{- | Backend-independent value and rank sampling.

This module is an exposed internal module. The generator layers of
microcfta-generator use it directly. Its exports are not covered by the PVP
contract of the package.
-}
module Data.CFTA.Ranked.Internal.Sampler (
    GenBackend (..),
    Exact (..),
    Sampler (..),
    SampleIndex (..),
    atomicSampleIndex,
    boundedSampler,
    choiceMassSampleIndex,
    choiceSampleIndex,
    compileWeighted,
    emptySampleIndex,
    exactPmfAtSize,
    fixSampleIndex,
    integerMasses,
    mapSampleIndex,
    mapSampler,
    productMassSampleIndex,
    productSampleIndex,
    productSampler,
    uniformSampleIndex,
    uniformSampler,
) where

import Data.List (mapAccumL)
import qualified Data.Map.Strict as Map
import Data.Ratio (denominator, numerator)
import GHC.Arr (listArray, unsafeAt)

import Data.CFTA.Index (
    Cardinality (..),
    ClassRank (..),
    Rank (..),
    RankOffset,
    Size,
    Weight (..),
    countWeight,
    everyRank,
    nextOffset,
    offsetRank,
    pairRank,
 )
import Data.CFTA.Ranked.Internal.Decoder (RankedValue (..), SizeClass (..), offsetRankedValue)
import Data.CFTA.Ranked.Internal.Size (
    SizeIndex,
    countAtSize,
    sizeClassCounts,
    sizeClassSelect,
 )

-- | Operations a sampling backend provides. 'filterGen' serves adapters that retry a backend-native generator.
class (Applicative gen) => GenBackend gen where
    -- | Select a rank of a language with the given cardinality, in @[0, cardinality)@.
    selectInteger :: Cardinality -> gen Rank

    -- | Select a machine 'Int' in @[0, bound)@.
    selectInt :: Int -> gen Int
    selectInt bound = (\(Rank rank) -> fromInteger rank) <$> selectInteger (Cardinality $ toInteger bound)

    -- | Select one backend generator with a positive relative weight.
    frequencyGen :: [(Weight, gen a)] -> gen a

    {- | Select one of the weighted values through its compiled ticket table.

    The default draws one ticket and decodes it. A backend that enumerates
    outcomes reads the weights instead, so it gives one outcome for each value
    and not one for each ticket.
    -}
    selectWeighted :: [(Weight, a)] -> (Int, Int -> a) -> gen a
    selectWeighted _ (bound, decode) = decode <$> selectInt bound

    -- | Retry until the generated value satisfies a predicate.
    filterGen :: (a -> Bool) -> gen a -> gen a

-- | A finite exact interpretation of one sampler, for distribution checks.
newtype Exact a = Exact {runExact :: [(Rational, a)]}

instance Functor Exact where
    fmap transform (Exact outcomes) =
        Exact [(mass, transform value) | (mass, value) <- outcomes]

instance Applicative Exact where
    pure value = Exact [(1, value)]
    Exact functions <*> Exact values =
        Exact
            [ (functionMass * valueMass, function value)
            | (functionMass, function) <- functions
            , (valueMass, value) <- values
            ]

instance GenBackend Exact where
    selectInteger cardinality@(Cardinality count) =
        Exact
            [ (1 / fromInteger count, rank)
            | rank <- everyRank cardinality
            ]

    frequencyGen alternatives =
        Exact
            [ (toRational weight / toRational totalWeight * mass, value)
            | (weight, Exact outcomes) <- alternatives
            , (mass, value) <- outcomes
            ]
      where
        totalWeight = sum $ map fst alternatives

    -- One outcome for each value: enumerating the tickets would multiply the
    -- outcomes of a product by the ticket count of every draw.
    selectWeighted weighted _ =
        Exact [(toRational weight / toRational totalWeight, value) | (weight, value) <- weighted]
      where
        totalWeight = sum $ map fst weighted

    filterGen predicate (Exact outcomes)
        | acceptedMass <= 0 = Exact []
        | otherwise =
            Exact
                [ (mass / acceptedMass, value)
                | (mass, value) <- accepted
                ]
      where
        accepted = filter (predicate . snd) outcomes
        acceptedMass = sum $ map fst accepted

-- | Backend-independent plans for sampling a value, with or without its rank.
data Sampler a = Sampler
    { runValueSampler :: forall gen. (GenBackend gen) => gen a
    , runRankSampler :: forall gen. (GenBackend gen) => gen (RankedValue a)
    }

{- | The sampler for each recursive size class.

Its rank is a position in that class, not a global rank. The bounded sampler
adds the preceding size classes to recover the stable size-major rank.
-}
newtype SampleIndex a = SampleIndex
    { samplerAtSize :: Size -> Sampler a
    }

-- | Sample one value of the given size class.
runValueAtSize :: (GenBackend gen) => SampleIndex a -> Size -> gen a
runValueAtSize sampling = runValueSampler . samplerAtSize sampling

{- | Sample one value of the given size class with its rank. The rank is a
position in that size class.
-}
runRankAtSize :: (GenBackend gen) => SampleIndex a -> Size -> gen (RankedValue a)
runRankAtSize sampling = runRankSampler . samplerAtSize sampling

{- | Aggregate the exact value distribution of one recursive size class.

This interprets the sampler rather than its structural ranks, so weighted
finite choices closed with @atomic@ keep their declared probability. The
observer may enumerate a sampler's products and is intended for diagnostics,
not for large language hot paths.
-}
exactPmfAtSize :: (Ord a) => SampleIndex a -> Size -> [(a, Rational)]
exactPmfAtSize sampling size =
    Map.toAscList
        $ Map.fromListWith (+)
        $ [(value, mass) | (mass, value) <- runExact $ runValueAtSize sampling size]

-- | Map sampled values while keeping their ranks.
mapSampler :: (a -> b) -> Sampler a -> Sampler b
mapSampler transform sampler =
    Sampler
        (transform <$> runValueSampler sampler)
        (fmap transform <$> runRankSampler sampler)

-- | Sample uniformly with one selection, using a machine 'Int' when it fits.
uniformSampler :: Cardinality -> (Rank -> a) -> Sampler a
uniformSampler 1 valueAt = Sampler (pure $ valueAt 0) (pure $ RankedValue 0 (valueAt 0))
uniformSampler (Cardinality totalOutcomes) valueAt
    | totalOutcomes <= toInteger (maxBound :: Int) =
        let bound = fromInteger totalOutcomes
            rankOfInt = Rank . toInteger
            valueAtInt = valueAt . rankOfInt
         in Sampler
                (valueAtInt <$> selectInt bound)
                ((\index -> RankedValue (rankOfInt index) (valueAtInt index)) <$> selectInt bound)
uniformSampler totalOutcomes valueAt =
    Sampler
        (valueAt <$> selectInteger totalOutcomes)
        ((\rank -> RankedValue rank (valueAt rank)) <$> selectInteger totalOutcomes)

-- | Sample a product, composing ranks in mixed radix.
productSampler :: Cardinality -> Sampler (a -> b) -> Sampler a -> Sampler b
productSampler rightCardinality leftSampler rightSampler =
    Sampler
        (runValueSampler leftSampler <*> runValueSampler rightSampler)
        ( liftA2
            ( \(RankedValue leftRank partial) (RankedValue rightRank value) ->
                RankedValue (pairRank rightCardinality leftRank rightRank) (partial value)
            )
            (runRankSampler leftSampler)
            (runRankSampler rightSampler)
        )

-- | Uniformly sample a position from one counted size class.
uniformSampleIndex :: SizeIndex a -> SampleIndex a
uniformSampleIndex index =
    SampleIndex $ \size ->
        -- The ranks of this sampler are the positions in the size class.
        uniformSampler
            (countAtSize index size)
            (\(Rank position) -> rankedValue $ sizeClassSelect index size $ ClassRank position)

-- | Use one finite atomic sampler as the only size-one class.
atomicSampleIndex :: Sampler a -> SampleIndex a
atomicSampleIndex sampler =
    SampleIndex $ \size -> if size == 1 then sampler else wrongSize size
  where
    wrongSize size =
        error $
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Sampler.atomicSampleIndex: "
                <> "an atom has no members of size "
                <> show size

-- | A placeholder for an empty recursive language. It is never sampled.
emptySampleIndex :: SampleIndex a
emptySampleIndex =
    SampleIndex $ const unavailable
  where
    unavailable =
        error $
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Sampler.emptySampleIndex: "
                <> "an empty language has no members to sample"

-- | Map sampled values while keeping their size-class positions.
mapSampleIndex :: (a -> b) -> SampleIndex a -> SampleIndex b
mapSampleIndex transform sampling =
    SampleIndex $ mapSampler transform . samplerAtSize sampling

{- | How to choose among weighted alternatives.

The field is rank-2 for the same reason 'Sampler' is: one plan is built once
and then run at whatever backend the caller lowers to. It exists so that the
count-weighted and mass-weighted variants below are one function each instead
of two copies each.
-}
newtype Choose weight = Choose
    { runChoose :: forall gen a. (GenBackend gen) => [(weight, gen a)] -> gen a
    }

-- | Choose in proportion to structural member counts.
byCount :: Choose Weight
byCount = Choose chooseWeighted

-- | Choose in proportion to unnormalized probability masses.
byMass :: Choose Rational
byMass = Choose chooseMassWeighted

-- | One non-empty size split of a product.
data ProductPart = ProductPart
    { partBlock :: !Cardinality
    -- ^ Members of the product contributed by this split.
    , partOffset :: !RankOffset
    -- ^ Position of the split's first member within the size class.
    , partFunctionSize :: !Size
    , partArgumentSize :: !Size
    , partArgumentCount :: !Cardinality
    -- ^ Radix for composing the two positions into one.
    }

{- | Sample a product at one exact size, choosing among the size splits with
the supplied weights.

Sampling inside each side is delegated to that side, so an atomic sampler can
remain non-uniform without changing product counts or positions, and the
weights choose only between splits, never within one.
-}
productSampleIndexBy ::
    Choose weight ->
    (ProductPart -> weight) ->
    SizeIndex (a -> b) ->
    SampleIndex (a -> b) ->
    SizeIndex a ->
    SampleIndex a ->
    SampleIndex b
productSampleIndexBy choose weightOf indexF samplingF indexX samplingX =
    SampleIndex $ \size ->
        Sampler
            ( runChoose
                choose
                [ ( weightOf part
                  , liftA2
                        ($)
                        (runValueAtSize samplingF $ partFunctionSize part)
                        (runValueAtSize samplingX $ partArgumentSize part)
                  )
                | part <- productSampleParts indexF indexX size
                ]
            )
            ( runChoose
                choose
                [ ( weightOf part
                  , liftA2
                        (combine (partOffset part) (partArgumentCount part))
                        (runRankAtSize samplingF $ partFunctionSize part)
                        (runRankAtSize samplingX $ partArgumentSize part)
                  )
                | part <- productSampleParts indexF indexX size
                ]
            )
  where
    combine offset argumentCount (RankedValue functionPosition function) (RankedValue argumentPosition argument) =
        RankedValue (offsetRank offset $ pairRank argumentCount functionPosition argumentPosition) (function argument)

-- | Sample a product at one exact size, weighting splits by member count.
productSampleIndex ::
    SizeIndex (a -> b) ->
    SampleIndex (a -> b) ->
    SizeIndex a ->
    SampleIndex a ->
    SampleIndex b
productSampleIndex = productSampleIndexBy byCount (countWeight . partBlock)

{- | Sample a product whose two sides are conditioned key groups.

The mass functions give each group's unnormalized probability mass at one
size. They choose among size splits without changing structural rank offsets.
-}
productMassSampleIndex ::
    SizeIndex (a -> b) ->
    (Size -> Rational) ->
    SampleIndex (a -> b) ->
    SizeIndex a ->
    (Size -> Rational) ->
    SampleIndex a ->
    SampleIndex b
productMassSampleIndex indexF massF samplingF indexX massX samplingX =
    productSampleIndexBy byMass splitMass indexF samplingF indexX samplingX
  where
    splitMass part = massF (partFunctionSize part) * massX (partArgumentSize part)

-- | Every non-empty size split of a product, with its position offset.
productSampleParts ::
    SizeIndex (a -> b) ->
    SizeIndex a ->
    Size ->
    [ProductPart]
productSampleParts indexF indexX size = go 0 $ takeWhile ((< size) . fst) (sizeClassCounts indexF)
  where
    go _ [] = []
    go offset ((functionSize, functionCount) : rest)
        | block <= 0 = go offset rest
        | otherwise =
            ProductPart block offset functionSize argumentSize argumentCount
                : go (nextOffset offset block) rest
      where
        argumentSize = size - functionSize
        argumentCount = countAtSize indexX argumentSize
        block = functionCount * argumentCount

{- | Sample ordered alternatives at one exact size, choosing with the supplied
weights.

Rank offsets always come from the structural counts, whatever the weights are:
an alternative that is skipped because its weight is zero still occupies its
positions in the size class. The weight function is handed that count so it
never has to recompute it.
-}
choiceSampleIndexBy ::
    Choose weight ->
    [(SizeIndex a, Cardinality -> Size -> Maybe weight, SampleIndex a)] ->
    SampleIndex a
choiceSampleIndexBy choose alternatives =
    SampleIndex $ \size ->
        Sampler
            ( runChoose
                choose
                [ (weight, runValueAtSize sampling size)
                | (weight, _, sampling) <- parts size
                ]
            )
            ( runChoose
                choose
                [ (weight, offsetRankedValue offset <$> runRankAtSize sampling size)
                | (weight, offset, sampling) <- parts size
                ]
            )
  where
    parts size = go 0 alternatives
      where
        go _ [] = []
        go offset ((index, weightAt, sampling) : rest) =
            case weightAt count size of
                Just weight -> (weight, offset, sampling) : go (nextOffset offset count) rest
                Nothing -> go (nextOffset offset count) rest
          where
            count = countAtSize index size

-- | Sample ordered alternatives at one exact size, weighted by member count.
choiceSampleIndex :: [(SizeIndex a, SampleIndex a)] -> SampleIndex a
choiceSampleIndex alternatives =
    choiceSampleIndexBy
        byCount
        [(index, liveCount, sampling) | (index, sampling) <- alternatives]
  where
    liveCount count _ = if count > 0 then Just (countWeight count) else Nothing

{- | Sample alternatives conditioned on one retained key.

Structural counts still define rank offsets. The supplied masses choose the
alternative, so regrouping does not erase a declared atomic distribution.
-}
choiceMassSampleIndex ::
    [(SizeIndex a, Size -> Rational, SampleIndex a)] ->
    SampleIndex a
choiceMassSampleIndex alternatives =
    choiceSampleIndexBy
        byMass
        [(index, liveMass massAtSize, sampling) | (index, massAtSize, sampling) <- alternatives]
  where
    liveMass massAtSize count size
        | count <= 0 = Nothing
        | mass <= 0 = Nothing
        | otherwise = Just mass
      where
        mass = massAtSize size

-- | Tie a guarded recursive sampler alongside its recursive size index.
fixSampleIndex :: (SampleIndex a -> SampleIndex a) -> SampleIndex a
fixSampleIndex build = sampling
  where
    sampling = build sampling

-- | Sample one bounded size class, then recover its global size-major rank.
boundedSampler :: [SizeClass a] -> SampleIndex a -> Sampler a
boundedSampler classes sampling =
    Sampler
        ( chooseWeighted
            [ (countWeight count, runValueAtSize sampling size)
            | SizeClass{classSize = size, classCardinality = count} <- classes
            ]
        )
        ( chooseWeighted
            [ (countWeight count, offsetRankedValue offset <$> runRankAtSize sampling size)
            | (size, count, offset) <- offsetClasses 0 classes
            ]
        )
  where
    offsetClasses _ [] = []
    offsetClasses offset (SizeClass{classSize = size, classCardinality = count} : rest) =
        (size, count, offset) : offsetClasses (nextOffset offset count) rest

-- | Avoid a random branch selection when only one branch is live.
chooseWeighted :: (GenBackend gen) => [(Weight, gen a)] -> gen a
chooseWeighted [(_, generated)] = generated
chooseWeighted alternatives@(_ : _ : _) = frequencyGen alternatives
chooseWeighted [] =
    error $
        "microcfta-generator bug in Data.CFTA.Ranked.Internal.Sampler.chooseWeighted: "
            <> "no live alternative"

-- | Choose from exact rational masses after removing their common scale.
chooseMassWeighted :: (GenBackend gen) => [(Rational, gen a)] -> gen a
chooseMassWeighted [(mass, generated)]
    | mass > 0 = generated
chooseMassWeighted alternatives =
    case integerMasses [(mass, generated) | (mass, generated) <- alternatives, mass > 0] of
        [(_, generated)] -> generated
        weighted@(_ : _ : _) -> frequencyGen weighted
        [] ->
            error $
                "microcfta-generator bug in Data.CFTA.Ranked.Internal.Sampler.chooseMassWeighted: "
                    <> "no positive mass"

{- | Convert rational masses to the smallest equivalent integer weights.

Precondition: every mass is positive. That is what makes the common factor at
least one, so the final division is well defined.
-}
integerMasses :: [(Rational, a)] -> [(Weight, a)]
integerMasses outcomes =
    zip
        (map (Weight . (`div` commonFactor)) unscaled)
        (map snd outcomes)
  where
    unscaled =
        [ numerator mass * (commonDenominator `div` denominator mass)
        | mass <- masses
        ]
      where
        commonDenominator = foldl lcm 1 $ map denominator masses

        masses = map fst outcomes
    commonFactor = foldl gcd 0 unscaled

{- | Compile positive integer tickets when their total fits a machine 'Int'.

Larger ticket spaces keep their existing compositional sampler.
-}
compileWeighted :: [(Weight, a)] -> Maybe (Int, Int -> a)
compileWeighted weighted
    | totalWeight > 0
    , totalWeight <= toInteger (maxBound :: Int) =
        let bound = fromInteger totalWeight
            entries = snd $ mapAccumL compileGroup 0 grouped
            lastIndex = length entries - 1
            table = listArray (0, lastIndex) entries
            -- \| Search the array without allocating a lookup result per ticket.
            lookupTicket ticket = go 0 lastIndex
              where
                go low high
                    | low == high =
                        let (lowerBound, (ticketWidth, values)) = unsafeAt table low
                         in unsafeAt values $ (ticket - lowerBound) `quot` ticketWidth
                    | otherwise =
                        let midpoint = low + (high - low + 1) `quot` 2
                            (lowerBound, _) = unsafeAt table midpoint
                         in if ticket < lowerBound
                                then go low (midpoint - 1)
                                else go midpoint high
         in Just (bound, lookupTicket)
    | otherwise = Nothing
  where
    Weight totalWeight = sum $ map fst weighted
    -- Prepending each singleton keeps grouping linear. Ticket order is
    -- private; every payload still carries its original structural rank.
    grouped =
        Map.toAscList $
            Map.fromListWith
                (<>)
                [(weight, [value]) | (weight, value) <- weighted]

    compileGroup lowerBound (Weight weight, values) =
        let !ticketWidth = fromInteger weight
            !upperBound = lowerBound + ticketWidth * length values
            !valueTable = listArray (0, length values - 1) values
         in ( upperBound
            , (lowerBound, (ticketWidth, valueTable))
            )
