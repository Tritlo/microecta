-- | Backend-independent value and rank sampling.
module Data.ECTA.Gen.Internal.Sampler (
    GenBackend (..),
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
import GHC.Arr (Array, listArray, unsafeAt)

import Data.ECTA.Gen.Internal.Size (
    SizeIndex,
    countAtSize,
    sizeClassSelect,
 )

-- | Backend operations needed only when sampling or crossing an opaque region.
class (Applicative gen) => GenBackend gen where
    -- | Select an integer in @[0, bound)@.
    selectInteger :: Integer -> gen Integer

    -- | Select a machine 'Int' in @[0, bound)@.
    selectInt :: Int -> gen Int
    selectInt bound = fromInteger <$> selectInteger (toInteger bound)

    -- | Select one backend generator with a positive relative weight.
    frequencyGen :: [(Integer, gen a)] -> gen a

    -- | Retry until the generated value satisfies a predicate.
    filterGen :: (a -> Bool) -> gen a -> gen a

-- | A finite exact interpretation of one sampler.
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
    selectInteger bound =
        Exact
            [ (1 / fromInteger bound, index)
            | index <- [0 .. bound - 1]
            ]

    frequencyGen alternatives =
        Exact
            [ (fromInteger weight / fromInteger totalWeight * mass, value)
            | (weight, Exact outcomes) <- alternatives
            , (mass, value) <- outcomes
            ]
      where
        totalWeight = sum $ map fst alternatives

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
    , runRankSampler :: forall gen. (GenBackend gen) => gen (Integer, a)
    }

{- | The sampler for each recursive size class.

Its rank is a position in that class, not a global rank. The bounded sampler
adds the preceding size classes to recover the stable size-major rank.
-}
newtype SampleIndex a = SampleIndex
    { samplerAtSize :: Int -> Sampler a
    }

runValueAtSize :: (GenBackend gen) => SampleIndex a -> Int -> gen a
runValueAtSize sampling = runValueSampler . samplerAtSize sampling

runRankAtSize :: (GenBackend gen) => SampleIndex a -> Int -> gen (Integer, a)
runRankAtSize sampling = runRankSampler . samplerAtSize sampling

{- | Aggregate the exact value distribution of one recursive size class.

This interprets the sampler rather than its structural ranks, so weighted
finite choices closed with @atomic@ keep their declared probability. The
observer may enumerate a sampler's products and is intended for diagnostics,
not for large language hot paths.
-}
exactPmfAtSize :: (Ord a) => SampleIndex a -> Int -> [(a, Rational)]
exactPmfAtSize sampling size =
    Map.toAscList $
        Map.fromListWith (+) $
            [(value, mass) | (mass, value) <- runExact $ runValueAtSize sampling size]

-- | Map sampled values while keeping their ranks.
mapSampler :: (a -> b) -> Sampler a -> Sampler b
mapSampler transform sampler =
    Sampler
        (transform <$> runValueSampler sampler)
        ( (\(rank, value) -> (rank, transform value))
            <$> runRankSampler sampler
        )

-- | Sample uniformly with one selection, using a machine 'Int' when it fits.
uniformSampler :: Integer -> (Integer -> a) -> Sampler a
uniformSampler 1 valueAt = Sampler (pure $ valueAt 0) (pure (0, valueAt 0))
uniformSampler totalOutcomes valueAt
    | totalOutcomes <= toInteger (maxBound :: Int) =
        let bound = fromInteger totalOutcomes
            valueAtInt = valueAt . toInteger
         in Sampler
                (valueAtInt <$> selectInt bound)
                ((\index -> (toInteger index, valueAtInt index)) <$> selectInt bound)
uniformSampler totalOutcomes valueAt =
    Sampler
        (valueAt <$> selectInteger totalOutcomes)
        ((\index -> (index, valueAt index)) <$> selectInteger totalOutcomes)

-- | Sample a product, composing ranks in mixed radix.
productSampler :: Integer -> Sampler (a -> b) -> Sampler a -> Sampler b
productSampler rightCardinality leftSampler rightSampler =
    Sampler
        (runValueSampler leftSampler <*> runValueSampler rightSampler)
        ( liftA2
            ( \(leftIndex, partial) (rightIndex, value) ->
                (leftIndex * rightCardinality + rightIndex, partial value)
            )
            (runRankSampler leftSampler)
            (runRankSampler rightSampler)
        )

-- | Uniformly sample a position from one counted size class.
uniformSampleIndex :: SizeIndex a -> SampleIndex a
uniformSampleIndex index =
    SampleIndex $ \size ->
        uniformSampler
            (countAtSize index size)
            (snd . sizeClassSelect index size)

-- | Use one finite atomic sampler as the only size-one class.
atomicSampleIndex :: Sampler a -> SampleIndex a
atomicSampleIndex sampler =
    SampleIndex $ \size -> if size == 1 then sampler else wrongSize size
  where
    wrongSize size =
        error $
            "microecta-generator bug in Data.ECTA.Gen.Internal.atomicSampleIndex: "
                <> "an atom has no members of size "
                <> show size

-- | A placeholder for an empty recursive language. It is never sampled.
emptySampleIndex :: SampleIndex a
emptySampleIndex =
    SampleIndex $ const unavailable
  where
    unavailable =
        error $
            "microecta-generator bug in Data.ECTA.Gen.Internal.emptySampleIndex: "
                <> "an empty language has no members to sample"

-- | Map sampled values while keeping their size-class positions.
mapSampleIndex :: (a -> b) -> SampleIndex a -> SampleIndex b
mapSampleIndex transform sampling =
    SampleIndex $ mapSampler transform . samplerAtSize sampling

{- | Sample a product at one exact size.

Size splits keep their count-based probability. Sampling inside each side is
delegated to that side, so an atomic sampler can remain non-uniform without
changing product counts or positions.
-}
productSampleIndex ::
    SizeIndex (a -> b) ->
    SampleIndex (a -> b) ->
    SizeIndex a ->
    SampleIndex a ->
    SampleIndex b
productSampleIndex indexF samplingF indexX samplingX =
    SampleIndex $ \size ->
        Sampler
            ( chooseWeighted
                [ ( block
                  , liftA2
                        ($)
                        (runValueAtSize samplingF functionSize)
                        (runValueAtSize samplingX argumentSize)
                  )
                | (block, _, functionSize, argumentSize, _) <-
                    productSampleParts indexF indexX size
                ]
            )
            ( chooseWeighted
                [ ( block
                  , liftA2
                        (combine offset argumentCount)
                        (runRankAtSize samplingF functionSize)
                        (runRankAtSize samplingX argumentSize)
                  )
                | (block, offset, functionSize, argumentSize, argumentCount) <-
                    productSampleParts indexF indexX size
                ]
            )
  where
    combine offset argumentCount (functionPosition, function) (argumentPosition, argument) =
        ( offset + functionPosition * argumentCount + argumentPosition
        , function argument
        )

{- | Sample a product whose two sides are conditioned key groups.

The mass functions give each group's unnormalized probability mass at one
size. They choose among size splits without changing structural rank offsets.
-}
productMassSampleIndex ::
    SizeIndex (a -> b) ->
    (Int -> Rational) ->
    SampleIndex (a -> b) ->
    SizeIndex a ->
    (Int -> Rational) ->
    SampleIndex a ->
    SampleIndex b
productMassSampleIndex indexF massF samplingF indexX massX samplingX =
    SampleIndex $ \size ->
        Sampler
            ( chooseMassWeighted
                [ ( massF functionSize * massX argumentSize
                  , liftA2
                        ($)
                        (runValueAtSize samplingF functionSize)
                        (runValueAtSize samplingX argumentSize)
                  )
                | (_, _, functionSize, argumentSize, _) <-
                    productSampleParts indexF indexX size
                ]
            )
            ( chooseMassWeighted
                [ ( massF functionSize * massX argumentSize
                  , liftA2
                        (combine offset argumentCount)
                        (runRankAtSize samplingF functionSize)
                        (runRankAtSize samplingX argumentSize)
                  )
                | (_, offset, functionSize, argumentSize, argumentCount) <-
                    productSampleParts indexF indexX size
                ]
            )
  where
    combine offset argumentCount (functionPosition, function) (argumentPosition, argument) =
        ( offset + functionPosition * argumentCount + argumentPosition
        , function argument
        )

-- | Every non-empty size split of a product, with its position offset.
productSampleParts ::
    SizeIndex (a -> b) ->
    SizeIndex a ->
    Int ->
    [(Integer, Integer, Int, Int, Integer)]
productSampleParts indexF indexX size = go 0 [1 .. size - 1]
  where
    go _ [] = []
    go offset (functionSize : rest)
        | block <= 0 = go offset rest
        | otherwise =
            (block, offset, functionSize, argumentSize, argumentCount)
                : go (offset + block) rest
      where
        argumentSize = size - functionSize
        functionCount = countAtSize indexF functionSize
        argumentCount = countAtSize indexX argumentSize
        block = functionCount * argumentCount

-- | Sample ordered alternatives at one exact size.
choiceSampleIndex :: [(SizeIndex a, SampleIndex a)] -> SampleIndex a
choiceSampleIndex alternatives =
    SampleIndex $ \size ->
        Sampler
            ( chooseWeighted
                [ (count, runValueAtSize sampling size)
                | (count, _, sampling) <- choiceSampleParts size alternatives
                ]
            )
            ( chooseWeighted
                [ ( count
                  , (\(position, value) -> (offset + position, value))
                        <$> runRankAtSize sampling size
                  )
                | (count, offset, sampling) <- choiceSampleParts size alternatives
                ]
            )

{- | Sample alternatives conditioned on one retained key.

Structural counts still define rank offsets. The supplied masses choose the
alternative, so regrouping does not erase a declared atomic distribution.
-}
choiceMassSampleIndex ::
    [(SizeIndex a, Int -> Rational, SampleIndex a)] ->
    SampleIndex a
choiceMassSampleIndex alternatives =
    SampleIndex $ \size ->
        Sampler
            ( chooseMassWeighted
                [ (mass, runValueAtSize sampling size)
                | (mass, _, sampling) <- parts size
                ]
            )
            ( chooseMassWeighted
                [ ( mass
                  , (\(position, value) -> (offset + position, value))
                        <$> runRankAtSize sampling size
                  )
                | (mass, offset, sampling) <- parts size
                ]
            )
  where
    parts size = go 0 alternatives
      where
        go _ [] = []
        go offset ((index, massAtSize, sampling) : rest)
            | count <= 0 = go offset rest
            | mass <= 0 = go (offset + count) rest
            | otherwise =
                (mass, offset, sampling) : go (offset + count) rest
          where
            count = countAtSize index size
            mass = massAtSize size

-- | Every non-empty alternative at one size, with its position offset.
choiceSampleParts ::
    Int ->
    [(SizeIndex a, SampleIndex a)] ->
    [(Integer, Integer, SampleIndex a)]
choiceSampleParts size = go 0
  where
    go _ [] = []
    go offset ((index, sampling) : rest)
        | count <= 0 = go offset rest
        | otherwise = (count, offset, sampling) : go (offset + count) rest
      where
        count = countAtSize index size

-- | Tie a guarded recursive sampler alongside its recursive size index.
fixSampleIndex :: (SampleIndex a -> SampleIndex a) -> SampleIndex a
fixSampleIndex build = sampling
  where
    sampling = build sampling

-- | Sample one bounded size class, then recover its global size-major rank.
boundedSampler ::
    [(Int, Integer, Integer -> a, Int -> a)] ->
    SampleIndex a ->
    Sampler a
boundedSampler classes sampling =
    Sampler
        ( chooseWeighted
            [ (count, runValueAtSize sampling size)
            | (size, count, _, _) <- classes
            ]
        )
        ( chooseWeighted
            [ ( count
              , (\(position, value) -> (offset + position, value))
                    <$> runRankAtSize sampling size
              )
            | (size, count, offset) <- offsetClasses 0 classes
            ]
        )
  where
    offsetClasses _ [] = []
    offsetClasses offset ((size, count, _, _) : rest) =
        (size, count, offset) : offsetClasses (offset + count) rest

-- | Avoid a random branch selection when only one branch is live.
chooseWeighted :: (GenBackend gen) => [(Integer, gen a)] -> gen a
chooseWeighted [(_, generated)] = generated
chooseWeighted alternatives@(_ : _ : _) = frequencyGen alternatives
chooseWeighted [] =
    error $
        "microecta-generator bug in Data.ECTA.Gen.Internal.chooseWeighted: "
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
                "microecta-generator bug in Data.ECTA.Gen.Internal.chooseMassWeighted: "
                    <> "no positive mass"

-- | Convert positive rational masses to the smallest integer ticket space.
integerMasses :: [(Rational, a)] -> [(Integer, a)]
integerMasses outcomes =
    zip
        (map (`div` commonFactor) unscaled)
        (map snd outcomes)
  where
    masses = map fst outcomes
    commonDenominator = foldl lcm 1 $ map denominator masses
    unscaled =
        [ numerator mass * (commonDenominator `div` denominator mass)
        | mass <- masses
        ]
    commonFactor = foldl gcd 0 unscaled

{- | Compile positive integer tickets when their total fits a machine 'Int'.

Larger ticket spaces keep their existing compositional sampler.
-}
compileWeighted :: [(Integer, a)] -> Maybe (Int, Int -> a)
compileWeighted weighted
    | totalWeight > 0
    , totalWeight <= toInteger (maxBound :: Int) =
        let bound = fromInteger totalWeight
            entries = snd $ mapAccumL compileGroup 0 grouped
            table = listArray (0, lastIndex) entries
         in Just (bound, lookupWeightGroup table lastIndex)
    | otherwise = Nothing
  where
    totalWeight = sum $ map fst weighted
    -- Prepending each singleton keeps grouping linear. Ticket order is
    -- private; every payload still carries its original structural rank.
    grouped =
        Map.toAscList $
            Map.fromListWith
                (<>)
                [(weight, [value]) | (weight, value) <- weighted]
    lastIndex = length grouped - 1

    compileGroup lowerBound (weight, values) =
        let !ticketWidth = fromInteger weight
            !upperBound = lowerBound + ticketWidth * length values
            valueTable = listArray (0, length values - 1) values
         in ( upperBound
            , WeightGroup lowerBound upperBound ticketWidth valueTable
            )

-- | Outcomes with one ticket width, stored as one contiguous ticket interval.
data WeightGroup a
    = WeightGroup
        {-# UNPACK #-} !Int
        {-# UNPACK #-} !Int
        {-# UNPACK #-} !Int
        !(Array Int a)

-- | Find the weight group containing one ticket, then index within that group.
lookupWeightGroup :: Array Int (WeightGroup a) -> Int -> Int -> a
lookupWeightGroup table lastIndex ticket = go 0 lastIndex
  where
    go low high
        | low == high =
            case unsafeAt table low of
                WeightGroup lowerBound _ ticketWidth values ->
                    unsafeAt values $ (ticket - lowerBound) `quot` ticketWidth
        | otherwise =
            case unsafeAt table midpoint of
                WeightGroup _ upperBound _ _
                    | ticket < upperBound -> go low midpoint
                    | otherwise -> go (midpoint + 1) high
      where
        midpoint = (low + high) `div` 2
