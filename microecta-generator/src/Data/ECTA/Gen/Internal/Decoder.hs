{- | Compiled rank decoders for transparent generators.

A 'Plan' preserves the choice, product, and map structure of a generator's
rank space. 'compilePlan' normalizes it and compiles one flat decoder, on
machine 'Int' arithmetic whenever the language fits.
-}
module Data.ECTA.Gen.Internal.Decoder (
    Plan (..),
    RankDecoder (..),
    planCardinality,
    compilePlan,
) where

import GHC.Arr (listArray, unsafeAt)

{- | Symbolic rank-decoding structure retained beside every outcome index.

The plan preserves choice, product, and map structure instead of losing it in
nested @Integer -> a@ closures, so lowering can normalize and compile it into
one flat decoder. Branch order and mixed-radix product order match the stable
rank order of the corresponding selectors exactly.
-}
data Plan a where
    -- | A leaf: a finite source decoded by index.
    PlanSelect :: !Integer -> (Integer -> a) -> Plan a
    -- | Map decoded values.
    PlanMap :: (b -> a) -> Plan b -> Plan a
    -- | Ordered alternatives; each pair is a branch cardinality and branch.
    PlanChoice :: [(Integer, Plan a)] -> Plan a
    {- | A product: function ranks are more significant than argument ranks,
    and the radix is the argument cardinality.
    -}
    PlanAp :: !Integer -> Plan (b -> a) -> Plan b -> Plan a
    {- | A language already stratified by member size: ascending sizes, each
    with its member count and a decoder for one position in that size class.

    Ranks are size-major, so a smaller rank never decodes to a larger member.
    This is what a recursive generator bounded by 'Data.ECTA.Gen.upToSize'
    lowers to; the other constructors keep the mixed-radix order they always
    had.
    -}
    PlanSized :: [(Int, Integer, Integer -> a)] -> Plan a

-- | A compiled rank decoder, on machine ints whenever the cardinality fits.
data RankDecoder a
    = SmallDecoder !Int (Int -> a)
    | LargeDecoder !Integer (Integer -> a)

-- | The exact number of ranks a plan decodes.
planCardinality :: Plan a -> Integer
planCardinality (PlanSelect cardinality' _) = cardinality'
planCardinality (PlanMap _ plan) = planCardinality plan
planCardinality (PlanChoice branches) = sum $ map fst branches
planCardinality (PlanAp rightCardinality planF _) =
    planCardinality planF * rightCardinality
planCardinality (PlanSized classes) =
    sum [classCount | (_, classCount, _) <- classes]

{- | Normalize a plan: push maps into leaves and product functions, splice
nested choices into one level, and collapse singleton choices.

Splicing preserves rank order because nested branch offsets concatenate in
the same order as the flattened cumulative offsets.
-}
normalizePlan :: Plan a -> Plan a
normalizePlan (PlanMap transform plan) = pushMap transform plan
normalizePlan (PlanChoice branches) =
    rebuildChoice $ concatMap flattenBranch branches
  where
    flattenBranch (branchCardinality, branch) =
        case normalizePlan branch of
            PlanChoice inner -> inner
            other -> [(branchCardinality, other)]
normalizePlan (PlanAp rightCardinality planF planX) =
    PlanAp rightCardinality (normalizePlan planF) (normalizePlan planX)
normalizePlan plan@(PlanSelect _ _) = plan
normalizePlan plan@(PlanSized _) = plan

-- | Push one pending map down while normalizing below it.
pushMap :: (b -> a) -> Plan b -> Plan a
pushMap transform (PlanMap inner plan) = pushMap (transform . inner) plan
pushMap transform (PlanSelect cardinality' decode) =
    PlanSelect cardinality' (transform . decode)
pushMap transform (PlanChoice branches) =
    rebuildChoice $ concatMap flattenBranch branches
  where
    flattenBranch (branchCardinality, branch) =
        case pushMap transform branch of
            PlanChoice inner -> inner
            other -> [(branchCardinality, other)]
pushMap transform (PlanAp rightCardinality planF planX) =
    PlanAp
        rightCardinality
        (pushMap (transform .) planF)
        (normalizePlan planX)
pushMap transform (PlanSized classes) =
    PlanSized
        [ (size, classCount, transform . decode)
        | (size, classCount, decode) <- classes
        ]

-- | Collapse a singleton choice into its only branch.
rebuildChoice :: [(Integer, Plan a)] -> Plan a
rebuildChoice [(_, only)] = only
rebuildChoice branches = PlanChoice branches

-- | Leaves at most this large are tabulated into arrays at compile time.
tabulationBound :: Integer
tabulationBound = 4096

-- | Compile a plan, choosing the machine-'Int' path when the language fits.
compilePlan :: Integer -> Plan a -> RankDecoder a
compilePlan totalOutcomes plan
    | totalOutcomes <= toInteger (maxBound :: Int) =
        SmallDecoder (fromInteger totalOutcomes) (compileRank normalized)
    | otherwise = LargeDecoder totalOutcomes (compileRank normalized)
  where
    normalized = normalizePlan plan

{- | Compile a normalized plan to one decoder over the given rank type.

Choices become weight-balanced comparison trees, products decode by
quotient and remainder, small leaves read tabulated arrays, and every
decoded argument is bound strictly before the operation closure is applied:
the operation is an unknown function, so an unforced argument would be
thunked only for the decoded value's strict fields to force it immediately.
-}
compileRank :: (Integral rank) => Plan a -> rank -> a
compileRank (PlanSelect cardinality' decode)
    | cardinality' <= tabulationBound =
        let size = fromInteger cardinality' :: Int
            table =
                listArray
                    (0, size - 1)
                    [decode (toInteger index) | index <- [0 .. size - 1]]
         in unsafeAt table . fromIntegral
    | otherwise = decode . toInteger
compileRank (PlanMap transform plan) =
    let decode = compileRank plan
     in \index ->
            let !value = decode index
             in transform value
compileRank (PlanChoice branches) =
    dispatchTree totalOutcomes $ offsetParts 0 [(branchCardinality, compileRank branch) | (branchCardinality, branch) <- branches]
  where
    totalOutcomes = fromInteger $ sum $ map fst branches
compileRank (PlanSized classes) =
    dispatchTree totalOutcomes $
        offsetParts 0 [(classCount, decode . toInteger) | (_, classCount, decode) <- classes]
  where
    totalOutcomes = fromInteger $ sum [classCount | (_, classCount, _) <- classes]
compileRank (PlanAp outerRadix (PlanAp innerRadix planF planX1) planX2)
    -- One fused decoder per binary application: one closure, one or two
    -- quotient-remainder steps, instead of two nested product closures.
    | outerRadix > 1
    , innerRadix > 1 =
        let decodeX1 = compileRank planX1
            decodeX2 = compileRank planX2
            outer = fromInteger outerRadix
            inner = fromInteger innerRadix
         in if planCardinality planF == 1
                then
                    let onlyFunction = compileRank planF (0 :: Int)
                     in \index ->
                            case index `quotRem` outer of
                                (leftIndex, rightIndex) ->
                                    let !leftArgument = decodeX1 leftIndex
                                        !rightArgument = decodeX2 rightIndex
                                     in onlyFunction leftArgument rightArgument
                else
                    let decodeF = compileRank planF
                     in \index ->
                            case index `quotRem` outer of
                                (functionAndLeft, rightIndex) ->
                                    case functionAndLeft `quotRem` inner of
                                        (functionIndex, leftIndex) ->
                                            let !leftArgument = decodeX1 leftIndex
                                                !rightArgument = decodeX2 rightIndex
                                             in decodeF functionIndex leftArgument rightArgument
compileRank (PlanAp rightCardinality planF planX)
    | rightCardinality == 1 =
        let decodeF = compileRank planF
            firstArgument = compileRank planX (0 :: Int)
         in \index -> decodeF index $! firstArgument
    | planCardinality planF == 1 =
        let onlyFunction = compileRank planF (0 :: Int)
            decodeX = compileRank planX
         in \index ->
                let !argument = decodeX index
                 in onlyFunction argument
    | otherwise =
        let decodeF = compileRank planF
            decodeX = compileRank planX
            radix = fromInteger rightCardinality
         in \index ->
                case index `quotRem` radix of
                    (functionIndex, argumentIndex) ->
                        let !argument = decodeX argumentIndex
                         in decodeF functionIndex argument
{-# SPECIALIZE compileRank :: Plan a -> Int -> a #-}
{-# SPECIALIZE compileRank :: Plan a -> Integer -> a #-}

-- | Pair each part decoder with its cumulative rank offset.
offsetParts :: (Integral rank) => rank -> [(Integer, rank -> a)] -> [(rank, rank -> a)]
offsetParts _ [] = []
offsetParts offset ((partCardinality, decode) : rest) =
    (offset, decode) : offsetParts (offset + fromInteger partCardinality) rest

{- | Dispatch a rank to the part holding it, rebased into that part.

The tree splits where the cumulative cardinality crosses the midpoint of the
covered range, so heavy parts sit near the root and the expected number of
comparisons tracks how the mass is distributed.
-}
dispatchTree :: (Integral rank) => rank -> [(rank, rank -> a)] -> rank -> a
dispatchTree _ [(offset, decode)]
    | offset == 0 = decode
    | otherwise = \index -> decode (index - offset)
dispatchTree upper parts =
    let low = case parts of
            (offset, _) : _ -> offset
            [] ->
                error
                    "microecta-generator bug in Data.ECTA.Gen.Internal.Decoder.dispatchTree: \
                    \no part to dispatch to"
        midpoint = (low + upper) `div` 2
        (lowParts, highParts) =
            case break (\(offset, _) -> offset > midpoint) parts of
                (allParts, []) -> (init allParts, [last allParts])
                split -> split
        pivot = case highParts of
            (offset, _) : _ -> offset
            [] ->
                error
                    "microecta-generator bug in Data.ECTA.Gen.Internal.Decoder.dispatchTree: \
                    \no part to dispatch to"
        decodeLow = dispatchTree pivot lowParts
        decodeHigh = dispatchTree upper highParts
     in \index ->
            if index < pivot
                then decodeLow index
                else decodeHigh index
