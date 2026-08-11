{- | Compiled rank decoders for transparent generators.

A 'Plan' preserves the choice, product, and map structure of a generator's
rank space; 'compilePlan' normalizes it and compiles one flat decoder, on
machine 'Int' arithmetic whenever the language fits.
-}
module Data.ECTA.Gen.Internal.Decoder (
    Plan (..),
    RankDecoder (..),
    planCardinality,
    compilePlan,
) where

import GHC.Arr (Array, listArray, unsafeAt)

{- | Symbolic rank-decoding structure retained beside every outcome index.

The plan preserves choice, product, and map structure instead of losing it in
nested @Integer -> a@ closures, so lowering can normalize and compile it into
one flat decoder. Branch order and mixed-radix product order match the stable
rank order of the corresponding selectors exactly.
-}
data Plan a where
    PlanSelect :: !Integer -> (Integer -> a) -> Plan a
    PlanMap :: (b -> a) -> Plan b -> Plan a
    PlanChoice :: [(Integer, Plan a)] -> Plan a
    PlanAp :: !Integer -> Plan (b -> a) -> Plan b -> Plan a

-- | A compiled rank decoder, on machine ints whenever the cardinality fits.
data RankDecoder a
    = SmallDecoder !Int (Int -> a)
    | LargeDecoder !Integer (Integer -> a)

planCardinality :: Plan a -> Integer
planCardinality (PlanSelect cardinality' _) = cardinality'
planCardinality (PlanMap _ plan) = planCardinality plan
planCardinality (PlanChoice branches) = sum $ map fst branches
planCardinality (PlanAp rightCardinality planF _) =
    planCardinality planF * rightCardinality

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

rebuildChoice :: [(Integer, Plan a)] -> Plan a
rebuildChoice [(_, only)] = only
rebuildChoice branches = PlanChoice branches

-- | Leaves at most this large are tabulated into arrays at compile time.
tabulationBound :: Int
tabulationBound = 4096

-- | Compile a plan, choosing the machine-'Int' path when the language fits.
compilePlan :: Integer -> Plan a -> RankDecoder a
compilePlan totalOutcomes plan
    | totalOutcomes <= toInteger (maxBound :: Int) =
        SmallDecoder (fromInteger totalOutcomes) (compileInt normalized)
    | otherwise = LargeDecoder totalOutcomes (compileInteger normalized)
  where
    normalized = normalizePlan plan

compileInt :: Plan a -> Int -> a
compileInt (PlanSelect cardinality' decode)
    | size <= tabulationBound =
        let table =
                listArray
                    (0, size - 1)
                    [decode (toInteger index) | index <- [0 .. size - 1]]
         in unsafeAt table
    | otherwise = decode . toInteger
  where
    size :: Int
    size = fromInteger cardinality'
compileInt (PlanMap transform plan) = (transform .) (compileInt plan)
compileInt (PlanChoice branches) =
    dispatchTree totalOutcomes $ offsetBranches 0 branches
  where
    totalOutcomes = fromInteger $ sum $ map fst branches

    offsetBranches _ [] = []
    offsetBranches offset ((branchCardinality, branch) : rest) =
        let upper = offset + fromInteger branchCardinality
         in (offset, compileInt branch) : offsetBranches upper rest

    -- Split where the cumulative cardinality crosses the midpoint of the
    -- covered range, so heavy branches sit near the root and the expected
    -- number of comparisons tracks the branch mass distribution.
    dispatchTree _ [(offset, decode)]
        | offset == 0 = decode
        | otherwise = \index -> decode (index - offset)
    dispatchTree upper offsetBranches' =
        let low = case offsetBranches' of
                (offset, _) : _ -> offset
                [] -> error "compileInt: empty dispatch"
            midpoint = (low + upper) `div` 2
            (lowBranches, highBranches) =
                case break (\(offset, _) -> offset > midpoint) offsetBranches' of
                    (allBranches, []) -> (init allBranches, [last allBranches])
                    split -> split
            pivot = case highBranches of
                (offset, _) : _ -> offset
                [] -> error "compileInt: empty dispatch"
            decodeLow = dispatchTree pivot lowBranches
            decodeHigh = dispatchTree upper highBranches
         in \index ->
                if index < pivot
                    then decodeLow index
                    else decodeHigh index
compileInt (PlanAp outerRadix (PlanAp innerRadix planF planX1) planX2)
    | outerRadix > 1
    , innerRadix > 1
    , Just leftTable <- leafTableInt planX1
    , Just rightTable <- leafTableInt planX2 =
        let outer = fromInteger outerRadix :: Int
            inner = fromInteger innerRadix :: Int
         in if planCardinality planF == 1
                then
                    let onlyFunction = compileInt planF 0
                     in \index ->
                            case index `quotRem` outer of
                                (leftIndex, rightIndex) ->
                                    let !leftArgument = unsafeAt leftTable leftIndex
                                        !rightArgument = unsafeAt rightTable rightIndex
                                     in onlyFunction leftArgument rightArgument
                else
                    let decodeF = compileInt planF
                     in \index ->
                            case index `quotRem` outer of
                                (functionAndLeft, rightIndex) ->
                                    case functionAndLeft `quotRem` inner of
                                        (functionIndex, leftIndex) ->
                                            let !leftArgument = unsafeAt leftTable leftIndex
                                                !rightArgument = unsafeAt rightTable rightIndex
                                             in decodeF functionIndex leftArgument rightArgument
compileInt (PlanAp outerRadix (PlanAp innerRadix planF planX1) planX2)
    | outerRadix > 1
    , innerRadix > 1 =
        let decodeX1 = compileInt planX1
            decodeX2 = compileInt planX2
            outer = fromInteger outerRadix :: Int
            inner = fromInteger innerRadix :: Int
         in if planCardinality planF == 1
                then
                    let onlyFunction = compileInt planF 0
                     in \index ->
                            case index `quotRem` outer of
                                (leftIndex, rightIndex) ->
                                    let !leftArgument = decodeX1 leftIndex
                                        !rightArgument = decodeX2 rightIndex
                                     in onlyFunction leftArgument rightArgument
                else
                    let decodeF = compileInt planF
                     in \index ->
                            case index `quotRem` outer of
                                (functionAndLeft, rightIndex) ->
                                    case functionAndLeft `quotRem` inner of
                                        (functionIndex, leftIndex) ->
                                            let !leftArgument = decodeX1 leftIndex
                                                !rightArgument = decodeX2 rightIndex
                                             in decodeF functionIndex leftArgument rightArgument
compileInt (PlanAp rightCardinality planF planX)
    | rightCardinality == 1 =
        let decodeF = compileInt planF
            firstArgument = compileInt planX 0
         in \index -> decodeF index $! firstArgument
    | planCardinality planF == 1 =
        let onlyFunction = compileInt planF 0
            decodeX = compileInt planX
         in \index ->
                let !argument = decodeX index
                 in onlyFunction argument
    | otherwise =
        let decodeF = compileInt planF
            decodeX = compileInt planX
            radix = fromInteger rightCardinality
         in \index ->
                case index `quotRem` radix of
                    (functionIndex, argumentIndex) ->
                        let !argument = decodeX argumentIndex
                         in decodeF functionIndex argument

-- | The tabulated array of a small leaf, for saturated in-branch reads.
leafTableInt :: Plan a -> Maybe (Array Int a)
leafTableInt (PlanSelect cardinality' decode)
    | size <= tabulationBound =
        Just $
            listArray
                (0, size - 1)
                [decode (toInteger index) | index <- [0 .. size - 1]]
  where
    size :: Int
    size = fromInteger cardinality'
leafTableInt _ = Nothing

compileInteger :: Plan a -> Integer -> a
compileInteger (PlanSelect cardinality' decode)
    | cardinality' <= toInteger tabulationBound =
        let size = fromInteger cardinality' :: Int
            table =
                listArray
                    (0, size - 1)
                    [decode (toInteger index) | index <- [0 .. size - 1]]
         in unsafeAt table . fromInteger
    | otherwise = decode
compileInteger (PlanMap transform plan) = (transform .) (compileInteger plan)
compileInteger (PlanChoice branches) =
    dispatchTree totalOutcomes $ offsetBranches 0 branches
  where
    totalOutcomes = sum $ map fst branches

    offsetBranches _ [] = []
    offsetBranches offset ((branchCardinality, branch) : rest) =
        let upper = offset + branchCardinality
         in (offset, compileInteger branch) : offsetBranches upper rest

    dispatchTree _ [(offset, decode)]
        | offset == 0 = decode
        | otherwise = \index -> decode (index - offset)
    dispatchTree upper offsetBranches' =
        let low = case offsetBranches' of
                (offset, _) : _ -> offset
                [] -> error "compileInteger: empty dispatch"
            midpoint = (low + upper) `div` 2
            (lowBranches, highBranches) =
                case break (\(offset, _) -> offset > midpoint) offsetBranches' of
                    (allBranches, []) -> (init allBranches, [last allBranches])
                    split -> split
            pivot = case highBranches of
                (offset, _) : _ -> offset
                [] -> error "compileInteger: empty dispatch"
            decodeLow = dispatchTree pivot lowBranches
            decodeHigh = dispatchTree upper highBranches
         in \index ->
                if index < pivot
                    then decodeLow index
                    else decodeHigh index
compileInteger (PlanAp outerRadix (PlanAp innerRadix planF planX1) planX2)
    | outerRadix > 1
    , innerRadix > 1 =
        let decodeX1 = compileInteger planX1
            decodeX2 = compileInteger planX2
         in if planCardinality planF == 1
                then
                    let onlyFunction = compileInteger planF 0
                     in \index ->
                            case index `quotRem` outerRadix of
                                (leftIndex, rightIndex) ->
                                    let !leftArgument = decodeX1 leftIndex
                                        !rightArgument = decodeX2 rightIndex
                                     in onlyFunction leftArgument rightArgument
                else
                    let decodeF = compileInteger planF
                     in \index ->
                            case index `quotRem` outerRadix of
                                (functionAndLeft, rightIndex) ->
                                    case functionAndLeft `quotRem` innerRadix of
                                        (functionIndex, leftIndex) ->
                                            let !leftArgument = decodeX1 leftIndex
                                                !rightArgument = decodeX2 rightIndex
                                             in decodeF functionIndex leftArgument rightArgument
compileInteger (PlanAp rightCardinality planF planX)
    | rightCardinality == 1 =
        let decodeF = compileInteger planF
            firstArgument = compileInteger planX 0
         in \index -> decodeF index $! firstArgument
    | planCardinality planF == 1 =
        let onlyFunction = compileInteger planF 0
            decodeX = compileInteger planX
         in \index ->
                let !argument = decodeX index
                 in onlyFunction argument
    | otherwise =
        let decodeF = compileInteger planF
            decodeX = compileInteger planX
         in \index ->
                case index `quotRem` rightCardinality of
                    (functionIndex, argumentIndex) ->
                        let !argument = decodeX argumentIndex
                         in decodeF functionIndex argument
