{- | Compiled rank decoders for transparent generators.

A 'Plan' preserves the choice, product, and map structure of a generator's
rank space. 'compilePlan' normalizes it and compiles one flat decoder, narrowing
each locally bounded rank to machine 'Int' arithmetic whenever it fits.
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
    {- | A leaf whose decoder must remain on demand even when it is small.

    Automaton enumerators use this so compiling a rank plan never constructs
    accepted terms merely to fill the ordinary small-leaf lookup table.
    -}
    PlanSelectOnDemand :: !Integer -> (Integer -> a) -> Plan a
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
    PlanSized :: [(Int, Integer, Integer -> a, Int -> a)] -> Plan a

-- | A compiled rank decoder, selected by the top-level cardinality.
data RankDecoder a
    = SmallDecoder !Int (Int -> a)
    | LargeDecoder !Integer (Integer -> a)

-- | The exact number of ranks a plan decodes.
planCardinality :: Plan a -> Integer
planCardinality (PlanSelect cardinality' _) = cardinality'
planCardinality (PlanSelectOnDemand cardinality' _) = cardinality'
planCardinality (PlanMap _ plan) = planCardinality plan
planCardinality (PlanChoice branches) = sum $ map fst branches
planCardinality (PlanAp rightCardinality planF _) =
    planCardinality planF * rightCardinality
planCardinality (PlanSized classes) =
    sum [classCount | (_, classCount, _, _) <- classes]

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
normalizePlan plan@(PlanSelectOnDemand _ _) = plan
normalizePlan plan@(PlanSized _) = plan

-- | Push one pending map down while normalizing below it.
pushMap :: (b -> a) -> Plan b -> Plan a
pushMap transform (PlanMap inner plan) = pushMap (transform . inner) plan
pushMap transform (PlanSelect cardinality' decode) =
    PlanSelect cardinality' (transform . decode)
pushMap transform (PlanSelectOnDemand cardinality' decode) =
    PlanSelectOnDemand cardinality' (transform . decode)
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
        [ (size, classCount, transform . decode, transform . decodeInt)
        | (size, classCount, decode, decodeInt) <- classes
        ]

-- | Collapse a singleton choice into its only branch.
rebuildChoice :: [(Integer, Plan a)] -> Plan a
rebuildChoice [(_, only)] = only
rebuildChoice branches = PlanChoice branches

-- | Leaves at most this large are tabulated into arrays at compile time.
tabulationBound :: Integer
tabulationBound = 4096

{- | Compile a plan, choosing the machine-'Int' path when the language fits.

A larger language keeps an 'Integer' at its root, but its decoder narrows each
branch or product component to 'Int' as soon as that subplan's own cardinality
fits. One wide outer rank therefore does not force machine-sized child ranks
through arbitrary-precision arithmetic.
-}
compilePlan :: Integer -> Plan a -> RankDecoder a
compilePlan totalOutcomes plan
    | totalOutcomes <= toInteger (maxBound :: Int) =
        SmallDecoder (fromInteger totalOutcomes) (compileRank normalized)
    | otherwise = LargeDecoder totalOutcomes (compileLargeRank normalized)
  where
    normalized = normalizePlan plan

{- | Compile a normalized plan to one decoder over the given rank type.

Choices become weight-balanced comparison trees, products decode by
quotient and remainder, small leaves read tabulated arrays, and every
decoded argument is bound strictly before the operation closure is applied:
the operation is an unknown function, so an unforced argument would be
thunked only for the decoded value's strict fields to force it immediately.
-}
compileRank :: Plan a -> Int -> a
compileRank (PlanSelect cardinality' decode)
    | cardinality' <= tabulationBound =
        let size = fromInteger cardinality' :: Int
            table =
                listArray
                    (0, size - 1)
                    [decode (toInteger index) | index <- [0 .. size - 1]]
         in unsafeAt table
    | otherwise = decode . toInteger
compileRank (PlanSelectOnDemand _ decode) = decode . toInteger
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
        offsetParts 0 [(classCount, decodeInt) | (_, classCount, _, decodeInt) <- classes]
  where
    totalOutcomes = fromInteger $ sum [classCount | (_, classCount, _, _) <- classes]
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

{- | Compile a wide plan while narrowing every locally bounded subplan.

The root still needs 'Integer' comparisons and divisions, but a product
remainder is bounded by its argument cardinality. 'compileLocalRank' turns that
remainder into an 'Int' before decoding the argument whenever possible.

This deliberately mirrors 'compileRank' clause for clause rather than sharing
one @Integral rank@ implementation with it: specialising the whole decoder to
machine 'Int' is the point of this module, and a polymorphic version would box
the arithmetic on exactly the path that is meant to be cheap.
-}
compileLargeRank :: Plan a -> Integer -> a
compileLargeRank (PlanSelect cardinality' decode)
    | cardinality' <= tabulationBound =
        let size = fromInteger cardinality' :: Int
            table =
                listArray
                    (0, size - 1)
                    [decode (toInteger index) | index <- [0 .. size - 1]]
         in unsafeAt table . fromInteger
    | otherwise = decode
compileLargeRank (PlanSelectOnDemand _ decode) = decode
compileLargeRank (PlanMap transform plan) =
    let decode = compileLocalRank plan
     in \index ->
            let !value = decode index
             in transform value
compileLargeRank (PlanChoice branches) =
    dispatchTree totalOutcomes $
        offsetParts
            0
            [ (branchCardinality, compileLocalRank branch)
            | (branchCardinality, branch) <- branches
            ]
  where
    totalOutcomes = sum $ map fst branches
compileLargeRank (PlanSized classes) =
    dispatchTree totalOutcomes $
        offsetParts
            0
            [ ( classCount
              , if classCount <= toInteger (maxBound :: Int)
                    then decodeInt . fromInteger
                    else decode
              )
            | (_, classCount, decode, decodeInt) <- classes
            ]
  where
    totalOutcomes = sum [classCount | (_, classCount, _, _) <- classes]
compileLargeRank (PlanAp outerRadix (PlanAp innerRadix planF planX1) planX2)
    | outerRadix > 1
    , innerRadix > 1 =
        let decodeX1 = compileLocalRank planX1
            decodeX2 = compileLocalRank planX2
         in if planCardinality planF == 1
                then
                    let onlyFunction = compileLocalRank planF 0
                     in \index ->
                            case index `quotRem` outerRadix of
                                (leftIndex, rightIndex) ->
                                    let !leftArgument = decodeX1 leftIndex
                                        !rightArgument = decodeX2 rightIndex
                                     in onlyFunction leftArgument rightArgument
                else
                    let decodeF = compileLocalRank planF
                     in \index ->
                            case index `quotRem` outerRadix of
                                (functionAndLeft, rightIndex) ->
                                    case functionAndLeft `quotRem` innerRadix of
                                        (functionIndex, leftIndex) ->
                                            let !leftArgument = decodeX1 leftIndex
                                                !rightArgument = decodeX2 rightIndex
                                             in decodeF functionIndex leftArgument rightArgument
compileLargeRank (PlanAp rightCardinality planF planX)
    | rightCardinality == 1 =
        let decodeF = compileLocalRank planF
            firstArgument = compileLocalRank planX 0
         in \index -> decodeF index $! firstArgument
    | planCardinality planF == 1 =
        let onlyFunction = compileLocalRank planF 0
            decodeX = compileLocalRank planX
         in \index ->
                let !argument = decodeX index
                 in onlyFunction argument
    | otherwise =
        let decodeF = compileLocalRank planF
            decodeX = compileLocalRank planX
         in \index ->
                case index `quotRem` rightCardinality of
                    (functionIndex, argumentIndex) ->
                        let !argument = decodeX argumentIndex
                         in decodeF functionIndex argument

-- | Decode an 'Integer' rank using 'Int' internally when this subplan fits.
compileLocalRank :: Plan a -> Integer -> a
compileLocalRank plan
    | planCardinality plan <= toInteger (maxBound :: Int) =
        let decode = compileRank plan
         in \index -> decode (fromInteger index)
    | otherwise = compileLargeRank plan

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
        -- Written this way so a total cardinality near maxBound does not
        -- overflow the sum and send the split the wrong way.
        midpoint = low + (upper - low) `div` 2
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
