{- | Compiled rank decoders for transparent generators.

A 'Plan' preserves the choice, product, and map structure of a generator's
rank space. 'compilePlan' normalizes it and compiles one flat decoder, narrowing
each locally bounded rank to machine 'Int' arithmetic whenever it fits.

This module is an exposed internal module. The generator layers of
microcfta-generator use it directly. Its exports are not covered by the PVP
contract of the package.
-}
module Data.CFTA.Ranked.Internal.Decoder (
    Plan (..),
    RankDecoder (..),
    planCardinality,
    compilePlan,
) where

import qualified Data.Map.Lazy as Map
import GHC.Arr (listArray, unsafeAt)

import Data.CFTA.Index (Cardinality (..), Rank (..))

{- | Symbolic rank-decoding structure retained beside every outcome index.

The plan preserves choice, product, and map structure instead of losing it in
nested @Integer -> a@ closures, so lowering can normalize and compile it into
one flat decoder. Branch order and mixed-radix product order match the stable
rank order of the corresponding selectors exactly. Every producer in this
package keeps to this: a choice lists its branches in rank order, and a product
puts the function rank before the argument rank, with the cardinality of the
argument as its radix. The producers are the applicative and the choice of the
ranked layer, the combinators of "Data.CFTA.Gen.Internal.Static", the buckets,
the joins, the argument chains, and the bounded recursive language.
-}
data Plan a where
    -- | A leaf: a finite source decoded by index.
    PlanSelect :: !Cardinality -> (Rank -> a) -> Plan a
    {- | A leaf whose decoder must remain on demand even when it is small.

    Automaton enumerators use this so compiling a rank plan never constructs
    accepted terms merely to fill the ordinary small-leaf lookup table.
    -}
    PlanSelectOnDemand :: !Cardinality -> (Rank -> a) -> Plan a
    -- | A shared subplan with its cardinality and compiled decoder.
    PlanShared :: !Cardinality -> RankDecoder a -> Plan a -> Plan a
    -- | Map decoded values.
    PlanMap :: (b -> a) -> Plan b -> Plan a
    -- | Ordered alternatives; each pair is a branch cardinality and branch.
    PlanChoice :: [(Cardinality, Plan a)] -> Plan a
    {- | A product: function ranks are more significant than argument ranks,
    and the radix is the argument cardinality.
    -}
    PlanAp :: !Cardinality -> Plan (b -> a) -> Plan b -> Plan a
    {- | A language already stratified by member size: ascending sizes, each
    with its member count and a decoder for one position in that size class.

    'PlanSized' does not check that the sizes ascend. Its producers keep them
    ascending. The bounded recursive language builds the classes with
    @sizeClasses@, which gives strictly ascending sizes. The @share@ of the
    ranked layer gives a language with one member as one class. So ranks are
    size-major, and a smaller rank never decodes to a larger member.
    A bounded size-indexed generator lowers to this plan. The other
    constructors retain their mixed-radix order.
    -}
    PlanSized :: [(Integer, Cardinality, Integer -> a, Int -> a)] -> Plan a

{- | A compiled rank decoder, selected by the top-level cardinality.

A small decoder keeps the cardinality and the rank as machine 'Int's.
-}
data RankDecoder a
    = SmallDecoder !Int (Int -> a)
    | LargeDecoder !Cardinality (Rank -> a)

-- | The exact number of ranks a plan decodes.
planCardinality :: Plan a -> Cardinality
planCardinality (PlanSelect cardinality' _) = cardinality'
planCardinality (PlanSelectOnDemand cardinality' _) = cardinality'
planCardinality (PlanShared cardinality' _ _) = cardinality'
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
normalizePlan plan@(PlanShared{}) = plan
normalizePlan plan@(PlanSized _) = plan

-- | Push one pending map down while normalizing below it.
pushMap :: (b -> a) -> Plan b -> Plan a
pushMap transform (PlanMap inner plan) = pushMap (transform . inner) plan
pushMap transform (PlanSelect cardinality' decode) =
    PlanSelect cardinality' (transform . decode)
pushMap transform (PlanSelectOnDemand cardinality' decode) =
    PlanSelectOnDemand cardinality' (transform . decode)
pushMap transform plan@(PlanShared{}) = PlanMap transform plan
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
rebuildChoice :: [(Cardinality, Plan a)] -> Plan a
rebuildChoice [(_, only)] = only
rebuildChoice branches = PlanChoice branches

-- | Leaves at most this large are tabulated into arrays at compile time.
tabulationBound :: Cardinality
tabulationBound = 4096

{- | Compile a plan, choosing the machine-'Int' path when the language fits.

A larger language keeps an 'Integer' at its root, but its decoder narrows each
branch or product component to 'Int' as soon as that subplan's own cardinality
fits. One wide outer rank therefore does not force machine-sized child ranks
through arbitrary-precision arithmetic.
-}
compilePlan :: Cardinality -> Plan a -> RankDecoder a
compilePlan (Cardinality totalOutcomes) plan
    | totalOutcomes <= toInteger (maxBound :: Int) =
        SmallDecoder (fromInteger totalOutcomes) (compileRank normalized)
    | otherwise = LargeDecoder (Cardinality totalOutcomes) (\(Rank rank) -> compileLargeRank normalized rank)
  where
    normalized = normalizePlan plan

-- | Compile a normalized plan to one decoder over machine 'Int' ranks.
compileRank :: Plan a -> Int -> a
compileRank = compileRankWith compileRank

{- | Compile a wide plan while narrowing every locally bounded subplan.

The root still needs 'Integer' comparisons and divisions, but a product
remainder is bounded by its argument cardinality. 'compileLocalRank' turns that
remainder into an 'Int' before decoding the argument whenever possible.
-}
compileLargeRank :: Plan a -> Integer -> a
compileLargeRank = compileRankWith compileLocalRank

{- | Compile a normalized plan to one decoder over the given rank type, with
the given compiler for its subplans.

Choices use cumulative-offset maps, products decode by quotient and remainder,
small leaves read tabulated arrays, and every decoded argument is bound
strictly before the operation closure is applied: the operation is an unknown
function, so an unforced argument would be thunked only for the decoded
value's strict fields to force it immediately.

The pragma makes one copy for 'Int' and one for 'Integer', each with its own
arithmetic. A tabulated leaf is a lambda, not the partial application
@unsafeAt table@: each call of a partial application goes through the generic
application code of the runtime. With the partial application, the benchmark
cells @fta@ and @ecta@ run 15% and 20% more instructions.
-}
compileRankWith :: (Integral rank) => (forall b. Plan b -> rank -> b) -> Plan a -> rank -> a
{-# INLINE compileRankWith #-}
compileRankWith _ (PlanSelect cardinality'@(Cardinality count) decode)
    | cardinality' <= tabulationBound =
        let size = fromInteger count :: Int
            table =
                listArray
                    (0, size - 1)
                    [decode (Rank $ toInteger index) | index <- [0 .. size - 1]]
         in \index -> unsafeAt table (fromIntegral index)
    | otherwise = decode . Rank . toInteger
compileRankWith _ (PlanSelectOnDemand _ decode) = decode . Rank . toInteger
compileRankWith _ (PlanShared _ (SmallDecoder _ decode) _) = decode . fromIntegral
compileRankWith _ (PlanShared _ (LargeDecoder _ decode) _) = decode . Rank . toInteger
compileRankWith child (PlanMap transform plan) =
    let decode = child plan
     in \index ->
            let !value = decode index
             in transform value
compileRankWith child (PlanChoice branches) =
    dispatchParts $
        offsetParts 0 [(branchCardinality, child branch) | (branchCardinality, branch) <- branches]
compileRankWith _ (PlanSized classes) =
    dispatchParts $
        offsetParts
            0
            [ ( classCount
              , if classCount <= Cardinality (toInteger (maxBound :: Int))
                    then decodeInt . fromIntegral
                    else decode . toInteger
              )
            | (_, classCount, decode, decodeInt) <- classes
            ]
compileRankWith child (PlanAp (Cardinality outerRadix) (PlanAp (Cardinality innerRadix) planF planX1) planX2)
    -- One fused decoder per binary application: one closure, one or two
    -- quotient-remainder steps, instead of two nested product closures.
    | outerRadix > 1
    , innerRadix > 1 =
        let decodeX1 = child planX1
            decodeX2 = child planX2
            outer = fromInteger outerRadix
            inner = fromInteger innerRadix
         in if planCardinality planF == 1
                then
                    let onlyFunction = child planF 0
                     in \index ->
                            case index `quotRem` outer of
                                (leftIndex, rightIndex) ->
                                    let !leftArgument = decodeX1 leftIndex
                                        !rightArgument = decodeX2 rightIndex
                                     in onlyFunction leftArgument rightArgument
                else
                    let decodeF = child planF
                     in \index ->
                            case index `quotRem` outer of
                                (functionAndLeft, rightIndex) ->
                                    case functionAndLeft `quotRem` inner of
                                        (functionIndex, leftIndex) ->
                                            let !leftArgument = decodeX1 leftIndex
                                                !rightArgument = decodeX2 rightIndex
                                             in decodeF functionIndex leftArgument rightArgument
compileRankWith child (PlanAp (Cardinality rightCardinality) planF planX)
    | rightCardinality == 1 =
        let decodeF = child planF
            firstArgument = child planX 0
         in \index -> decodeF index $! firstArgument
    | planCardinality planF == 1 =
        let onlyFunction = child planF 0
            decodeX = child planX
         in \index ->
                let !argument = decodeX index
                 in onlyFunction argument
    | otherwise =
        let decodeF = child planF
            decodeX = child planX
            radix = fromInteger rightCardinality
         in \index ->
                case index `quotRem` radix of
                    (functionIndex, argumentIndex) ->
                        let !argument = decodeX argumentIndex
                         in decodeF functionIndex argument

-- | Decode an 'Integer' rank using 'Int' internally when this subplan fits.
compileLocalRank :: Plan a -> Integer -> a
compileLocalRank plan
    | planCardinality plan <= Cardinality (toInteger (maxBound :: Int)) =
        let decode = compileRank plan
         in \index -> decode (fromInteger index)
    | otherwise = compileLargeRank plan

-- | Pair each part decoder with its cumulative rank offset.
offsetParts :: (Integral rank) => rank -> [(Cardinality, rank -> a)] -> [(rank, rank -> a)]
offsetParts _ [] = []
offsetParts offset ((Cardinality partCardinality, decode) : rest)
    | partCardinality > 0 =
        (offset, decode) : offsetParts (offset + fromInteger partCardinality) rest
    | otherwise = offsetParts offset rest

-- | Dispatch a rank through the cumulative offsets and rebase it into its part.
dispatchParts :: (Integral rank) => [(rank, rank -> a)] -> rank -> a
dispatchParts [(offset, decode)]
    | offset == 0 = decode
    | otherwise = \index -> decode (index - offset)
dispatchParts parts = compileTable (Map.fromDistinctAscList parts)
  where
    -- \| Compile the branches once to avoid allocating a lookup result per rank.
    compileTable table
        | Map.null table =
            error
                "microcfta-generator bug in Data.CFTA.Ranked.Internal.Decoder.dispatchParts: \
                \no part to dispatch to"
        | Map.size table == 1 = dispatchParts [Map.findMin table]
        | otherwise =
            let (low, high) = Map.splitAt (Map.size table `quot` 2) table
                pivot = fst (Map.findMin high)
                decodeLow = compileTable low
                decodeHigh = compileTable high
             in \index ->
                    if index < pivot then decodeLow index else decodeHigh index
