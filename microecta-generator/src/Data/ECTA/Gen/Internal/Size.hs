{- | Size-stratified counting and indexing for plans.

A plan's members split into size classes, where size is the number of source
choices in a member: an atom has size one, and an application adds the sizes
of its operation and argument choices. 'sizeIndex' counts every class by
FEAT-style convolution — a product of size @s@ splits into an operation of
size @a@ and arguments of size @s - a@ — and indexes into one directly,
returning the member's canonical rank alongside its value.

Counting is independent of the canonical rank order: a class is enumerated
in split-ascending, branch order, and each member's canonical rank is
reassembled from the sub-ranks on the way back up. Building the index costs
one traversal per plan occurrence, like compiling a decoder does; nothing
enumerates the language.
-}
module Data.ECTA.Gen.Internal.Size (
    SizeIndex (..),
    sizeIndex,
    countAtSize,
) where

import Data.ECTA.Gen.Internal.Decoder (Plan (..))

{- | The size classes of one plan: how many members each holds, and how to
select one by its position in the class.
-}
data SizeIndex a = SizeIndex
    { sizeClassCounts :: [Integer]
    -- ^ Members per size, for ascending sizes from one.
    , sizeClassSelect :: Int -> Integer -> (Integer, a)
    -- ^ Canonical rank and value of one member of one size class.
    }

-- | The number of members of one size, zero outside the counted sizes.
countAtSize :: SizeIndex a -> Int -> Integer
countAtSize index size
    | size < 1 = 0
    | otherwise = case drop (size - 1) (sizeClassCounts index) of
        count : _ -> count
        [] -> 0

-- | Count and index the size classes of a plan.
sizeIndex :: Plan a -> SizeIndex a
sizeIndex (PlanSelect cardinality' decode) =
    SizeIndex [cardinality'] select
  where
    select 1 index = (index, decode index)
    select size _ = error $ "sizeIndex: leaf has no members of size " <> show size
sizeIndex (PlanMap transform plan) =
    SizeIndex (sizeClassCounts inner) select
  where
    inner = sizeIndex plan
    select size index =
        let (rank, value) = sizeClassSelect inner size index
         in (rank, transform value)
sizeIndex (PlanChoice branches) =
    SizeIndex counts select
  where
    offsetBranches _ [] = []
    offsetBranches offset ((branchCardinality, branch) : rest) =
        (offset, sizeIndex branch) : offsetBranches (offset + branchCardinality) rest
    entries = offsetBranches 0 branches
    counts = foldr (addPoly . sizeClassCounts . snd) [] entries

    select size = go entries
      where
        go [] _ = error "sizeIndex: index outside choice size class"
        go ((offset, inner) : rest) index
            | index < count =
                let (rank, value) = sizeClassSelect inner size index
                 in (offset + rank, value)
            | otherwise = go rest (index - count)
          where
            count = countAtSize inner size
sizeIndex (PlanAp radix planF planX) =
    SizeIndex counts select
  where
    indexF = sizeIndex planF
    indexX = sizeIndex planX
    -- A product needs one choice from each side, so the smallest product is
    -- size two: the convolution starts one size later than its operands.
    counts = 0 : mulPoly (sizeClassCounts indexF) (sizeClassCounts indexX)

    select size = go [(functionSize, size - functionSize) | functionSize <- [1 .. size - 1]]
      where
        go [] _ = error "sizeIndex: index outside product size class"
        go ((functionSize, argumentSize) : rest) index
            | index < block =
                let (functionIndex, argumentIndex) = index `quotRem` countAtSize indexX argumentSize
                    (functionRank, function) = sizeClassSelect indexF functionSize functionIndex
                    (argumentRank, argument) = sizeClassSelect indexX argumentSize argumentIndex
                 in (functionRank * radix + argumentRank, function argument)
            | otherwise = go rest (index - block)
          where
            block = countAtSize indexF functionSize * countAtSize indexX argumentSize

-- | Add two size-count vectors, keeping the longer tail.
addPoly :: [Integer] -> [Integer] -> [Integer]
addPoly [] ys = ys
addPoly xs [] = xs
addPoly (x : xs) (y : ys) = x + y : addPoly xs ys

{- | Convolve two size-count vectors.

Productive on infinite operands: every output element needs only finite
prefixes of both, so recursive languages can be counted lazily.
-}
mulPoly :: [Integer] -> [Integer] -> [Integer]
mulPoly [] _ = []
mulPoly _ [] = []
mulPoly (x : xs) allYs@(y : ys) =
    x * y : addPoly (map (x *) ys) (mulPoly xs allYs)
