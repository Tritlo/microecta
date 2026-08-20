{- | Size-stratified counting and indexing.

A language's members split into size classes, where size is the number of
source choices in a member: an atom has size one, and an application adds
the sizes of its operation and argument choices. A t'SizeIndex' counts every
class by FEAT-style convolution — a product of size @s@ splits into an
operation of size @a@ and arguments of size @s - a@ — and indexes into one
directly, returning the member's rank alongside its value.

Two kinds of index share the type. 'sizeIndex' reads a finite 'Plan' and
reports that plan's own mixed-radix rank, so counting a class never changes
what a rank means. The combinators ('mapIndex', 'productIndex',
'choiceIndex', 'fixIndex') build languages that may be recursive, where
mixed radix has no meaning because a side can be unbounded; those report a
size-major rank instead, the position of the member in the size-ordered
enumeration. Either way the rank is the one canonical rank of the
generator it came from.

Convolution is productive on infinite operands, which is what makes
'fixIndex' work: a recursive occurrence contributes to size @s@ only
through products, and a product needs one choice from each side, so
counting size @s@ only ever consults sizes below it.
-}
module Data.ECTA.Gen.Internal.Size (
    SizeIndex (sizeClassCounts, sizeClassSelect),
    probeIndex,
    isUnguarded,
    usesOccurrence,
    sizeIndex,
    countAtSize,
    countUpToSize,
    sizeClassOf,
    constantIndex,
    mapIndex,
    productIndex,
    choiceIndex,
    fixIndex,
    sizeClasses,
) where

import Data.ECTA.Gen.Internal.Decoder (Plan (..))

{- | The size classes of one language: how many members each holds, and how
to select one by its position in the class.
-}
data SizeIndex a = SizeIndex
    { sizeClassCounts :: [Integer]
    -- ^ Members per size, for ascending sizes from one.
    , sizeClassSelect :: Int -> Integer -> (Integer, a)
    -- ^ Rank and value of one member of one size class.
    , sizeClassValueInt :: Int -> Int -> a
    {- ^ Value of one member using machine arithmetic. Called only when the
    requested size class fits in 'Int'.
    -}
    , unguardedOccurrence :: Bool
    {- ^ Whether a 'probeIndex' can be reached without passing through a
    product. Counting such an index would consult its own size, so a
    recursive definition shaped this way has no smallest member.
    -}
    , usedOccurrence :: Bool
    {- ^ Whether a 'probeIndex' is reachable at all. A recursive definition
    whose body never reaches its own occurrence is not recursive.
    -}
    }

{- | A stand-in for a recursive occurrence, used to check that a recursive
definition is guarded before it is tied.

Only its 'unguardedOccurrence' is ever read: building a language around a
probe answers whether the recursion passes through a product without
counting anything.
-}
probeIndex :: SizeIndex a
probeIndex =
    SizeIndex
        ( error
            "microecta-generator bug in Data.ECTA.Gen.Internal.Size.probeIndex: \
            \a probe counts no size classes; only its two flags are read"
        )
        ( error
            "microecta-generator bug in Data.ECTA.Gen.Internal.Size.probeIndex: \
            \a probe decodes no members; only its two flags are read"
        )
        ( error
            "microecta-generator bug in Data.ECTA.Gen.Internal.Size.probeIndex: \
            \a probe decodes no members; only its two flags are read"
        )
        True
        True

{- | Whether a language built around 'probeIndex' left the occurrence
unguarded, so that counting it would not terminate.
-}
isUnguarded :: SizeIndex a -> Bool
isUnguarded = unguardedOccurrence

{- | Whether a language built around 'probeIndex' reaches the occurrence at
all. A body that does not is a language in its own right, not a recursive
one.
-}
usesOccurrence :: SizeIndex a -> Bool
usesOccurrence = usedOccurrence

-- | The number of members of one size, zero outside the counted sizes.
countAtSize :: SizeIndex a -> Int -> Integer
countAtSize index size
    | size < 1 = 0
    | otherwise = case drop (size - 1) (sizeClassCounts index) of
        count : _ -> count
        [] -> 0

-- | The number of members of size at most the bound.
countUpToSize :: SizeIndex a -> Int -> Integer
countUpToSize index bound = sum $ take bound $ sizeClassCounts index

{- | The size class holding one rank, with the rank rebased into it.

Only meaningful for a size-major index. 'Nothing' means the rank is outside
the language, which can only be discovered for a language with finitely
many size classes.
-}
sizeClassOf :: SizeIndex a -> Integer -> Maybe (Int, Integer)
sizeClassOf index rank
    | rank < 0 = Nothing
    | otherwise = go 1 rank $ sizeClassCounts index
  where
    go _ _ [] = Nothing
    go size position (count : rest)
        | position < count = Just (size, position)
        | otherwise = go (size + 1) (position - count) rest

{- | The non-empty size classes up to a bound, as size, count, and a decoder
for one position in that class.

This is the bridge back to a finite language: a recursive index bounded this
way becomes an ordinary 'PlanSized' plan whose ranks are size-major.
-}
sizeClasses :: Int -> SizeIndex a -> [(Int, Integer, Integer -> a, Int -> a)]
sizeClasses bound index =
    [ ( size
      , count
      , snd . sizeClassSelect index size
      , sizeClassValueInt index size
      )
    | (size, count) <- zip [1 ..] (take bound (sizeClassCounts index))
    , count > 0
    ]

-- | Count and index the size classes of a finite plan, keeping its ranks.
sizeIndex :: Plan a -> SizeIndex a
sizeIndex (PlanSelect cardinality' decode) =
    SizeIndex [cardinality'] select selectInt False False
  where
    select 1 position = (position, decode position)
    select size _ =
        error $
            "microecta-generator bug in Data.ECTA.Gen.Internal.Size.sizeIndex: \
            \a leaf has no members of size "
                <> show size
    selectInt 1 position = decode $ toInteger position
    selectInt size _ =
        error $
            "microecta-generator bug in Data.ECTA.Gen.Internal.Size.sizeIndex: \
            \a leaf has no members of size "
                <> show size
sizeIndex (PlanMap transform plan) = mapIndex transform $ sizeIndex plan
sizeIndex (PlanChoice branches) =
    SizeIndex counts select selectInt False False
  where
    entries = offsetBranches 0 branches
    offsetBranches _ [] = []
    offsetBranches offset ((branchCardinality, branch) : rest) =
        (offset, sizeIndex branch) : offsetBranches (offset + branchCardinality) rest
    counts = foldr (addPoly . sizeClassCounts . snd) [] entries

    select size position =
        let (offset, inner, rebased) = partAt size entries position
            (rank, value) = sizeClassSelect inner size rebased
         in (offset + rank, value)
    selectInt size position =
        let (inner, rebased) = partAtInt size (map snd entries) position
         in sizeClassValueInt inner size rebased
sizeIndex (PlanAp radix planF planX) =
    SizeIndex counts select selectInt False False
  where
    indexF = sizeIndex planF
    indexX = sizeIndex planX
    counts = productCounts indexF indexX

    select size position =
        let (functionSize, functionPosition, argumentSize, argumentPosition) =
                productSplit indexF indexX size position
            (functionRank, function) = sizeClassSelect indexF functionSize functionPosition
            (argumentRank, argument) = sizeClassSelect indexX argumentSize argumentPosition
         in (functionRank * radix + argumentRank, function argument)
    selectInt size position =
        let (functionSize, functionPosition, argumentSize, argumentPosition) =
                productSplitInt indexF indexX size position
            function = sizeClassValueInt indexF functionSize functionPosition
            argument = sizeClassValueInt indexX argumentSize argumentPosition
         in function argument
sizeIndex (PlanSized classes) =
    SizeIndex counts select selectInt False False
  where
    counts = classCounts classes
    offsets = offsetClasses 0 classes
    offsetClasses _ [] = []
    offsetClasses offset ((size, count, decode, decodeInt) : rest) =
        (size, offset, count, decode, decodeInt) : offsetClasses (offset + count) rest

    select size position = case [entry | entry@(size', _, _, _, _) <- offsets, size' == size] of
        (_, offset, _, decode, _) : _ -> (offset + position, decode position)
        [] ->
            error $
                "microecta-generator bug in Data.ECTA.Gen.Internal.Size.sizeIndex: \
                \no size class of size "
                    <> show size
    selectInt size position = case [entry | entry@(size', _, _, _, _) <- offsets, size' == size] of
        (_, _, _, _, decodeInt) : _ -> decodeInt position
        [] ->
            error $
                "microecta-generator bug in Data.ECTA.Gen.Internal.Size.sizeIndex: \
                \no size class of size "
                    <> show size

-- | The one-member index of a single value, of size one.
constantIndex :: a -> SizeIndex a
constantIndex value =
    SizeIndex [1] select selectInt False False
  where
    select 1 0 = (0, value)
    select size position =
        error $
            "microecta-generator bug in Data.ECTA.Gen.Internal.Size.constantIndex: \
            \no member at size "
                <> show size
                <> " position "
                <> show position
    selectInt 1 0 = value
    selectInt size position =
        error $
            "microecta-generator bug in Data.ECTA.Gen.Internal.Size.constantIndex: \
            \no member at size "
                <> show size
                <> " position "
                <> show position

-- | Map the values of an index, keeping its counts and ranks.
mapIndex :: (a -> b) -> SizeIndex a -> SizeIndex b
mapIndex transform index =
    SizeIndex
        (sizeClassCounts index)
        select
        selectInt
        (unguardedOccurrence index)
        (usedOccurrence index)
  where
    select size position =
        let (rank, value) = sizeClassSelect index size position
         in (rank, transform value)
    selectInt size = transform . sizeClassValueInt index size

{- | The product of two indexes, ranked size-major.

Within a size class, splits come in ascending operation size, and each split
is ordered operation-major. Either side may be recursive.
-}
productIndex :: SizeIndex (a -> b) -> SizeIndex a -> SizeIndex b
-- A product consumes one choice from each side, so counting a size only
-- consults smaller ones: this is what guards a recursive occurrence.
productIndex indexF indexX =
    SizeIndex
        counts
        select
        selectInt
        False
        (usedOccurrence indexF || usedOccurrence indexX)
  where
    counts = productCounts indexF indexX
    ranks = sizeMajorRanks counts

    select size position =
        let (functionSize, functionPosition, argumentSize, argumentPosition) =
                productSplit indexF indexX size position
            (_, function) = sizeClassSelect indexF functionSize functionPosition
            (_, argument) = sizeClassSelect indexX argumentSize argumentPosition
         in (rankAt ranks size position, function argument)
    selectInt size position =
        let (functionSize, functionPosition, argumentSize, argumentPosition) =
                productSplitInt indexF indexX size position
            function = sizeClassValueInt indexF functionSize functionPosition
            argument = sizeClassValueInt indexX argumentSize argumentPosition
         in function argument

{- | Ordered alternatives, ranked size-major.

Within a size class the alternatives keep their order. Any alternative may
be recursive.
-}
choiceIndex :: [SizeIndex a] -> SizeIndex a
choiceIndex branches =
    SizeIndex
        counts
        select
        selectInt
        (any unguardedOccurrence branches)
        (any usedOccurrence branches)
  where
    counts = foldr (addPoly . sizeClassCounts) [] branches
    ranks = sizeMajorRanks counts
    entries = [((), branch) | branch <- branches]

    select size position =
        let (_, inner, rebased) = partAt size entries position
            (_, value) = sizeClassSelect inner size rebased
         in (rankAt ranks size position, value)
    selectInt size position =
        let (inner, rebased) = partAtInt size branches position
         in sizeClassValueInt inner size rebased

{- | Tie a recursive index: the body is built from the index being defined.

The recursion must be guarded — every recursive occurrence under at least
one 'productIndex' — so that counting a size only consults smaller sizes.
Callers check that with 'probeIndex' first, because an unguarded knot
diverges rather than failing.
-}
fixIndex :: (SizeIndex a -> SizeIndex a) -> SizeIndex a
fixIndex build = index
  where
    index = build index

-- | Cumulative counts: the rank the first member of each size class takes.
sizeMajorRanks :: [Integer] -> [Integer]
sizeMajorRanks = scanl (+) 0

-- | The size-major rank of one position in one size class.
rankAt :: [Integer] -> Int -> Integer -> Integer
rankAt ranks size position = case drop (size - 1) ranks of
    rank : _ -> rank + position
    [] ->
        error $
            "microecta-generator bug in Data.ECTA.Gen.Internal.Size.rankAt: \
            \no size class of size "
                <> show size

-- | Size counts of a product: one choice from each side, so sizes add.
productCounts :: SizeIndex (a -> b) -> SizeIndex a -> [Integer]
productCounts indexF indexX =
    -- A product needs one choice from each side, so the smallest product is
    -- size two: the convolution starts one size later than its operands.
    0 : mulPoly (sizeClassCounts indexF) (sizeClassCounts indexX)

-- | Size counts of an already stratified language.
classCounts :: [(Int, Integer, Integer -> a, Int -> a)] -> [Integer]
classCounts classes = go 1 classes
  where
    go _ [] = []
    go size all'@((classSize, count, _, _) : rest)
        | size < classSize = 0 : go (size + 1) all'
        | otherwise = count : go (size + 1) rest

{- | The alternative holding one position of a size class, with the position
rebased into it.
-}
partAt :: Int -> [(offset, SizeIndex a)] -> Integer -> (offset, SizeIndex a, Integer)
partAt size = go
  where
    go [] _ =
        error
            "microecta-generator bug in Data.ECTA.Gen.Internal.Size.sizeIndex: \
            \position outside the size class"
    go ((offset, inner) : rest) position
        | position < count = (offset, inner, position)
        | otherwise = go rest (position - count)
      where
        count = countAtSize inner size

-- | The branch holding one machine-sized position in a size class.
partAtInt :: Int -> [SizeIndex a] -> Int -> (SizeIndex a, Int)
partAtInt size = go
  where
    go [] _ =
        error
            "microecta-generator bug in Data.ECTA.Gen.Internal.Size.sizeIndex: \
            \position outside the size class"
    go (inner : rest) position
        | position < count = (inner, position)
        | otherwise = go rest (position - count)
      where
        count = fromInteger $ countAtSize inner size

{- | The split of a product size class holding one position, as the size and
position of each side.
-}
productSplit ::
    SizeIndex (a -> b) ->
    SizeIndex a ->
    Int ->
    Integer ->
    (Int, Integer, Int, Integer)
productSplit indexF indexX size = go [1 .. size - 1]
  where
    go [] _ =
        error
            "microecta-generator bug in Data.ECTA.Gen.Internal.Size.sizeIndex: \
            \position outside the product size class"
    go (functionSize : rest) position
        | position < block =
            let (functionPosition, argumentPosition) = position `quotRem` argumentCount
             in (functionSize, functionPosition, size - functionSize, argumentPosition)
        | otherwise = go rest (position - block)
      where
        argumentCount = countAtSize indexX (size - functionSize)
        block = countAtSize indexF functionSize * argumentCount

-- | Split one machine-sized product position without widening its arithmetic.
productSplitInt ::
    SizeIndex (a -> b) ->
    SizeIndex a ->
    Int ->
    Int ->
    (Int, Int, Int, Int)
productSplitInt indexF indexX size = go [1 .. size - 1]
  where
    go [] _ =
        error
            "microecta-generator bug in Data.ECTA.Gen.Internal.Size.sizeIndex: \
            \position outside the product size class"
    go (functionSize : rest) position
        | position < block =
            let (functionPosition, argumentPosition) = position `quotRem` argumentCount
             in (functionSize, functionPosition, size - functionSize, argumentPosition)
        | otherwise = go rest (position - block)
      where
        argumentCount = fromInteger $ countAtSize indexX (size - functionSize)
        functionCount = fromInteger $ countAtSize indexF functionSize
        block = functionCount * argumentCount

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
