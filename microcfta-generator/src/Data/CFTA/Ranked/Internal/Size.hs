{- | Size-stratified counting and indexing.

A language's members split into size classes, where size is the number of
source choices in a member: an atom has size one, and an application adds
the sizes of its operation and argument choices. A t'SizeIndex' counts every
class by FEAT-style convolution (a product of size @s@ splits into an
operation of size @a@ and arguments of size @s - a@) and indexes into one
directly, returning the member's rank alongside its value.

Two kinds of index share the type. 'sizeIndex' reads a finite 'Plan' and
reports that plan's own mixed-radix rank, so counting a class never changes
what a rank means. The combinators ('mapIndex', 'productIndex',
'choiceIndex', 'fixIndex') build languages that may be recursive, where
mixed radix has no meaning because a side can be unbounded; those report a
size-major rank instead, the position of the member in the size-ordered
enumeration. Either way the rank is the one canonical rank of the
generator it came from: the compiled decoder of a finite plan reads the
mixed-radix rank, and 'unrank' of a recursive generator reads the size-major
rank. The callers that take the rank part of 'sizeClassSelect' on a finite plan
index use it as a plan rank, and the others take the value or compute the
size-major rank from the counts.

The counts are sparse: sizes in ascending order, each with its count. A
shared automaton can have members of astronomical size and only a few
distinct sizes, so the work follows the size classes that exist, not the
range of sizes. A 'Data.CFTA.Index.Size' holds an 'Integer' for the same
reason. A count can be zero: a product in a recursive definition starts with a
zero count at size one, and that entry flows into the counts built from it.

Convolution is productive on infinite operands, which is what makes
'fixIndex' work: a recursive occurrence contributes to size @s@ only
through products, and a product needs one choice from each side, so
counting size @s@ only ever consults sizes below it.

This module is an exposed internal module. The generator layers of
microcfta-generator use it directly. Its exports are not covered by the PVP
contract of the package.
-}
module Data.CFTA.Ranked.Internal.Size (
    SizeCounts,
    SizeIndex (sizeClassCounts, sizeClassSelect, minimumMemberSize),
    probeIndex,
    probeIndexWithMinimum,
    closedProbe,
    isUnguarded,
    usesOccurrence,
    sizeIndex,
    countAtSize,
    sizeClassOf,
    constantIndex,
    mapIndex,
    productIndex,
    choiceIndex,
    fixIndex,
    withKnotMetadata,
    sizeClasses,
    addSparse,
    mulSparse,
    valueAtSize,
) where

import Data.CFTA.Index (
    Cardinality (..),
    ClassRank (..),
    Rank (..),
    RankOffset,
    Size (..),
    classMemberRank,
    nextOffset,
    offsetRank,
    pairRank,
 )
import Data.CFTA.Ranked.Internal.Decoder (Plan (..), SizeClass (..), SizeCounts, SizeIndex (..))

{- | A stand-in for a recursive occurrence, used to check that a recursive
definition is guarded before it is tied.

Only its metadata is ever read: building a language around a probe answers
whether the recursion passes through a product and whether it can close to a
finite member, without counting anything.
-}
probeIndex :: SizeIndex a
probeIndex = probeIndexWithMinimum Nothing

{- | A recursive-occurrence probe with an assumed minimum.

Grouped recursion uses this to solve the least live size of mutually
recursive keys without forcing their count knots.
-}
probeIndexWithMinimum :: Maybe Size -> SizeIndex a
probeIndexWithMinimum minimumSize' =
    SizeIndex
        ( error
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.probeIndex: \
            \a probe counts no size classes; only its metadata is read"
        )
        ( error
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.probeIndex: \
            \a probe decodes no members; only its metadata is read"
        )
        ( error
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.probeIndex: \
            \a probe decodes no members; only its metadata is read"
        )
        minimumSize'
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
countAtSize :: SizeIndex a -> Size -> Cardinality
countAtSize index = valueAtSize (sizeClassCounts index)

{- | The size class holding one rank, with the rank rebased into it.

Only meaningful for a size-major index. 'Nothing' means the rank is outside
the language, which can only be discovered for a language with finitely
many size classes.
-}
sizeClassOf :: SizeIndex a -> Rank -> Maybe (Size, ClassRank)
sizeClassOf index (Rank rank)
    | rank < 0 = Nothing
    | otherwise = go rank $ sizeClassCounts index
  where
    go _ [] = Nothing
    go position ((size, Cardinality count) : rest)
        | position < count = Just (size, ClassRank position)
        | otherwise = go (position - count) rest

{- | The non-empty size classes up to a bound.

This is the bridge back to a finite language: a recursive index bounded this
way becomes an ordinary 'PlanSized' plan whose ranks are size-major.
-}
sizeClasses :: Size -> SizeIndex a -> [SizeClass a]
sizeClasses bound index =
    [ SizeClass size count (snd . sizeClassSelect index size) (sizeClassValueInt index size)
    | (size, count) <- takeWhile ((<= bound) . fst) (sizeClassCounts index)
    , count > 0
    ]

-- | Count and index the size classes of a finite plan, keeping its ranks.
sizeIndex :: Plan a -> SizeIndex a
sizeIndex (PlanSelect cardinality' decode) =
    SizeIndex [(1, cardinality') | cardinality' > 0] select selectInt minimumSize' False False
  where
    minimumSize'
        | cardinality' > 0 = Just 1
        | otherwise = Nothing
    -- A leaf has one size class, so a rank in that class is a rank.
    select 1 (ClassRank classRank) = let rank = Rank classRank in (rank, decode rank)
    select size _ =
        error $
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.sizeIndex: \
            \a leaf has no members of size "
                <> show size
    selectInt 1 position = decode $ Rank $ toInteger position
    selectInt size _ =
        error $
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.sizeIndex: \
            \a leaf has no members of size "
                <> show size
sizeIndex (PlanSelectOnDemand cardinality' decode) =
    sizeIndex $ PlanSelect cardinality' decode
sizeIndex (PlanShared _ _ index _) = index
sizeIndex (PlanMap transform plan) = mapIndex transform $ sizeIndex plan
sizeIndex (PlanChoice branches) =
    SizeIndex counts select selectInt minimumSize' False False
  where
    entries = offsetBranches 0 branches
    offsetBranches _ [] = []
    offsetBranches offset ((branchCardinality, branch) : rest) =
        (offset, sizeIndex branch) : offsetBranches (nextOffset offset branchCardinality) rest
    counts = foldr (addCounts . sizeClassCounts . snd) [] entries
    minimumSize' = minimumOf $ map (minimumMemberSize . snd) entries

    select size position =
        let (offset, inner, rebased) = partAt size entries position
            (rank, value) = sizeClassSelect inner size rebased
         in (offsetRank offset rank, value)
    selectInt size position =
        let (inner, rebased) = partAtInt size (map snd entries) position
         in sizeClassValueInt inner size rebased
sizeIndex (PlanAp radix planF planX) =
    SizeIndex counts select selectInt minimumSize' False False
  where
    indexF = sizeIndex planF
    indexX = sizeIndex planX
    counts = productCounts indexF indexX
    minimumSize' = (+) <$> minimumMemberSize indexF <*> minimumMemberSize indexX

    select size position =
        let (functionSize, functionPosition, argumentSize, argumentPosition) =
                productSplit indexF indexX size position
            (functionRank, function) = sizeClassSelect indexF functionSize functionPosition
            (argumentRank, argument) = sizeClassSelect indexX argumentSize argumentPosition
         in (pairRank radix functionRank argumentRank, function argument)
    selectInt size position =
        let (functionSize, functionPosition, argumentSize, argumentPosition) =
                productSplitInt indexF indexX size position
            function = sizeClassValueInt indexF functionSize functionPosition
            argument = sizeClassValueInt indexX argumentSize argumentPosition
         in function argument
sizeIndex (PlanSized classes) =
    SizeIndex counts select selectInt minimumSize' False False
  where
    counts = [(size, count) | SizeClass{classSize = size, classCardinality = count} <- classes, count > 0]
    minimumSize' = case [size | SizeClass{classSize = size, classCardinality = count} <- classes, count > 0] of
        [] -> Nothing
        liveSizes -> Just $ minimum liveSizes
    offsets = offsetClasses 0 classes
    offsetClasses _ [] = []
    offsetClasses offset (sizeClass@SizeClass{classCardinality = count} : rest) =
        (offset, sizeClass) : offsetClasses (nextOffset offset count) rest

    select size position = case [entry | entry@(_, SizeClass{classSize = size'}) <- offsets, size' == size] of
        (offset, SizeClass{classMember = decode}) : _ -> (classMemberRank offset position, decode position)
        [] ->
            error $
                "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.sizeIndex: \
                \no size class of size "
                    <> show size
    selectInt size position = case [entry | entry@(_, SizeClass{classSize = size'}) <- offsets, size' == size] of
        (_, SizeClass{classMemberInt = decodeInt}) : _ -> decodeInt position
        [] ->
            error $
                "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.sizeIndex: \
                \no size class of size "
                    <> show size

-- | The one-member index of a single value, of size one.
constantIndex :: a -> SizeIndex a
constantIndex value =
    SizeIndex [(1, 1)] select selectInt (Just 1) False False
  where
    select 1 0 = (0, value)
    select size position =
        error $
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.constantIndex: \
            \no member at size "
                <> show size
                <> " position "
                <> show position
    selectInt 1 0 = value
    selectInt size position =
        error $
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.constantIndex: \
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
        (minimumMemberSize index)
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
        ((+) <$> minimumMemberSize indexF <*> minimumMemberSize indexX)
        False
        (usedOccurrence indexF || usedOccurrence indexX)
  where
    -- The zero count at size one lets a recursive definition that uses this
    -- product give its own smallest members before the product is counted:
    -- every product has size two or more.
    counts = (1, 0) : productCounts indexF indexX
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
        (minimumOf $ map minimumMemberSize branches)
        (any unguardedOccurrence branches)
        (any usedOccurrence branches)
  where
    counts = foldr (addCounts . sizeClassCounts) [] branches
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

The recursion must be guarded (every recursive occurrence under at least
one 'productIndex'), so that counting a size only consults smaller sizes.
Callers check that with 'probeIndex' first, because an unguarded knot
diverges rather than failing.
-}
fixIndex :: (SizeIndex a -> SizeIndex a) -> SizeIndex a
fixIndex build = index
  where
    index = withKnotMetadata (minimumMemberSize $ build probeIndex) (build closedProbe) (build index)

{- | An occurrence of a definition that is already tied. No probe is reached
through it: the definition answered its own probe when it was tied.
-}
closedProbe :: SizeIndex a
closedProbe = probeIndex{unguardedOccurrence = False, usedOccurrence = False}

{- | Give a tied index a minimum and the occurrence flags of a build that does
not read the knot, leaving counts and decoding unchanged.

The flags of the tied index itself read the index again, so a definition
that reads them before its own occurrence does not terminate. A build around
'closedProbe' gives the same answer for every enclosing probe. The result is
a new record, not an update of the index: an update would evaluate the index,
and a nested definition in its body can read the flags of this one.
-}
withKnotMetadata :: Maybe Size -> SizeIndex b -> SizeIndex a -> SizeIndex a
withKnotMetadata minimumSize' closed index =
    SizeIndex
        { sizeClassCounts = sizeClassCounts index
        , sizeClassSelect = sizeClassSelect index
        , sizeClassValueInt = sizeClassValueInt index
        , minimumMemberSize = minimumSize'
        , unguardedOccurrence = unguardedOccurrence closed
        , usedOccurrence = usedOccurrence closed
        }

-- | The least present value, ignoring absent entries.
minimumOf :: [Maybe Size] -> Maybe Size
minimumOf = foldr combine Nothing
  where
    combine Nothing current = current
    combine current Nothing = current
    combine (Just left) (Just right) = Just $ min left right

-- | Each size class with the rank that its first member takes.
sizeMajorRanks :: SizeCounts -> [(Size, RankOffset)]
sizeMajorRanks counts = zip (map fst counts) (scanl nextOffset 0 (map snd counts))

-- | The size-major rank of one position in one size class.
rankAt :: [(Size, RankOffset)] -> Size -> ClassRank -> Rank
rankAt ranks size position = case dropWhile ((< size) . fst) ranks of
    (found, offset) : _ | found == size -> classMemberRank offset position
    _ ->
        error $
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.rankAt: \
            \no size class of size "
                <> show size

-- | Size counts of a product: one choice from each side, so sizes add.
productCounts :: SizeIndex (a -> b) -> SizeIndex a -> SizeCounts
productCounts indexF indexX = mulCounts (sizeClassCounts indexF) (sizeClassCounts indexX)

{- | The alternative holding one position of a size class, with the position
rebased into it.
-}
partAt :: Size -> [(offset, SizeIndex a)] -> ClassRank -> (offset, SizeIndex a, ClassRank)
partAt size parts (ClassRank start) = go parts start
  where
    go [] _ =
        error
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.partAt: \
            \position outside the size class"
    go ((offset, inner) : rest) position
        | position < count = (offset, inner, ClassRank position)
        | otherwise = go rest (position - count)
      where
        Cardinality count = countAtSize inner size

-- | The branch holding one machine-sized position in a size class.
partAtInt :: Size -> [SizeIndex a] -> Int -> (SizeIndex a, Int)
partAtInt size = go
  where
    go [] _ =
        error
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.partAtInt: \
            \position outside the size class"
    go (inner : rest) position
        | position < count = (inner, position)
        | otherwise = go rest (position - count)
      where
        count = case countAtSize inner size of
            Cardinality wide -> fromInteger wide

{- | The split of a product size class holding one position, as the size and
position of each side.
-}
productSplit ::
    SizeIndex (a -> b) ->
    SizeIndex a ->
    Size ->
    ClassRank ->
    (Size, ClassRank, Size, ClassRank)
productSplit indexF indexX size (ClassRank start) = go (takeWhile ((< size) . fst) (sizeClassCounts indexF)) start
  where
    go [] _ =
        error
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.productSplit: \
            \position outside the product size class"
    go ((functionSize, Cardinality functionCount) : rest) position
        | position < block =
            let (functionPosition, argumentPosition) = position `quotRem` argumentCount
             in (functionSize, ClassRank functionPosition, size - functionSize, ClassRank argumentPosition)
        | otherwise = go rest (position - block)
      where
        Cardinality argumentCount = countAtSize indexX (size - functionSize)
        block = functionCount * argumentCount

-- | Split one machine-sized product position without widening its arithmetic.
productSplitInt ::
    SizeIndex (a -> b) ->
    SizeIndex a ->
    Size ->
    Int ->
    (Size, Int, Size, Int)
productSplitInt indexF indexX size = go $ takeWhile ((< size) . fst) (sizeClassCounts indexF)
  where
    go [] _ =
        error
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.productSplitInt: \
            \position outside the product size class"
    go ((functionSize, Cardinality functionCount) : rest) position
        | position < block =
            let (functionPosition, argumentPosition) = position `quotRem` argumentCount
             in (functionSize, functionPosition, size - functionSize, argumentPosition)
        | otherwise = go rest (position - block)
      where
        argumentCount = case countAtSize indexX (size - functionSize) of
            Cardinality wide -> fromInteger wide
        block = fromInteger functionCount * argumentCount

-- | Add two sparse counts, merging their sizes.
addCounts :: SizeCounts -> SizeCounts -> SizeCounts
addCounts = addSparse

-- | Convolve two sparse counts: the sizes of a pair add, and the counts multiply.
mulCounts :: SizeCounts -> SizeCounts -> SizeCounts
mulCounts = mulSparse

{- | Add two sparse series of values by size, merging their sizes. Each series
lists the sizes with a nonzero value, in ascending order.
-}
addSparse :: (Num value) => [(Size, value)] -> [(Size, value)] -> [(Size, value)]
addSparse [] right = right
addSparse left [] = left
addSparse left@((leftSize, leftValue) : leftRest) right@((rightSize, rightValue) : rightRest)
    | leftSize < rightSize = (leftSize, leftValue) : addSparse leftRest right
    | rightSize < leftSize = (rightSize, rightValue) : addSparse left rightRest
    | otherwise = (leftSize, leftValue + rightValue) : addSparse leftRest rightRest

{- | Convolve two sparse series: the sizes of a pair add, and the values
multiply.

Productive on infinite operands: the first pair is the smallest sum, and every
later element needs only finite prefixes of both, so recursive languages can
be counted lazily.
-}
mulSparse :: (Num value) => [(Size, value)] -> [(Size, value)] -> [(Size, value)]
mulSparse [] _ = []
mulSparse _ [] = []
mulSparse ((leftSize, leftValue) : leftRest) right@((rightSize, rightValue) : rightRest) =
    (leftSize + rightSize, leftValue * rightValue)
        : addSparse
            [(leftSize + size, leftValue * value) | (size, value) <- rightRest]
            (mulSparse leftRest right)

-- | The value of one size in a sparse series, zero when the size is absent.
valueAtSize :: (Num value) => [(Size, value)] -> Size -> value
valueAtSize series size = case dropWhile ((< size) . fst) series of
    (found, value) : _ | found == size -> value
    _ -> 0
