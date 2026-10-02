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
range of sizes. Sizes are 'Integer' for the same reason. A count can be zero:
a product in a recursive definition starts with a zero count at size one, and
that entry flows into the counts built from it.

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
    SizeIndex (sizeClassCounts, sizeClassSelect, minimumMemberSize, largestMemberSize),
    probeIndexWithMinimum,
    closedProbe,
    isUnguarded,
    usesOccurrence,
    reachesOccurrence,
    sizeIndex,
    countAtSize,
    sizeClassOf,
    sizeMajorRank,
    planPosition,
    productPosition,
    choicePosition,
    constantIndex,
    mapIndex,
    mapIndexWithRank,
    productIndex,
    choiceIndex,
    fixIndex,
    withKnotMetadata,
    sizeClasses,
    addSparse,
    mulSparse,
    valueAtSize,
) where

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Data.CFTA.Ranked.Internal.Decoder (Plan (..), planCardinality)

-- | Members per size: sizes in ascending order, each with its count, which can be zero.
type SizeCounts = [(Integer, Integer)]

{- | The size classes of one language: how many members each holds, and how
to select one by its position in the class.
-}
data SizeIndex a = SizeIndex
    { sizeClassCounts :: SizeCounts
    -- ^ Members per size, for ascending sizes.
    , sizeClassSelect :: Integer -> Integer -> (Integer, a)
    -- ^ Rank and value of one member of one size class.
    , sizeClassValueInt :: Integer -> Int -> a
    {- ^ Value of one member using machine arithmetic. Called only when the
    requested size class fits in 'Int'.
    -}
    , minimumMemberSize :: Maybe Integer
    -- ^ Smallest live size, or 'Nothing' when no finite member is known.
    , largestMemberSize :: Maybe Integer
    {- ^ A size that no member exceeds, when the sizes end. A tied recursion
    gives 'Nothing'.
    -}
    , unguardedOccurrences :: IntSet
    {- ^ The recursions whose probe can be reached without passing through a
    product. Counting such an index would consult its own size, so a
    recursive definition shaped this way has no smallest member.
    -}
    , usedOccurrences :: IntSet
    {- ^ The recursions whose probe is reachable at all. A recursive definition
    whose body never reaches its own occurrence is not recursive.
    -}
    }

{- | A stand-in for the occurrence of one recursion, with an assumed minimum,
used to check that the recursive definition is guarded before it is tied.

The token identifies the recursion. A nested definition can reach the probe
of an enclosing one, so each recursion reads only its own token.

Only its metadata is ever read: building a language around a probe answers
whether the recursion passes through a product and whether it can close to a
finite member, without counting anything.
-}
probeIndexWithMinimum :: Int -> Maybe Integer -> SizeIndex a
probeIndexWithMinimum token minimumSize' =
    SizeIndex
        ( error
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.probeIndexWithMinimum: \
            \a probe counts no size classes; only its metadata is read"
        )
        ( error
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.probeIndexWithMinimum: \
            \a probe decodes no members; only its metadata is read"
        )
        ( error
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.probeIndexWithMinimum: \
            \a probe decodes no members; only its metadata is read"
        )
        minimumSize'
        Nothing
        (IntSet.singleton token)
        (IntSet.singleton token)

{- | Whether a language built around the probe of a token left that
occurrence unguarded, so that counting it would not terminate.
-}
isUnguarded :: Int -> SizeIndex a -> Bool
isUnguarded token = IntSet.member token . unguardedOccurrences

{- | Whether a language built around the probe of a token reaches that
occurrence at all. A body that does not is a language in its own right, not
a recursive one.
-}
usesOccurrence :: Int -> SizeIndex a -> Bool
usesOccurrence token = IntSet.member token . usedOccurrences

{- | Whether a language reaches the probe of any recursion. Such a language
depends on a definition that is not tied yet.
-}
reachesOccurrence :: SizeIndex a -> Bool
reachesOccurrence = not . IntSet.null . usedOccurrences

-- | The number of members of one size, zero outside the counted sizes.
countAtSize :: SizeIndex a -> Integer -> Integer
countAtSize index = valueAtSize (sizeClassCounts index)

{- | The size class holding one rank, with the rank rebased into it.

Only meaningful for a size-major index. 'Nothing' means the rank is outside
the language, which can only be discovered for a language with finitely
many size classes.
-}
sizeClassOf :: SizeIndex a -> Integer -> Maybe (Integer, Integer)
sizeClassOf index rank
    | rank < 0 = Nothing
    | otherwise = go rank $ sizeClassCounts index
  where
    go _ [] = Nothing
    go position ((size, count) : rest)
        | position < count = Just (size, position)
        | otherwise = go (position - count) rest

-- | The size-major rank of one position in one size class: the members of the smaller sizes come first.
sizeMajorRank :: SizeIndex a -> Integer -> Integer -> Integer
sizeMajorRank index size position = countBelow (sizeClassCounts index) size + position

-- | The number of members smaller than one size.
countBelow :: SizeCounts -> Integer -> Integer
countBelow counts size = sum [count | (_, count) <- takeWhile ((< size) . fst) counts]

{- | The size class and the position in it of one rank of a finite plan.

This is the inverse of 'sizeClassSelect' on 'sizeIndex': the rank that
'sizeClassSelect' returns for the size and position is the given rank.
'Nothing' means that the rank is outside the plan.
-}
planPosition :: Plan a -> Integer -> Maybe (Integer, Integer)
planPosition plan rank
    | rank < 0 || rank >= planCardinality plan = Nothing
    | otherwise = case plan of
        PlanSelect _ _ -> Just (1, rank)
        PlanSelectOnDemand _ _ -> Just (1, rank)
        PlanShared _ _ inner -> planPosition inner rank
        PlanMap _ inner -> planPosition inner rank
        PlanChoice branches -> branchPosition [] branches rank
        PlanAp radix planF planX -> do
            let (rankF, rankX) = rank `quotRem` radix
            positionF <- planPosition planF rankF
            positionX <- planPosition planX rankX
            pure $ productPosition (sizeIndex planF) (sizeIndex planX) positionF positionX
        PlanSized classes -> classPosition classes rank
  where
    branchPosition _ [] _ = Nothing
    branchPosition earlier ((count, branch) : rest) remaining
        | remaining < count = do
            (size, position) <- planPosition branch remaining
            pure (size, choicePosition (map sizeIndex $ reverse earlier) (length earlier) size position)
        | otherwise = branchPosition (branch : earlier) rest (remaining - count)
    classPosition [] _ = Nothing
    classPosition ((size, count, _, _) : rest) remaining
        | remaining < count = Just (size, remaining)
        | otherwise = classPosition rest (remaining - count)

{- | The size and the position in its size class of a product member, from
the size and position of its function and of its argument.

Within a size class, splits come in ascending function size, and each split
is ordered function-major, as 'productSplit' reads them.
-}
productPosition :: SizeIndex f -> SizeIndex x -> (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer)
productPosition indexF indexX (sizeF, positionF) (sizeX, positionX) =
    ( size
    , sum
        [ functionCount * countAtSize indexX (size - functionSize)
        | (functionSize, functionCount) <- takeWhile ((< sizeF) . fst) (sizeClassCounts indexF)
        ]
        + positionF * countAtSize indexX sizeX
        + positionX
    )
  where
    size = sizeF + sizeX

{- | The position in one size class of a member of one alternative, from its
position in that alternative's class. The alternatives before it come first,
as 'partAt' reads them.
-}
choicePosition :: [SizeIndex a] -> Int -> Integer -> Integer -> Integer
choicePosition branches branch size position =
    sum [countAtSize earlier size | earlier <- take branch branches] + position

{- | The non-empty size classes up to a bound, as size, count, and a decoder
for one position in that class.

This is the bridge back to a finite language: a recursive index bounded this
way becomes an ordinary 'PlanSized' plan whose ranks are size-major.
-}
sizeClasses :: Integer -> SizeIndex a -> [(Integer, Integer, Integer -> a, Int -> a)]
sizeClasses bound index =
    [ ( size
      , count
      , snd . sizeClassSelect index size
      , sizeClassValueInt index size
      )
    | (size, count) <- takeWhile ((<= bound) . fst) (sizeClassCounts index)
    , count > 0
    ]

-- | Count and index the size classes of a finite plan, keeping its ranks.
sizeIndex :: Plan a -> SizeIndex a
sizeIndex (PlanSelect cardinality' decode) =
    SizeIndex [(1, cardinality') | cardinality' > 0] select selectInt minimumSize' (Just 1) IntSet.empty IntSet.empty
  where
    minimumSize'
        | cardinality' > 0 = Just 1
        | otherwise = Nothing
    select 1 position = (position, decode position)
    select size _ =
        error $
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.sizeIndex: \
            \a leaf has no members of size "
                <> show size
    selectInt 1 position = decode $ toInteger position
    selectInt size _ =
        error $
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.sizeIndex: \
            \a leaf has no members of size "
                <> show size
sizeIndex (PlanSelectOnDemand cardinality' decode) =
    sizeIndex $ PlanSelect cardinality' decode
sizeIndex (PlanShared _ _ plan) = sizeIndex plan
sizeIndex (PlanMap transform plan) = mapIndex transform $ sizeIndex plan
sizeIndex (PlanChoice branches) =
    SizeIndex counts select selectInt minimumSize' largestSize IntSet.empty IntSet.empty
  where
    entries = offsetBranches 0 branches
    offsetBranches _ [] = []
    offsetBranches offset ((branchCardinality, branch) : rest) =
        (offset, sizeIndex branch) : offsetBranches (offset + branchCardinality) rest
    counts = foldr (addCounts . sizeClassCounts . snd) [] entries
    minimumSize' = minimumOf $ map (minimumMemberSize . snd) entries
    largestSize = maximum . (0 :) <$> traverse (largestMemberSize . snd) entries

    select size position =
        let (offset, inner, rebased) = partAt size entries position
            (rank, value) = sizeClassSelect inner size rebased
         in (offset + rank, value)
    selectInt size position =
        let (inner, rebased) = partAtInt size (map snd entries) position
         in sizeClassValueInt inner size rebased
sizeIndex (PlanAp radix planF planX) =
    SizeIndex counts select selectInt minimumSize' largestSize IntSet.empty IntSet.empty
  where
    indexF = sizeIndex planF
    indexX = sizeIndex planX
    counts = productCounts indexF indexX
    minimumSize' = (+) <$> minimumMemberSize indexF <*> minimumMemberSize indexX
    largestSize = (+) <$> largestMemberSize indexF <*> largestMemberSize indexX

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
    SizeIndex counts select selectInt minimumSize' largestSize IntSet.empty IntSet.empty
  where
    counts = [(size, count) | (size, count, _, _) <- classes, count > 0]
    largestSize = Just $ maximum $ 0 : [size | (size, count, _, _) <- classes, count > 0]
    minimumSize' = case [size | (size, count, _, _) <- classes, count > 0] of
        [] -> Nothing
        liveSizes -> Just $ minimum liveSizes
    offsets = offsetClasses 0 classes
    offsetClasses _ [] = []
    offsetClasses offset ((size, count, decode, decodeInt) : rest) =
        (size, offset, count, decode, decodeInt) : offsetClasses (offset + count) rest

    select size position = case [entry | entry@(size', _, _, _, _) <- offsets, size' == size] of
        (_, offset, _, decode, _) : _ -> (offset + position, decode position)
        [] ->
            error $
                "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.sizeIndex: \
                \no size class of size "
                    <> show size
    selectInt size position = case [entry | entry@(size', _, _, _, _) <- offsets, size' == size] of
        (_, _, _, _, decodeInt) : _ -> decodeInt position
        [] ->
            error $
                "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.sizeIndex: \
                \no size class of size "
                    <> show size

-- | The one-member index of a single value, of size one.
constantIndex :: a -> SizeIndex a
constantIndex value =
    SizeIndex [(1, 1)] select selectInt (Just 1) (Just 1) IntSet.empty IntSet.empty
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
        (largestMemberSize index)
        (unguardedOccurrences index)
        (usedOccurrences index)
  where
    select size position =
        let (rank, value) = sizeClassSelect index size position
         in (rank, transform value)
    selectInt size = transform . sizeClassValueInt index size

{- | Map the values of an index with their ranks, keeping its counts and
ranks.
-}
mapIndexWithRank :: (Integer -> a -> b) -> SizeIndex a -> SizeIndex b
mapIndexWithRank transform index =
    SizeIndex
        (sizeClassCounts index)
        select
        (\size -> snd . select size . toInteger)
        (minimumMemberSize index)
        (largestMemberSize index)
        (unguardedOccurrences index)
        (usedOccurrences index)
  where
    select size position =
        let (rank, value) = sizeClassSelect index size position
         in (rank, transform rank value)

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
        ((+) <$> largestMemberSize indexF <*> largestMemberSize indexX)
        IntSet.empty
        (IntSet.union (usedOccurrences indexF) (usedOccurrences indexX))
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
        (maximum . (0 :) <$> traverse largestMemberSize branches)
        (IntSet.unions $ map unguardedOccurrences branches)
        (IntSet.unions $ map usedOccurrences branches)
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
Callers check that with a probe first, because an unguarded knot diverges
rather than failing. The minimum and the flags come from one build around
'closedProbe', which does not read the knot.
-}
fixIndex :: (SizeIndex a -> SizeIndex a) -> SizeIndex a
fixIndex build = index
  where
    closed = build closedProbe
    index = withKnotMetadata (minimumMemberSize closed) closed (build index)

{- | An occurrence of a definition that is already tied. No probe is reached
through it: the definition answered its own probe when it was tied.
-}
closedProbe :: SizeIndex a
closedProbe = (probeIndexWithMinimum 0 Nothing){unguardedOccurrences = IntSet.empty, usedOccurrences = IntSet.empty}

{- | Give a tied index a minimum and the occurrence flags of a build that does
not read the knot, leaving counts and decoding unchanged.

The flags of the tied index itself read the index again, so a definition
that reads them before its own occurrence does not terminate. A build around
'closedProbe' gives the same answer for every enclosing probe. The result is
a new record, not an update of the index: an update would evaluate the index,
and a nested definition in its body can read the flags of this one.
-}
withKnotMetadata :: Maybe Integer -> SizeIndex b -> SizeIndex a -> SizeIndex a
withKnotMetadata minimumSize' closed index =
    SizeIndex
        { sizeClassCounts = sizeClassCounts index
        , sizeClassSelect = sizeClassSelect index
        , sizeClassValueInt = sizeClassValueInt index
        , minimumMemberSize = minimumSize'
        , largestMemberSize = Nothing
        , unguardedOccurrences = unguardedOccurrences closed
        , usedOccurrences = usedOccurrences closed
        }

-- | The least present value, ignoring absent entries.
minimumOf :: [Maybe Integer] -> Maybe Integer
minimumOf = foldr combine Nothing
  where
    combine Nothing current = current
    combine current Nothing = current
    combine (Just left) (Just right) = Just $ min left right

-- | Each size class with the rank that its first member takes.
sizeMajorRanks :: SizeCounts -> [(Integer, Integer)]
sizeMajorRanks counts = zip (map fst counts) (scanl (+) 0 (map snd counts))

-- | The size-major rank of one position in one size class.
rankAt :: [(Integer, Integer)] -> Integer -> Integer -> Integer
rankAt ranks size position = case dropWhile ((< size) . fst) ranks of
    (found, rank) : _ | found == size -> rank + position
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
partAt :: Integer -> [(offset, SizeIndex a)] -> Integer -> (offset, SizeIndex a, Integer)
partAt size = go
  where
    go [] _ =
        error
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.partAt: \
            \position outside the size class"
    go ((offset, inner) : rest) position
        | position < count = (offset, inner, position)
        | otherwise = go rest (position - count)
      where
        count = countAtSize inner size

-- | The branch holding one machine-sized position in a size class.
partAtInt :: Integer -> [SizeIndex a] -> Int -> (SizeIndex a, Int)
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
        count = fromInteger $ countAtSize inner size

{- | The split of a product size class holding one position, as the size and
position of each side.
-}
productSplit ::
    SizeIndex (a -> b) ->
    SizeIndex a ->
    Integer ->
    Integer ->
    (Integer, Integer, Integer, Integer)
productSplit indexF indexX size = go $ takeWhile ((< size) . fst) (sizeClassCounts indexF)
  where
    go [] _ =
        error
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.productSplit: \
            \position outside the product size class"
    go ((functionSize, functionCount) : rest) position
        | position < block =
            let (functionPosition, argumentPosition) = position `quotRem` argumentCount
             in (functionSize, functionPosition, size - functionSize, argumentPosition)
        | otherwise = go rest (position - block)
      where
        argumentCount = countAtSize indexX (size - functionSize)
        block = functionCount * argumentCount

-- | Split one machine-sized product position without widening its arithmetic.
productSplitInt ::
    SizeIndex (a -> b) ->
    SizeIndex a ->
    Integer ->
    Int ->
    (Integer, Int, Integer, Int)
productSplitInt indexF indexX size = go $ takeWhile ((< size) . fst) (sizeClassCounts indexF)
  where
    go [] _ =
        error
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.productSplitInt: \
            \position outside the product size class"
    go ((functionSize, functionCount) : rest) position
        | position < block =
            let (functionPosition, argumentPosition) = position `quotRem` argumentCount
             in (functionSize, functionPosition, size - functionSize, argumentPosition)
        | otherwise = go rest (position - block)
      where
        argumentCount = fromInteger $ countAtSize indexX (size - functionSize)
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
addSparse :: (Num value) => [(Integer, value)] -> [(Integer, value)] -> [(Integer, value)]
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
mulSparse :: (Num value) => [(Integer, value)] -> [(Integer, value)] -> [(Integer, value)]
mulSparse [] _ = []
mulSparse _ [] = []
mulSparse ((leftSize, leftValue) : leftRest) right@((rightSize, rightValue) : rightRest) =
    (leftSize + rightSize, leftValue * rightValue)
        : addSparse
            [(leftSize + size, leftValue * value) | (size, value) <- rightRest]
            (mulSparse leftRest right)

-- | The value of one size in a sparse series, zero when the size is absent.
valueAtSize :: (Num value) => [(Integer, value)] -> Integer -> value
valueAtSize series size = case dropWhile ((< size) . fst) series of
    (found, value) : _ | found == size -> value
    _ -> 0
