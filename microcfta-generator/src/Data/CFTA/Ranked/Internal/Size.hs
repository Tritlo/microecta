{-# LANGUAGE DerivingStrategies #-}

{- | Size-stratified counting and indexing.

A language's members split into size classes. Sizes follow FEAT (Duregård,
Jansson, and Wang, "Feat: Functional Enumeration of Algebraic Types",
Haskell 2012): the member of @pure@ has size zero, an atom has size one, a
product adds the sizes of its operation and argument, a choice keeps the
sizes of its alternatives, and 'payIndex' adds one. A t'SizeIndex' counts
every class by convolution (a product of size @s@ splits into an operation
of size @a@ and arguments of size @s - a@) and indexes into one directly,
returning the member's rank alongside its value.

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
reason. A count can be zero: a product and a pay give their smallest size
before they count it, and that entry can be zero.

Convolution is productive on infinite operands, which is what makes
'fixIndex' work. A recursive occurrence must be guarded: it contributes to
size @s@ only through a pay, or through a product whose other side has no
member of size zero. Then counting size @s@ only consults the occurrence at
sizes below @s@.

This module is an exposed internal module. The generator layers of
microcfta-generator use it directly. Its exports are not covered by the PVP
contract of the package.
-}
module Data.CFTA.Ranked.Internal.Size (
    SizeCounts,
    SizeIndex (sizeClassCounts, sizeClassSelect, minimumMemberSize, largestMemberSize),
    MinimumSize (..),
    LargestSize (..),
    SizedRank (..),
    Occurrence (..),
    closedOccurrence,
    probeIndexWithMinimum,
    minimumOf,
    closedProbe,
    closedProbeWithOccurrencesOf,
    sameOccurrences,
    isUnguarded,
    usesOccurrence,
    reachesOccurrence,
    sizeIndex,
    countAtSize,
    sizeClassOf,
    sizeMajorRank,
    planPosition,
    productPosition,
    ChoiceIndex (..),
    choicePosition,
    constantIndex,
    mapIndex,
    mapIndexWithRank,
    productIndex,
    choiceIndex,
    payIndex,
    constructorIndex,
    fixIndex,
    withKnotMetadata,
    sizeClasses,
    addSparse,
    mulSparse,
    valueAtSize,
) where

import Data.Foldable (toList)
import Data.Hashable (Hashable)
import qualified Data.IntSet as IntSet
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Sequence

import Data.CFTA.Index (
    Cardinality (..),
    ClassRank (..),
    Rank (..),
    RankOffset,
    Size (..),
    classMemberRank,
    hasRank,
    nextOffset,
    offsetRank,
    pairRank,
    rebaseRank,
    splitRank,
 )
import Data.CFTA.Ranked.Internal.Decoder (
    LargestSize (..),
    MinimumSize (..),
    Plan (..),
    RankedValue (..),
    SizeClass (..),
    SizeCounts,
    SizeIndex (..),
    planCardinality,
 )

{- | A token that identifies the occurrence of one recursion in the probe
flags of a size index. The flags hold the 'Int' of each token in an 'IntSet'.
-}
newtype Occurrence = Occurrence Int

{- | The token of 'closedProbe', which stands for a recursion that is already
tied. A closed probe clears its flags, so no flag holds this token. The
supply of tokens for the recursions starts at the token after it.
-}
closedOccurrence :: Occurrence
closedOccurrence = Occurrence 0

{- | A stand-in for the occurrence of one recursion, with an assumed minimum,
used to check that the recursive definition is guarded before it is tied.

The token identifies the recursion. A nested definition can reach the probe
of an enclosing one, so each recursion reads only its own token.

Only its metadata is ever read: building a language around a probe answers
whether the recursion passes through a product and whether it can close to a
finite member, without counting anything.
-}
probeIndexWithMinimum :: Occurrence -> MinimumSize -> SizeIndex a
probeIndexWithMinimum (Occurrence token) minimumSize' =
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
        SizesDoNotEnd
        (IntSet.singleton token)
        (IntSet.singleton token)
        (IntSet.singleton token)

{- | Whether a language built around the probe of a token left that
occurrence unguarded: counting it would not terminate, or it adds no term
node, so that one term could have infinitely many ranks.
-}
isUnguarded :: Occurrence -> SizeIndex a -> Bool
isUnguarded (Occurrence token) index =
    IntSet.member token (unguardedOccurrences index) || IntSet.member token (termlessOccurrences index)

{- | Whether a language built around the probe of a token reaches that
occurrence at all. A body that does not is a language in its own right, not
a recursive one.
-}
usesOccurrence :: Occurrence -> SizeIndex a -> Bool
usesOccurrence (Occurrence token) = IntSet.member token . usedOccurrences

{- | Whether a language reaches the probe of any recursion. Such a language
depends on a definition that is not tied yet.
-}
reachesOccurrence :: SizeIndex a -> Bool
reachesOccurrence = not . IntSet.null . usedOccurrences

-- | The number of members of one size, zero outside the counted sizes.
countAtSize :: SizeIndex a -> Size -> Cardinality
countAtSize index = valueAtSize (sizeClassCounts index)

{- | A size, and a rank in the size class of that size.

A member of a size-stratified language has one sized rank. The derived order
compares the sizes first, then the class ranks: this is the size-major order
of the members. The fields are lazy, so a caller can make the sized ranks of
many members and read only some of them.
-}
data SizedRank = SizedRank
    { rankSize :: Size
    -- ^ The size of the member.
    , classRank :: ClassRank
    -- ^ The rank of the member in its size class.
    }
    deriving (Eq, Ord, Show)

{- | The size class holding one rank, with the rank rebased into it.

Only meaningful for a size-major index. 'Nothing' means the rank is outside
the language, which can only be discovered for a language with finitely
many size classes.
-}
sizeClassOf :: SizeIndex a -> Rank -> Maybe SizedRank
sizeClassOf index (Rank rank)
    | rank < 0 = Nothing
    | otherwise = go rank $ sizeClassCounts index
  where
    go _ [] = Nothing
    go position ((size, Cardinality count) : rest)
        | position < count = Just (SizedRank size (ClassRank position))
        | otherwise = go (position - count) rest

-- | The size-major rank of one sized rank: the members of the smaller sizes come first.
sizeMajorRank :: SizeIndex a -> SizedRank -> Rank
sizeMajorRank index (SizedRank size position) = classMemberRank (countBelow (sizeClassCounts index) size) position

-- | The first rank of one size class: the members of the smaller sizes come before it.
countBelow :: SizeCounts -> Size -> RankOffset
countBelow counts size = foldl' nextOffset 0 [count | (_, count) <- takeWhile ((< size) . fst) counts]

{- | The size class and the position in it of one rank of a finite plan.

This is the inverse of 'sizeClassSelect' on 'sizeIndex': the rank that
'sizeClassSelect' returns for the size and position is the given rank.
'Nothing' means that the rank is outside the plan.
-}
planPosition :: Plan a -> Rank -> Maybe SizedRank
planPosition plan rank
    | not $ hasRank (planCardinality plan) rank = Nothing
    | otherwise = case plan of
        -- A leaf has one size class, so a rank is its rank in that class.
        PlanSelect _ _ -> Just (SizedRank 1 leafRank)
        PlanSelectOnDemand _ _ -> Just (SizedRank 1 leafRank)
        PlanPure _ -> Just (SizedRank 0 leafRank)
        PlanPay inner -> (\(SizedRank size position) -> SizedRank (size + 1) position) <$> planPosition inner rank
        PlanShared _ _ _ inner -> planPosition inner rank
        PlanMap _ inner -> planPosition inner rank
        PlanChoice branches -> branchPosition Empty 0 branches
        PlanAp radix planF planX -> do
            let (rankF, rankX) = splitRank radix rank
            positionF <- planPosition planF rankF
            positionX <- planPosition planX rankX
            pure $ productPosition (sizeIndex planF) (sizeIndex planX) positionF positionX
        PlanSized classes -> classPosition 0 classes
  where
    leafRank = let Rank wide = rank in ClassRank wide
    branchPosition _ _ [] = Nothing
    branchPosition earlier offset ((count, branch) : rest)
        | hasRank count remaining = do
            SizedRank size position <- planPosition branch remaining
            pure $
                SizedRank size (choicePosition (map sizeIndex $ toList earlier) (ChoiceIndex $ Sequence.length earlier) size position)
        | otherwise = branchPosition (earlier :|> branch) (nextOffset offset count) rest
      where
        remaining = rebaseRank offset rank
    classPosition _ [] = Nothing
    classPosition offset (SizeClass{classSize = size, classCardinality = count} : rest)
        | hasRank count remaining = Just (SizedRank size (ClassRank position))
        | otherwise = classPosition (nextOffset offset count) rest
      where
        remaining@(Rank position) = rebaseRank offset rank

{- | The size and the position in its size class of a product member, from
the size and position of its function and of its argument.

Within a size class, splits come in ascending function size, and each split
is ordered function-major, as 'productSplit' reads them.
-}
productPosition :: SizeIndex f -> SizeIndex x -> SizedRank -> SizedRank -> SizedRank
productPosition indexF indexX (SizedRank sizeF (ClassRank positionF)) (SizedRank sizeX (ClassRank positionX)) =
    SizedRank size
        $ ClassRank
        $ sum
            [ functionCount * argumentCount (size - functionSize)
            | (functionSize, Cardinality functionCount) <- takeWhile ((< sizeF) . fst) (sizeClassCounts indexF)
            ]
            + positionF * argumentCount sizeX
            + positionX
  where
    size = sizeF + sizeX
    argumentCount argumentSize = case countAtSize indexX argumentSize of
        Cardinality count -> count

{- | The zero-based index of an alternative in a choice.

A choice of size indexes ('choiceIndex') and a generator choice
('Data.CFTA.Gen.Label.Choice') number their alternatives in order, from zero.
-}
newtype ChoiceIndex = ChoiceIndex Int
    deriving newtype (Eq, Ord, Show, Hashable, Num, Enum)

{- | The position in one size class of a member of one alternative, from its
position in that alternative's class. The alternatives before it come first,
as 'partAt' reads them.
-}
choicePosition :: [SizeIndex a] -> ChoiceIndex -> Size -> ClassRank -> ClassRank
choicePosition branches (ChoiceIndex branch) size (ClassRank position) =
    case sum [countAtSize earlier size | earlier <- take branch branches] of
        Cardinality before -> ClassRank $ before + position

{- | The non-empty size classes up to a bound.

This is the bridge back to a finite language: a recursive index bounded this
way becomes an ordinary 'PlanSized' plan whose ranks are size-major.
-}
sizeClasses :: Size -> SizeIndex a -> [SizeClass a]
sizeClasses bound index =
    [ SizeClass size count (rankedValue . sizeClassSelect index size) (sizeClassValueInt index size)
    | (size, count) <- takeWhile ((<= bound) . fst) (sizeClassCounts index)
    , count > 0
    ]

-- | Count and index the size classes of a finite plan, keeping its ranks.
sizeIndex :: Plan a -> SizeIndex a
sizeIndex (PlanSelect cardinality' decode) =
    SizeIndex
        [(1, cardinality') | cardinality' > 0]
        select
        selectInt
        minimumSize'
        (LargestSize 1)
        IntSet.empty
        IntSet.empty
        IntSet.empty
  where
    minimumSize'
        | cardinality' > 0 = MinimumSize 1
        | otherwise = NoFiniteMember
    -- A leaf has one size class, so a rank in that class is a rank.
    select 1 (ClassRank position) = let rank = Rank position in RankedValue rank (decode rank)
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
sizeIndex (PlanPure value) = constantIndex value
sizeIndex (PlanPay plan) = payIndex $ sizeIndex plan
sizeIndex (PlanShared _ _ index _) = index
sizeIndex (PlanMap transform plan) = mapIndex transform $ sizeIndex plan
sizeIndex (PlanChoice branches) =
    SizeIndex counts select selectInt minimumSize' largestSize IntSet.empty IntSet.empty IntSet.empty
  where
    entries = offsetBranches 0 branches
    offsetBranches _ [] = []
    offsetBranches offset ((branchCardinality, branch) : rest) =
        (offset, sizeIndex branch) : offsetBranches (nextOffset offset branchCardinality) rest
    counts = foldr (addCounts . sizeClassCounts . snd) [] entries
    minimumSize' = minimumOf $ map (minimumMemberSize . snd) entries
    largestSize = largestOf $ map (largestMemberSize . snd) entries

    select size position =
        let (offset, inner, rebased) = partAt size entries position
            RankedValue rank value = sizeClassSelect inner size rebased
         in RankedValue (offsetRank offset rank) value
    selectInt size position =
        let (inner, rebased) = partAtInt size (map snd entries) position
         in sizeClassValueInt inner size rebased
sizeIndex (PlanAp radix planF planX) =
    SizeIndex counts select selectInt minimumSize' largestSize IntSet.empty IntSet.empty IntSet.empty
  where
    indexF = sizeIndex planF
    indexX = sizeIndex planX
    counts = productCounts indexF indexX
    minimumSize' = productMinimum (minimumMemberSize indexF) (minimumMemberSize indexX)
    largestSize = productLargest (largestMemberSize indexF) (largestMemberSize indexX)

    select size position =
        let (functionSize, functionPosition, argumentSize, argumentPosition) =
                productSplit indexF indexX size position
            RankedValue functionRank function = sizeClassSelect indexF functionSize functionPosition
            RankedValue argumentRank argument = sizeClassSelect indexX argumentSize argumentPosition
         in RankedValue (pairRank radix functionRank argumentRank) (function argument)
    selectInt size position =
        let (functionSize, functionPosition, argumentSize, argumentPosition) =
                productSplitInt indexF indexX size position
            function = sizeClassValueInt indexF functionSize functionPosition
            argument = sizeClassValueInt indexX argumentSize argumentPosition
         in function argument
sizeIndex (PlanSized classes) =
    SizeIndex counts select selectInt minimumSize' largestSize IntSet.empty IntSet.empty IntSet.empty
  where
    counts = [(size, count) | SizeClass{classSize = size, classCardinality = count} <- classes, count > 0]
    largestSize = LargestSize $ maximum $ 0 : [size | SizeClass{classSize = size, classCardinality = count} <- classes, count > 0]
    minimumSize' = case [size | SizeClass{classSize = size, classCardinality = count} <- classes, count > 0] of
        [] -> NoFiniteMember
        liveSizes -> MinimumSize $ minimum liveSizes
    offsets = offsetClasses 0 classes
    offsetClasses _ [] = []
    offsetClasses offset (sizeClass@SizeClass{classCardinality = count} : rest) =
        (offset, sizeClass) : offsetClasses (nextOffset offset count) rest

    select size position = case [entry | entry@(_, SizeClass{classSize = size'}) <- offsets, size' == size] of
        (offset, SizeClass{classMember = decode}) : _ -> RankedValue (classMemberRank offset position) (decode position)
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

-- | The one-member index of a single value, of size zero.
constantIndex :: a -> SizeIndex a
constantIndex value =
    SizeIndex [(0, 1)] select selectInt (MinimumSize 0) (LargestSize 0) IntSet.empty IntSet.empty IntSet.empty
  where
    select 0 0 = RankedValue 0 value
    select size position =
        error $
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Size.constantIndex: \
            \no member at size "
                <> show size
                <> " position "
                <> show position
    selectInt 0 0 = value
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
        (termlessOccurrences index)
        (usedOccurrences index)
  where
    select size position =
        let RankedValue rank value = sizeClassSelect index size position
         in RankedValue rank (transform value)
    selectInt size = transform . sizeClassValueInt index size

{- | Map the values of an index with their ranks, keeping its counts and
ranks.
-}
mapIndexWithRank :: (Rank -> a -> b) -> SizeIndex a -> SizeIndex b
mapIndexWithRank transform index =
    SizeIndex
        (sizeClassCounts index)
        select
        (\size -> rankedValue . select size . ClassRank . toInteger)
        (minimumMemberSize index)
        (largestMemberSize index)
        (unguardedOccurrences index)
        (termlessOccurrences index)
        (usedOccurrences index)
  where
    select size position =
        let RankedValue rank value = sizeClassSelect index size position
         in RankedValue rank (transform rank value)

{- | The product of two indexes, ranked size-major.

Within a size class, splits come in ascending operation size, and each split
is ordered operation-major. Either side may be recursive.
-}
productIndex :: SizeIndex (a -> b) -> SizeIndex a -> SizeIndex b
-- A side with no member of size zero makes every member of the product larger
-- than the member of the other side, so counting a size consults only smaller
-- sizes of the other side: such a side guards an occurrence on the other side.
productIndex indexF indexX =
    SizeIndex
        counts
        select
        selectInt
        smallest
        (productLargest (largestMemberSize indexF) (largestMemberSize indexX))
        (IntSet.union (unguardedBeside indexX indexF) (unguardedBeside indexF indexX))
        IntSet.empty
        (IntSet.union (usedOccurrences indexF) (usedOccurrences indexX))
  where
    smallest = productMinimum (minimumMemberSize indexF) (minimumMemberSize indexX)
    -- The counts start with the smallest size of the product, which comes
    -- from the minimums of the sides, before the convolution is read. So a
    -- recursive definition that uses this product gives its own smallest
    -- members before the product is counted.
    counts = case smallest of
        NoFiniteMember -> []
        MinimumSize size -> (size, valueAtSize convolution size) : dropWhile ((<= size) . fst) convolution
    convolution = productCounts indexF indexX
    ranks = sizeMajorRanks counts

    select size position =
        let (functionSize, functionPosition, argumentSize, argumentPosition) =
                productSplit indexF indexX size position
            RankedValue _ function = sizeClassSelect indexF functionSize functionPosition
            RankedValue _ argument = sizeClassSelect indexX argumentSize argumentPosition
         in RankedValue (rankAt ranks size position) (function argument)
    selectInt size position =
        let (functionSize, functionPosition, argumentSize, argumentPosition) =
                productSplitInt indexF indexX size position
            function = sizeClassValueInt indexF functionSize functionPosition
            argument = sizeClassValueInt indexX argumentSize argumentPosition
         in function argument

{- | The occurrences that a side leaves unguarded in a product, beside the
other side. The other side guards them unless it has a member of size zero.
-}
unguardedBeside :: SizeIndex b -> SizeIndex a -> IntSet.IntSet
unguardedBeside other side = case minimumMemberSize other of
    MinimumSize 0 -> unguardedOccurrences side
    _ -> IntSet.empty

{- | The members of an index, each one larger: the @pay@ of FEAT. Ranks and
values do not change.

A pay guards every occurrence below it. Its counts start with its smallest
size, one more than the minimum of the inner index, before the inner counts
are read. So a recursive definition under a pay gives its smallest members
before the inner language is counted. FEAT starts @pay@ with an empty part of
size zero instead, but here a zero count of size zero would multiply the
count of the full size in a product, and reading that count inside its own
definition does not terminate.
-}
payIndex :: SizeIndex a -> SizeIndex a
payIndex index =
    SizeIndex
        ( case minimumMemberSize index of
            NoFiniteMember -> []
            MinimumSize smallest ->
                (smallest + 1, valueAtSize (sizeClassCounts index) smallest)
                    : [(size + 1, count) | (size, count) <- sizeClassCounts index, size > smallest]
        )
        (\size -> sizeClassSelect index (size - 1))
        (\size -> sizeClassValueInt index (size - 1))
        ( case minimumMemberSize index of
            MinimumSize size -> MinimumSize $ size + 1
            NoFiniteMember -> NoFiniteMember
        )
        ( case largestMemberSize index of
            LargestSize size -> LargestSize $ size + 1
            SizesDoNotEnd -> SizesDoNotEnd
        )
        IntSet.empty
        (termlessOccurrences index)
        (usedOccurrences index)

{- | The members of an index under a constructor: each one larger, as
'payIndex' gives them. A constructor adds a term node, so no occurrence below
it is termless. The result is a new record, not an update of the index, as in
'withKnotMetadata'.
-}
constructorIndex :: SizeIndex a -> SizeIndex a
constructorIndex index =
    SizeIndex
        { sizeClassCounts = sizeClassCounts paid
        , sizeClassSelect = sizeClassSelect paid
        , sizeClassValueInt = sizeClassValueInt paid
        , minimumMemberSize = minimumMemberSize paid
        , largestMemberSize = largestMemberSize paid
        , unguardedOccurrences = unguardedOccurrences paid
        , termlessOccurrences = IntSet.empty
        , usedOccurrences = usedOccurrences paid
        }
  where
    paid = payIndex index

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
        (largestOf $ map largestMemberSize branches)
        (IntSet.unions $ map unguardedOccurrences branches)
        (IntSet.unions $ map termlessOccurrences branches)
        (IntSet.unions $ map usedOccurrences branches)
  where
    counts = foldr (addCounts . sizeClassCounts) [] branches
    ranks = sizeMajorRanks counts
    entries = [((), branch) | branch <- branches]

    select size position =
        let (_, inner, rebased) = partAt size entries position
            RankedValue _ value = sizeClassSelect inner size rebased
         in RankedValue (rankAt ranks size position) value
    selectInt size position =
        let (inner, rebased) = partAtInt size branches position
         in sizeClassValueInt inner size rebased

{- | Tie a recursive index: the body is built from the index being defined.

The recursion must be guarded (every recursive occurrence under a
'payIndex', or beside a side of a 'productIndex' that has no member of size
zero), so that counting a size only consults smaller sizes.
Callers check that with a probe first, because an unguarded knot diverges
rather than failing. The minimum and the flags come from one build around
'closedProbe', which does not read the knot.

The closed occurrence has the given smallest member size: the minimum that
the probe of the recursion converged to. A nested definition whose finite
members all go through the occurrence is then not empty in the closed build,
so the flags of the index keep the occurrences that the nested definition
reaches.
-}
fixIndex :: MinimumSize -> (SizeIndex a -> SizeIndex a) -> SizeIndex a
fixIndex minimumSize' build = index
  where
    closed = build $ closedProbe minimumSize'
    index = withKnotMetadata (minimumMemberSize closed) closed (build index)

{- | An occurrence of a definition that is already tied, with the smallest
size of its members. No probe is reached through it: the definition answered
its own probe when it was tied.
-}
closedProbe :: MinimumSize -> SizeIndex a
closedProbe minimumSize' =
    (probeIndexWithMinimum closedOccurrence minimumSize')
        { unguardedOccurrences = IntSet.empty
        , termlessOccurrences = IntSet.empty
        , usedOccurrences = IntSet.empty
        }

{- | 'closedProbe' with the occurrence flags of another index. A member of a
recursive family stands for the body of its key, which can reach the probe of
an enclosing recursion, and the flags carry that to the members that read it.
-}
closedProbeWithOccurrencesOf :: SizeIndex b -> MinimumSize -> SizeIndex a
closedProbeWithOccurrencesOf flags minimumSize' =
    (closedProbe minimumSize')
        { unguardedOccurrences = unguardedOccurrences flags
        , termlessOccurrences = termlessOccurrences flags
        , usedOccurrences = usedOccurrences flags
        }

-- | Whether two indexes reach the same probes, and leave the same ones unguarded.
sameOccurrences :: SizeIndex a -> SizeIndex b -> Bool
sameOccurrences left right =
    unguardedOccurrences left == unguardedOccurrences right
        && termlessOccurrences left == termlessOccurrences right
        && usedOccurrences left == usedOccurrences right

{- | Give a tied index a minimum and the occurrence flags of a build that does
not read the knot, leaving counts and decoding unchanged.

The flags of the tied index itself read the index again, so a definition
that reads them before its own occurrence does not terminate. A build around
'closedProbe' gives the same answer for every enclosing probe. The result is
a new record, not an update of the index: an update would evaluate the index,
and a nested definition in its body can read the flags of this one.
-}
withKnotMetadata :: MinimumSize -> SizeIndex b -> SizeIndex a -> SizeIndex a
withKnotMetadata minimumSize' closed index =
    SizeIndex
        { sizeClassCounts = sizeClassCounts index
        , sizeClassSelect = sizeClassSelect index
        , sizeClassValueInt = sizeClassValueInt index
        , minimumMemberSize = minimumSize'
        , largestMemberSize = SizesDoNotEnd
        , unguardedOccurrences = unguardedOccurrences closed
        , termlessOccurrences = termlessOccurrences closed
        , usedOccurrences = usedOccurrences closed
        }

-- | The least of the minimum sizes, ignoring 'NoFiniteMember'.
minimumOf :: [MinimumSize] -> MinimumSize
minimumOf = foldr combine NoFiniteMember
  where
    combine NoFiniteMember current = current
    combine current NoFiniteMember = current
    combine (MinimumSize left) (MinimumSize right) = MinimumSize $ min left right

{- | The largest of the largest sizes of the alternatives of a choice, and at
least zero. If the sizes of one alternative do not end, the sizes of the
choice do not end.
-}
largestOf :: [LargestSize] -> LargestSize
largestOf = foldr combine (LargestSize 0)
  where
    combine SizesDoNotEnd _ = SizesDoNotEnd
    combine _ SizesDoNotEnd = SizesDoNotEnd
    combine (LargestSize left) (LargestSize right) = LargestSize $ max left right

{- | The minimum size of a product: the sum of the minimum sizes of its two
sides. A product has a finite member only when both sides have one.
-}
productMinimum :: MinimumSize -> MinimumSize -> MinimumSize
productMinimum (MinimumSize left) (MinimumSize right) = MinimumSize $ left + right
productMinimum _ _ = NoFiniteMember

{- | The largest size of a product: the sum of the largest sizes of its two
sides. If the sizes of one side do not end, the sizes of the product do not
end.
-}
productLargest :: LargestSize -> LargestSize -> LargestSize
productLargest (LargestSize left) (LargestSize right) = LargestSize $ left + right
productLargest _ _ = SizesDoNotEnd

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
productSplit indexF indexX size (ClassRank start) = go (takeWhile ((<= size) . fst) (sizeClassCounts indexF)) start
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
productSplitInt indexF indexX size = go $ takeWhile ((<= size) . fst) (sizeClassCounts indexF)
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
