{- | Structural shrinking for transparent generators.

A rank is a serialized derivation: through the plan it factors into a
choice branch and mixed-radix product components, and shrinking works on
those decisions instead of the number. Two mechanisms build on the same
factoring:

* 'shrinkPlanRank' produces structural shrink candidates: jump to an
  earlier alternative at its smallest member, or shrink the operation and
  each argument component independently. No candidate decodes to a member
  larger than the current one.

* 'smallerPlanMembers' streams every member structurally smaller than a
  rank's member, in size order, where size ('planMemberSize') is the number
  of source choices in a member. Size classes are counted and indexed
  directly ("Data.CFTA.Ranked.Internal.Size"), not enumerated. The stream
  covers every strictly smaller size. 'Data.CFTA.Gen.QuickCheck.forAllWithLimit'
  puts this stream before the structural candidates, and QuickCheck takes the
  first candidate that fails, so for a deterministic property the loop ends at
  a failing member of the smallest failing size, if the search reaches it. The
  search reads at most @smallerMemberLimit@ members in each step.
  'Data.CFTA.Ranked.QuickCheck.forAll' does not use this stream.

Every candidate either re-encodes a modified decision tree or is selected
from a size class of the plan itself, so shrinking can never leave the
generated language. The walkers read the raw plan, whose structure is the
source of truth for rank order; only the compiled decoder needs the
normalized form.

This module is an exposed internal module. The generator layers of
microcfta-generator use it directly. Its exports are not covered by the PVP
contract of the package.
-}
module Data.CFTA.Ranked.Internal.Shrink (
    withOffsets,
    shrinkPlanRank,
    smallestPlanRank,
    planMemberSize,
    smallerPlanMembers,
) where

import Data.CFTA.Index (
    Cardinality (..),
    ClassRank (..),
    Rank (..),
    RankOffset,
    Size,
    hasRank,
    nextOffset,
    offsetRank,
    pairRank,
    rebaseRank,
    splitRank,
 )
import Data.CFTA.Ranked.Internal.Decoder (Plan (..), RankedValue (..), SizeClass (..))
import Data.CFTA.Ranked.Internal.Size (
    MinimumSize (..),
    SizeIndex (minimumMemberSize, sizeClassCounts, sizeClassSelect),
    countAtSize,
 )

{- | The rank of a structurally smallest member, preferring the earlier stable
rank when several members have the same size.

This walks the plan, not its values. In particular, an earlier choice branch
may contain only larger members than a later branch, so rank zero is not a
general finite minimum.
-}
smallestPlanRank :: Plan a -> Maybe Rank
smallestPlanRank = fmap snd . smallestPlanMember

-- | The size and rank of a structurally smallest member; see 'smallestPlanRank'.
smallestPlanMember :: Plan a -> Maybe (Size, Rank)
smallestPlanMember (PlanSelect cardinality _) =
    if cardinality > 0 then Just (1, 0) else Nothing
smallestPlanMember (PlanSelectOnDemand cardinality _) =
    if cardinality > 0 then Just (1, 0) else Nothing
-- A shared subplan gives its smallest member from its size classes, and does
-- not walk the subplan again. The smallest size class of a finite plan lists
-- its members in rank order, so position zero has the least rank.
smallestPlanMember (PlanShared _ _ index _) = case minimumMemberSize index of
    MinimumSize size -> Just (size, valueRank $ sizeClassSelect index size 0)
    NoFiniteMember -> Nothing
smallestPlanMember (PlanMap _ plan) = smallestPlanMember plan
smallestPlanMember (PlanChoice branches) = go 0 branches
  where
    go _ [] = Nothing
    go offset ((cardinality, branch) : rest) =
        smallerMember
            (fmap (fmap (offsetRank offset)) $ smallestPlanMember branch)
            (go (nextOffset offset cardinality) rest)
smallestPlanMember (PlanAp rightCardinality functions arguments) = do
    (functionSize, functionRank) <- smallestPlanMember functions
    (argumentSize, argumentRank) <- smallestPlanMember arguments
    pure
        ( functionSize + argumentSize
        , pairRank rightCardinality functionRank argumentRank
        )
smallestPlanMember (PlanSized classes) = go 0 classes
  where
    go _ [] = Nothing
    go offset (SizeClass{classSize = size, classCardinality = count} : rest) =
        smallerMember
            (if count > 0 then Just (size, offsetRank offset 0) else Nothing)
            (go (nextOffset offset count) rest)

-- | The smaller of two optional members, preferring the first on a tie.
smallerMember :: Maybe (Size, Rank) -> Maybe (Size, Rank) -> Maybe (Size, Rank)
smallerMember Nothing right = right
smallerMember left Nothing = left
smallerMember left@(Just first) right@(Just second)
    | first <= second = left
    | otherwise = right

{- | Shrink candidates for one rank, guided by the plan structure.

The rank factors into a choice branch and mixed-radix product components,
so shrinking is structural: jump to the smallest member of an earlier
alternative first (in layered generators with base alternatives first, this
replaces a whole subtree with an atom), then shrink each product component
independently, recursing into operation and argument sub-ranks. Every
candidate is a valid rank of the same plan, so shrinking never leaves the
language, and every candidate is a strictly smaller rank whose member is no
larger than the current member, so a shrink loop terminates without growing
its counterexample. An earlier alternative whose smallest member is larger
than the current member is skipped.
-}
shrinkPlanRank :: Plan a -> Rank -> [Rank]
shrinkPlanRank = go
  where
    go :: Plan b -> Rank -> [Rank]
    go (PlanSelect _ _) index = towardZero index
    go (PlanSelectOnDemand _ _) index = towardZero index
    go (PlanShared _ _ _ plan) index = go plan index
    go (PlanMap _ plan) index = go plan index
    go (PlanChoice branches) index =
        case break (holdsRank index) (withOffsets fst branches) of
            (earlier, (offset, (_, branch)) : _) ->
                let currentSize = planMemberSize branch (rebaseRank offset index)
                 in [ offsetRank offset' smallest
                    | (offset', (_, earlierBranch)) <- earlier
                    , Just (size, smallest) <- [smallestPlanMember earlierBranch]
                    , size <= currentSize
                    ]
                        <> [offsetRank offset inner | inner <- go branch (rebaseRank offset index)]
            (_, []) -> []
    -- Size-major ranks: a smaller rank is never a larger member, so the
    -- ordinary integral shrink sequence is already a structural one.
    go (PlanSized _) index = towardZero index
    go (PlanAp radix planF planX) index =
        case splitRank radix index of
            (functionIndex, argumentIndex) ->
                [ pairRank radix functionIndex' argumentIndex
                | functionIndex' <- go planF functionIndex
                ]
                    <> [ pairRank radix functionIndex argumentIndex'
                       | argumentIndex' <- go planX argumentIndex
                       ]

    -- The shrink sequence of 'shrinkIntegral': zero, then successive
    -- halvings of the distance back toward the original.
    towardZero (Rank index) =
        [Rank $ index - step | step <- takeWhile (> 0) (iterate (`div` 2) index)]

-- | Pair each alternative with its cumulative rank offset, given its cardinality.
withOffsets :: (a -> Cardinality) -> [a] -> [(RankOffset, a)]
withOffsets cardinalityOf = go 0
  where
    go _ [] = []
    go offset (alternative : rest) =
        (offset, alternative) : go (nextOffset offset $ cardinalityOf alternative) rest

{- | Whether a rank falls inside an offset branch. The branches before it hold
the smaller ranks, so the rank is at least the offset of the branch.
-}
holdsRank :: Rank -> (RankOffset, (Cardinality, Plan a)) -> Bool
holdsRank rank (offset, (branchCardinality, _)) =
    hasRank branchCardinality $ rebaseRank offset rank

{- | The size of the member a rank decodes to: its number of source choices.

An atom has size one; an application adds the sizes of its operation and
argument choices.
-}
planMemberSize :: Plan a -> Rank -> Size
planMemberSize (PlanSelect _ _) _ = 1
planMemberSize (PlanSelectOnDemand _ _) _ = 1
planMemberSize (PlanShared _ _ _ plan) rank = planMemberSize plan rank
planMemberSize (PlanMap _ plan) rank = planMemberSize plan rank
planMemberSize (PlanChoice branches) rank =
    case dropWhile (not . holdsRank rank) (withOffsets fst branches) of
        (offset, (_, branch)) : _ -> planMemberSize branch (rebaseRank offset rank)
        [] ->
            error
                "microcfta-generator bug in Data.CFTA.Ranked.Internal.Shrink.planMemberSize: \
                \rank outside the plan"
planMemberSize (PlanAp radix planF planX) rank =
    case splitRank radix rank of
        (functionRank, argumentRank) ->
            planMemberSize planF functionRank + planMemberSize planX argumentRank
planMemberSize (PlanSized classes) rank = go 0 classes
  where
    go _ [] =
        error
            "microcfta-generator bug in Data.CFTA.Ranked.Internal.Shrink.planMemberSize: \
            \rank outside the plan"
    go offset (SizeClass{classSize = size, classCardinality = count} : rest)
        | hasRank count $ rebaseRank offset rank = size
        | otherwise = go (nextOffset offset count) rest

{- | Every member structurally smaller than the given rank's member, in size
order, as replayable rank and value.

The index must be the 'sizeIndex' of the plan. Callers keep it beside the
plan so a shrink loop does not rebuild the size classes on every step.
Reaching position @i@ of a size class costs one walk down the plan rather
than enumerating everything before it. The stream is lazy in both
directions: consumers may cap it, and a size class larger than the
consumer's demand is never forced completely.
-}
smallerPlanMembers :: SizeIndex a -> Plan a -> Rank -> [RankedValue a]
smallerPlanMembers index plan rank =
    concatMap (classMembers . fst) $ takeWhile ((< planMemberSize plan rank) . fst) (sizeClassCounts index)
  where
    classMembers size =
        let Cardinality count = countAtSize index size
         in [sizeClassSelect index size classRank | classRank <- map ClassRank [0 .. count - 1]]
