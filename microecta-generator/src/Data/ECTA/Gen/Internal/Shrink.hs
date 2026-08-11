{- | Structural shrinking for transparent generators.

A rank is a serialized derivation: through the plan it factors into a
choice branch and mixed-radix product components, and shrinking works on
those decisions instead of the number. Two mechanisms build on the same
factoring:

* 'shrinkPlanRank' produces structural shrink candidates: jump to an
  earlier alternative at its minimal rank, or shrink the operation and each
  argument component independently.

* 'smallerPlanMembers' streams every member structurally smaller than a
  rank's member, in size order, where size ('planMemberSize') is the number
  of source choices in a member. Size classes are counted and indexed
  directly ("Data.ECTA.Gen.Internal.Size"), not enumerated. Searching this
  stream first makes a greedy shrink loop terminate at the globally
  smallest failing member.

Every candidate either re-encodes a modified decision tree or is selected
from a size class of the plan itself, so shrinking can never leave the
generated language. The walkers read the raw plan, whose structure is the
source of truth for rank order; only the compiled decoder needs the
normalized form.
-}
module Data.ECTA.Gen.Internal.Shrink (
    shrinkPlanRank,
    planMemberSize,
    smallerPlanMembers,
) where

import Data.ECTA.Gen.Internal.Decoder (Plan (..))
import Data.ECTA.Gen.Internal.Size (
    SizeIndex (sizeClassSelect),
    countAtSize,
    sizeIndex,
 )

{- | Shrink candidates for one rank, guided by the plan structure.

The rank factors into a choice branch and mixed-radix product components,
so shrinking is structural: jump to the minimal rank of an earlier
alternative first (in layered generators with base alternatives first, this
replaces a whole subtree with an atom), then shrink each product component
independently, recursing into operation and argument sub-ranks. Every
candidate is a valid rank of the same plan, so shrinking never leaves the
language.
-}
shrinkPlanRank :: Plan a -> Integer -> [Integer]
shrinkPlanRank = go
  where
    go :: Plan b -> Integer -> [Integer]
    go (PlanSelect _ _) index = towardZero index
    go (PlanMap _ plan) index = go plan index
    go (PlanChoice branches) index =
        case break (holdsRank index) (withOffsets branches) of
            (earlier, (offset, _, branch) : _) ->
                [offset' | (offset', _, _) <- earlier]
                    <> [offset + inner | inner <- go branch (index - offset)]
            (_, []) -> []
    go (PlanAp radix planF planX) index =
        case index `quotRem` radix of
            (functionIndex, argumentIndex) ->
                [ functionIndex' * radix + argumentIndex
                | functionIndex' <- go planF functionIndex
                ]
                    <> [ functionIndex * radix + argumentIndex'
                       | argumentIndex' <- go planX argumentIndex
                       ]

    -- The shrink sequence of 'shrinkIntegral': zero, then successive
    -- halvings of the distance back toward the original.
    towardZero index =
        [index - step | step <- takeWhile (> 0) (iterate (`div` 2) index)]

-- | Pair each branch with its cumulative rank offset.
withOffsets :: [(Integer, Plan a)] -> [(Integer, Integer, Plan a)]
withOffsets = go 0
  where
    go _ [] = []
    go offset ((branchCardinality, branch) : rest) =
        (offset, branchCardinality, branch) : go (offset + branchCardinality) rest

-- | Whether a rank falls inside an offset branch.
holdsRank :: Integer -> (Integer, Integer, Plan a) -> Bool
holdsRank rank (offset, branchCardinality, _) =
    rank < offset + branchCardinality

{- | The size of the member a rank decodes to: its number of source choices.

An atom has size one; an application adds the sizes of its operation and
argument choices.
-}
planMemberSize :: Plan a -> Integer -> Int
planMemberSize (PlanSelect _ _) _ = 1
planMemberSize (PlanMap _ plan) rank = planMemberSize plan rank
planMemberSize (PlanChoice branches) rank =
    case dropWhile (not . holdsRank rank) (withOffsets branches) of
        (offset, _, branch) : _ -> planMemberSize branch (rank - offset)
        [] -> error "planMemberSize: rank outside plan"
planMemberSize (PlanAp radix planF planX) rank =
    case rank `quotRem` radix of
        (functionRank, argumentRank) ->
            planMemberSize planF functionRank + planMemberSize planX argumentRank

{- | Every member structurally smaller than the given rank's member, in size
order, as replayable rank and value.

Members come from 'sizeIndex', so reaching position @i@ of a size class
costs one walk down the plan rather than enumerating everything before it.
The stream is lazy in both directions: consumers may cap it, and a size
class larger than the consumer's demand is never forced completely.
-}
smallerPlanMembers :: Plan a -> Integer -> [(Integer, a)]
smallerPlanMembers plan rank =
    concatMap classMembers [1 .. planMemberSize plan rank - 1]
  where
    index = sizeIndex plan
    classMembers size =
        [ sizeClassSelect index size position
        | position <- [0 .. countAtSize index size - 1]
        ]
