{- | Weighted subsets of a finite source-rank domain.

Ranks identify source occurrences, so repeated values remain distinct. Union
operands must be disjoint. Products use the entire right source domain as their
radix, including rejected ranks. Queries do not enumerate source members.
-}
module Data.LTA.Gen.Internal.SourceIndex (
    SourceIndex,
    empty,
    full,
    singleton,
    fromPrefix,
    union,
    product,
    shift,
    scale,
    withDomain,
    cardinality,
    mass,
    select,
    selectByMass,
    rank,
) where

import Prelude hiding (product)

-- | A source subset with cached domain, count, mass, and occupied bounds.
data SourceIndex = SourceIndex
    { domain :: !Integer
    -- ^ Exclusive upper bound of the raw source ranks.
    , cardinality :: !Integer
    -- ^ Number of retained source ranks.
    , mass :: !Integer
    -- ^ Sum of the positive weights of retained ranks.
    , lower :: !Integer
    , upper :: !Integer
    , plan :: !Plan
    }

-- | Compact operations over source subsets. An interval has one fixed weight.
data Plan
    = Empty
    | Interval !Integer
    | Union SourceIndex SourceIndex
    | Product SourceIndex SourceIndex
    | Shift !Integer SourceIndex
    | Scale !Integer SourceIndex
    | Counted (Integer -> Integer)

-- | Retain no ranks in a nonnegative source domain.
empty :: Integer -> SourceIndex
empty bound
    | bound < 0 = error "SourceIndex.empty: negative domain"
    | otherwise = SourceIndex bound 0 0 0 0 Empty

-- | Retain every rank with weight one in a nonnegative source domain.
full :: Integer -> SourceIndex
full bound
    | bound < 0 = error "SourceIndex.full: negative domain"
    | otherwise = interval bound 0 bound 1

-- | Retain one in-range source rank with a positive weight.
singleton :: Integer -> Integer -> Integer -> SourceIndex
singleton bound source sourceWeight
    | bound < 0 = error "SourceIndex.singleton: negative domain"
    | source < 0 || source >= bound = error "SourceIndex.singleton: rank outside domain"
    | sourceWeight <= 0 = error "SourceIndex.singleton: nonpositive weight"
    | otherwise = interval bound source (source + 1) sourceWeight

{- | Retain a uniformly weighted subset through its exact prefix counts.

The callback counts retained source ranks strictly below its argument. It must
start at zero, end at the supplied count, and increase by zero or one at each
source rank. These integration invariants are not checked by enumeration.
-}
fromPrefix :: Integer -> Integer -> (Integer -> Integer) -> SourceIndex
fromPrefix bound count prefixAt
    | count <= 0 = empty bound
    | count == bound = full bound
    | bound < 0 || count > bound = error "SourceIndex.fromPrefix: invalid cardinality"
    | otherwise = index{lower = search index prefixAt 0, upper = search index prefixAt (count - 1) + 1}
  where
    index = SourceIndex bound count count 0 bound (Counted prefixAt)

{- | Combine disjoint subsets and retain the larger raw domain.

The caller must ensure that the operands contain no shared source rank.
This operation does not check disjointness by enumerating their members.
-}
union :: SourceIndex -> SourceIndex -> SourceIndex
union left right
    | cardinality left == 0 = withDomain bound right
    | cardinality right == 0 = withDomain bound left
    | Interval leftWeight <- plan left
    , Interval rightWeight <- plan right
    , leftWeight == rightWeight
    , upper left == lower right || upper right == lower left =
        interval bound first last_ leftWeight
    | otherwise =
        SourceIndex
            bound
            (cardinality left + cardinality right)
            (mass left + mass right)
            first
            last_
            (Union left right)
  where
    bound = max (domain left) (domain right)
    first = min (lower left) (lower right)
    last_ = max (upper left) (upper right)

{- | Form a mixed-radix product and multiply each pair's weights.

The source rank of a pair is @leftRank * domain right + rightRank@.
-}
product :: SourceIndex -> SourceIndex -> SourceIndex
product left right
    | cardinality left == 0 || cardinality right == 0 = empty bound
    | cardinality left == 1 =
        withDomain bound $ shift (lower left * radix) $ scale (mass left) right
    | domain right == 1 = scale (mass right) left
    | Interval leftWeight <- plan left
    , Interval rightWeight <- plan right
    , lower right == 0
    , upper right == radix =
        interval bound (lower left * radix) (upper left * radix) (leftWeight * rightWeight)
    | otherwise =
        SourceIndex
            bound
            (cardinality left * cardinality right)
            (mass left * mass right)
            (lower left * radix + lower right)
            ((upper left - 1) * radix + upper right)
            (Product left right)
  where
    radix = domain right
    bound = domain left * radix

-- | Add a nonnegative offset to every rank and to the source domain bound.
shift :: Integer -> SourceIndex -> SourceIndex
shift offset index
    | offset < 0 = error "SourceIndex.shift: negative offset"
    | offset == 0 = index
    | cardinality index == 0 = empty bound
    | Interval sourceWeight <- plan index =
        interval bound (offset + lower index) (offset + upper index) sourceWeight
    | Shift previous nested <- plan index =
        withDomain bound $ shift (offset + previous) nested
    | otherwise =
        index
            { domain = bound
            , lower = offset + lower index
            , upper = offset + upper index
            , plan = Shift offset index
            }
  where
    bound = offset + domain index

-- | Multiply retained weights by a positive factor without changing ranks.
scale :: Integer -> SourceIndex -> SourceIndex
scale factor index
    | factor <= 0 = error "SourceIndex.scale: nonpositive factor"
    | factor == 1 || cardinality index == 0 = index
    | Interval sourceWeight <- plan index =
        interval (domain index) (lower index) (upper index) (factor * sourceWeight)
    | Scale previous nested <- plan index =
        withDomain (domain index) $ scale (factor * previous) nested
    | otherwise = index{mass = factor * mass index, plan = Scale factor index}

-- | Extend the raw domain without adding members or changing their weights.
withDomain :: Integer -> SourceIndex -> SourceIndex
withDomain bound index
    | bound < domain index = error "SourceIndex.withDomain: cannot reduce domain"
    | otherwise = index{domain = bound}

-- | Count retained ranks strictly below a raw source rank. Queries saturate.
prefixCount :: SourceIndex -> Integer -> Integer
prefixCount index source = fst $ prefix index source

-- | Sum weights strictly below a raw source rank. Queries saturate.
prefixMass :: SourceIndex -> Integer -> Integer
prefixMass index source = snd $ prefix index source

-- | Test membership. Negative and out-of-range source ranks are absent.
member :: SourceIndex -> Integer -> Bool
member index source
    | source < lower index || source >= upper index = False
    | otherwise = case plan index of
        Empty -> False
        Interval _ -> True
        Union left right -> member left source || member right source
        Product left right ->
            let (leftRank, rightRank) = source `quotRem` domain right
             in member left leftRank && member right rightRank
        Shift offset nested -> member nested $ source - offset
        Scale _ nested -> member nested source
        Counted prefixAt -> prefixAt (source + 1) > prefixAt source

-- | Return a retained rank's weight, or zero when the rank is absent.
weight :: SourceIndex -> Integer -> Integer
weight index source
    | source < lower index || source >= upper index = 0
    | otherwise = case plan index of
        Empty -> 0
        Interval sourceWeight -> sourceWeight
        Union left right ->
            let leftWeight = weight left source
             in if leftWeight > 0 then leftWeight else weight right source
        Product left right ->
            let (leftRank, rightRank) = source `quotRem` domain right
                leftWeight = weight left leftRank
             in if leftWeight == 0 then 0 else leftWeight * weight right rightRank
        Shift offset nested -> weight nested $ source - offset
        Scale factor nested -> factor * weight nested source
        Counted prefixAt -> prefixAt (source + 1) - prefixAt source

-- | Decode a zero-based accepted rank in ascending source-rank order.
select :: SourceIndex -> Integer -> Maybe Integer
select index accepted
    | accepted < 0 || accepted >= cardinality index = Nothing
    | accepted == 0 = Just $ lower index
    | accepted == cardinality index - 1 = Just $ upper index - 1
    | Interval _ <- plan index = Just $ lower index + accepted
    | otherwise = Just $ search index (prefixCount index) accepted

-- | Decode a ticket in @[0, mass)@ to its weighted source occurrence.
selectByMass :: SourceIndex -> Integer -> Maybe Integer
selectByMass index ticket
    | ticket < 0 || ticket >= mass index = Nothing
    | ticket == 0 = Just $ lower index
    | ticket == mass index - 1 = Just $ upper index - 1
    | Interval sourceWeight <- plan index = Just $ lower index + ticket `quot` sourceWeight
    | otherwise = Just $ search index (prefixMass index) ticket

-- | Find the accepted rank of a source occurrence, if it is retained.
rank :: SourceIndex -> Integer -> Maybe Integer
rank index source
    | member index source = Just $ prefixCount index source
    | otherwise = Nothing

-- | Build a nonempty uniform interval, or retain its empty raw domain.
interval :: Integer -> Integer -> Integer -> Integer -> SourceIndex
interval bound first last_ sourceWeight
    | first == last_ = empty bound
    | otherwise = SourceIndex bound count (count * sourceWeight) first last_ (Interval sourceWeight)
  where
    count = last_ - first

-- | Compute prefix count and mass with the same product decomposition.
prefix :: SourceIndex -> Integer -> (Integer, Integer)
prefix index source
    | source <= lower index = (0, 0)
    | source >= upper index = (cardinality index, mass index)
    | otherwise = case plan index of
        Empty -> (0, 0)
        Interval sourceWeight ->
            let count = source - lower index
             in (count, count * sourceWeight)
        Union left right ->
            let (leftCount, leftMass) = prefix left source
                (rightCount, rightMass) = prefix right source
             in (leftCount + rightCount, leftMass + rightMass)
        Product left right ->
            let (leftRank, rightRank) = source `quotRem` domain right
                (leftCount, leftMass) = prefix left leftRank
                completeCount = leftCount * cardinality right
                completeMass = leftMass * mass right
             in if member left leftRank
                    then
                        let (rightCount, rightMass) = prefix right rightRank
                            partialMass
                                | rightMass == 0 = 0
                                | otherwise = weight left leftRank * rightMass
                         in (completeCount + rightCount, completeMass + partialMass)
                    else (completeCount, completeMass)
        Shift offset nested -> prefix nested $ source - offset
        Scale factor nested ->
            let (count, totalMass) = prefix nested source
             in (count, factor * totalMass)
        Counted prefixAt -> let count = prefixAt source in (count, count)

-- | Find the first source rank whose inclusive prefix exceeds the ticket.
search :: SourceIndex -> (Integer -> Integer) -> Integer -> Integer
search index prefixAt ticket = go (lower index) (upper index - 1)
  where
    go first last_
        | first == last_ = first
        | prefixAt (middle + 1) > ticket = go first middle
        | otherwise = go (middle + 1) last_
      where
        middle = first + (last_ - first) `quot` 2
