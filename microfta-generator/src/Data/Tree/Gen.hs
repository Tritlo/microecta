{- | Backend-independent finite ranked generators.

This is the layer below the automaton adapters. A language is compiled once
into stable ranks; sampling, replay, and shrinking then require no knowledge
of the support automaton or its constraint theory.

The types come from the @internal@ sublibrary, so their field documentation
is on that sublibrary's pages; in short:

* t'Indexed' describes a finite source by its cardinality and a decoder from a
  zero-based index.

* t'WeightedIndexed' separates replay ranks from sampling tickets: a
  cardinality, a total ticket weight, a decoder from a rank, and a map from a
  ticket to its rank. Every rank must receive at least one ticket.

* t'RankedError' reports an empty language, a non-positive weight, a total
  weight below the cardinality, a negative rank, or a rank outside the
  language.

* t'GenBackend' is what a sampling backend provides: selecting an integer or a
  machine 'Int' below a bound, weighted choice among backend generators, and
  retrying a backend-native generator until a predicate holds.

* t'Ranked' is a compiled language; it is abstract here and has 'Functor' and
  'Applicative' instances.

The functions below are the public contracts. Their implementations live in
"Data.Tree.Gen.Internal", which the constrained generator packages use
directly.
-}
module Data.Tree.Gen (
    Indexed (..),
    WeightedIndexed (..),
    Ranked,
    RankedError (..),
    GenBackend (..),
    fromIndexed,
    fromIndexedOnDemand,
    fromWeightedIndexedOnDemand,
    fromWeighted,
    frequency,
    oneof,
    cardinality,
    unrank,
    lower,
    lowerWithRank,
    shrinkRank,
    smallerMembers,
    sizeOfRank,
) where

import Data.Tree.Gen.Internal (Indexed (..), Ranked, RankedError (..), WeightedIndexed (..))
import qualified Data.Tree.Gen.Internal as Internal
import Data.Tree.Gen.Internal.Sampler (GenBackend (..))

-- | Build a ranked language from an indexed source.
fromIndexed :: Indexed a -> Either RankedError (Ranked a)
fromIndexed = Internal.fromIndexed

{- | Build a ranked language whose members are decoded only when selected.

Unlike 'fromIndexed', small sources are not tabulated while the rank decoder
is compiled. Automaton adapters use this to keep term materialization at the
enumeration boundary.
-}
fromIndexedOnDemand :: Indexed a -> Either RankedError (Ranked a)
fromIndexedOnDemand = Internal.fromIndexedOnDemand

{- | Build a weighted ranked language without enumerating its values or tickets.

Sampling selects one ticket and maps it to the retained replay rank. Weight
does not change cardinality or rank order. The constructor checks cardinality
and total weight only; it does not evaluate either callback.
-}
fromWeightedIndexedOnDemand :: WeightedIndexed a -> Either RankedError (Ranked a)
fromWeightedIndexedOnDemand = Internal.fromWeightedIndexedOnDemand

{- | Build a ranked language whose members have positive relative weights.

Weight affects sampling, not cardinality or rank order: each list entry has
exactly one stable rank.
-}
fromWeighted :: [(Integer, a)] -> Either RankedError (Ranked a)
fromWeighted = Internal.fromWeighted

-- | Combine non-empty alternatives with positive relative weights.
frequency :: [(Integer, Ranked a)] -> Either RankedError (Ranked a)
frequency = Internal.frequency

-- | Combine equally weighted non-empty alternatives.
oneof :: [Ranked a] -> Either RankedError (Ranked a)
oneof = Internal.oneof

-- | Return the exact number of stable ranks.
cardinality :: Ranked a -> Integer
cardinality = Internal.cardinality

-- | Decode one stable rank.
unrank :: Ranked a -> Integer -> Either RankedError a
unrank = Internal.unrank

-- | Lower a ranked language to any supported sampling backend.
lower :: (GenBackend gen) => Ranked a -> gen a
lower = Internal.lower

-- | Lower a ranked language while retaining the selected replay rank.
lowerWithRank :: (GenBackend gen) => Ranked a -> gen (Integer, a)
lowerWithRank = Internal.lowerWithRank

{- | Structural shrink candidates for one rank.

Each candidate is a strictly smaller valid rank of the same language whose
member is no larger than the current member, measured in source choices.
Earlier alternatives come first at their smallest member, then each product
component shrinks on its own. Use 'smallerMembers' for every member of
strictly smaller size.
-}
shrinkRank :: Ranked a -> Integer -> [Integer]
shrinkRank = Internal.shrinkRank

-- | Every member structurally smaller than the selected member, in size order.
smallerMembers :: Ranked a -> Integer -> [(Integer, a)]
smallerMembers = Internal.smallerMembers

-- | Structural size of the member at a valid rank.
sizeOfRank :: Ranked a -> Integer -> Maybe Int
sizeOfRank = Internal.sizeOfRank
