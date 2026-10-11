{- | Finite languages with stable ranks, independent of the sampling backend.

The generator layers of this package build on this module. A language is
compiled once. Then 'unrank', sampling, and shrinking read the compiled
language and not the automaton that it came from.

* t'Indexed' is a finite source: a cardinality and a decoder from a
  zero-based rank. "Data.CFTA.Index" defines t'Data.CFTA.Index.Rank' and
  t'Data.CFTA.Index.Cardinality'.

* t'WeightedIndexed' is a weighted finite source. It has a cardinality, a
  total weight, a decoder from a rank, and a map from a ticket to a rank.
  Each rank must have at least one ticket.

* t'RankedError' reports an empty language, a weight below one, a total
  weight below the cardinality, a negative rank, or a rank outside the
  language.

* t'GenBackend' is a sampling backend. It selects a rank below a
  cardinality, an 'Int' below a bound, one of several weighted generators,
  and one of several weighted values.

* t'Ranked' is a compiled language. This module does not export its
  constructor. It has 'Functor' and 'Applicative' instances.

* t'RankedValue' is a value with its rank. 'lowerWithRank' and
  'smallerMembers' give these.

The implementations are in "Data.CFTA.Ranked.Internal". The generator layers
of this package use that module directly.
-}
module Data.CFTA.Ranked (
    Indexed (..),
    WeightedIndexed (..),
    Ranked,
    RankedError (..),
    RankedValue (..),
    GenBackend (..),
    fromIndexed,
    fromIndexedOnDemand,
    fromWeightedIndexedOnDemand,
    fromWeighted,
    frequency,
    oneof,
    pay,
    cardinality,
    unrank,
    lower,
    lowerWithRank,
    shrinkRank,
    smallerMembers,
    sizeOfRank,
) where

import Data.CFTA.Ranked.Internal (
    Indexed (..),
    Ranked,
    RankedError (..),
    WeightedIndexed (..),
    cardinality,
    frequency,
    fromIndexed,
    fromIndexedOnDemand,
    fromWeighted,
    fromWeightedIndexedOnDemand,
    lower,
    lowerWithRank,
    oneof,
    pay,
    shrinkRank,
    sizeOfRank,
    smallerMembers,
    unrank,
 )
import Data.CFTA.Ranked.Internal.Decoder (RankedValue (..))
import Data.CFTA.Ranked.Internal.Sampler (GenBackend (..))
