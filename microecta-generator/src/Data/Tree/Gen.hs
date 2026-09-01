{- | Backend-independent finite ranked generators.

This is the automaton-neutral layer shared by ECTA and LTA generators. A
language is compiled once into stable ranks; sampling, replay, and shrinking
then require no knowledge of the support automaton or its constraint theory.
-}
module Data.Tree.Gen (
    Indexed (..),
    Ranked,
    RankedError (..),
    GenBackend (..),
    fromIndexed,
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

import Data.ECTA.Gen.Internal.Sampler (GenBackend (..))
import Data.Tree.Gen.Internal
