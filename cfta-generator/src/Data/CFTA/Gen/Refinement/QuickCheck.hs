{- | QuickCheck integration for refinement generators.

This module re-exports "Data.CFTA.Gen.Refinement" and its qualified
do-notation, and adds the sampling, pools, and properties of
"Data.CFTA.Gen.QuickCheck". A deferred generator must be compiled before it
is sampled.
-}
module Data.CFTA.Gen.Refinement.QuickCheck (
    -- * Generators
    module Data.CFTA.Gen.Refinement,

    -- * Pools
    samplePool,
    freeze,

    -- * Sampling and properties
    toGen,
    toGenWithRank,
    toGenEither,
    forAll,
    forAllWithLimit,
    smallerMemberLimit,
    sized,

    -- * Qualified do-notation
    module Data.CFTA.Gen.Do,
) where

import Data.CFTA.Gen.Do
import Data.CFTA.Gen.QuickCheck (
    forAll,
    forAllWithLimit,
    freeze,
    samplePool,
    sized,
    smallerMemberLimit,
    toGen,
    toGenEither,
    toGenWithRank,
 )
import Data.CFTA.Gen.Refinement
