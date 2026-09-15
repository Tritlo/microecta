{- | The generator engine behind "Data.ECTA.Gen".

This module re-exports the engine as one interface. Finite languages are
represented as a t'Static': an ECTA support paired with an t'OutcomeIndex'
that counts, selects, decodes, and samples outcomes by rank. Recursive
languages keep their @Mu@ automaton and their size classes instead. The
sampling engine lives in "Data.Tree.Gen.Internal.Sampler". The public
generator types and combinators live in "Data.ECTA.Gen".
-}
module Data.ECTA.Gen.Internal (
    -- * Sources and failures
    Indexed (..),
    ECTAGenError (..),
    explain,

    -- * Languages
    Outcome (..),
    ArgChain (..),
    OutcomeIndex (..),
    Static (..),
    Recursive (..),
    KeyedBucket (..),
    KeyedRecursive (..),

    -- * Building languages
    pureStatic,
    indexedStatic,
    termStatic,
    applyStatic,
    labelStatic,
    labelRecursive,
    frequencyStatic,
    atomicStatic,
    mapStatic,
    boundedStatic,
    recursiveFromStatic,
    bucketFromOutcomes,
    mergeBucketGroup,
    mergeComponentsByKey,
    mergeRecursiveGroups,
    keyedRecursive,
    keyedRecursiveFromBuckets,

    -- * Joins
    joinStatic,
    relateStatic,
    joinNBucketStatic,
    recursiveJoin,
    groupOutcomes,

    -- * Argument chains
    ArgMaps (..),
    lookupArgs,
    mapChain,
    chainMass,

    -- * Masses
    emptyMassIndex,
    keyedRecursiveMassAtSize,

    -- * Inspection and lowering
    enumerateOutcomeIndex,
    compileOutcomes,
    sampleStatic,
    sampleStaticWithRank,
    compiledDecoder,
    checkIndex,
    normalize,

    -- * Support construction
    applySymbol,
    familyNode,
    frequencySymbol,
    restrictToKey,
) where

import Data.ECTA.Gen.Internal.Bucket
import Data.ECTA.Gen.Internal.Chain
import Data.ECTA.Gen.Internal.Error
import Data.ECTA.Gen.Internal.Join
import Data.ECTA.Gen.Internal.Recursive
import Data.ECTA.Gen.Internal.Static
import Data.ECTA.Gen.Internal.Support
import Data.Tree.Gen.Internal (Indexed (..))
