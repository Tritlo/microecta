{- | The generator engine behind "Data.CFTA.Gen.Equality".

This module re-exports the engine as one interface. Finite languages are
represented as a t'Static': an ECTA support paired with an t'OutcomeIndex'
that counts, selects, decodes, and samples outcomes by rank. Recursive
languages keep their @Mu@ automaton and their size classes instead. The
sampling engine lives in "Data.CFTA.Ranked.Internal.Sampler". The public
generator types and combinators live in "Data.CFTA.Gen.Equality".
-}
module Data.CFTA.Gen.Equality.Internal (
    -- * Sources and failures
    Indexed (..),
    GenError (..),
    explain,

    -- * Languages
    Inspection (..),
    InspectionSymbol (..),
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

import Data.CFTA.Gen.Equality.Internal.Bucket
import Data.CFTA.Gen.Equality.Internal.Chain
import Data.CFTA.Gen.Equality.Internal.Inspection
import Data.CFTA.Gen.Equality.Internal.Join
import Data.CFTA.Gen.Equality.Internal.Recursive
import Data.CFTA.Gen.Equality.Internal.Static
import Data.CFTA.Gen.Equality.Internal.Support
import Data.CFTA.Gen.Error
import Data.CFTA.Ranked.Internal (Indexed (..))
