{- | Recursive languages and the key masses that condition them.

A t'Recursive' is one @Mu@ automaton together with the size classes it
accepts. Members are reached through those classes rather than through a
cardinality, and 'boundedStatic' turns one back into a finite language that
keeps the ranks the recursive language already gave its members.
-}
module Data.CFTA.Gen.Equality.Internal.Recursive (
    -- * Recursive languages
    Recursive (..),
    recursiveFromStatic,
    boundedStatic,
    labelRecursive,

    -- * Keyed recursive families
    KeyedRecursive (..),
    keyedRecursive,
    keyedRecursiveFromBuckets,
    mergeRecursiveGroups,

    -- * Masses
    MassIndex,
    massAtSize,
    keyedRecursiveMassAtSize,
    emptyMassIndex,
    productMassIndex,
) where

import Data.CFTA.Constraint (Constraint (..))
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import Data.CFTA.Equality (Edge (Edge), Node (Node))
import Data.CFTA.Gen.Equality.Internal.Bucket (KeyedBucket (..))
import Data.CFTA.Gen.Equality.Internal.Inspection
import Data.CFTA.Gen.Equality.Internal.Static
import Data.CFTA.Gen.Equality.Internal.Support (labelSupport, labelTerm)
import Data.CFTA.Gen.Error (GenError (..))
import Data.CFTA.Gen.Label (Label (..))
import Data.CFTA.Ranked.Internal.Decoder (Plan (..))
import Data.CFTA.Ranked.Internal.Sampler
import Data.CFTA.Ranked.Internal.Size (
    SizeIndex (sizeClassCounts),
    choiceIndex,
    sizeClasses,
 )

{- | One recursive ECTA and the size-stratified language it accepts.

The support is a @Mu@ node: a finite automaton standing for an unbounded
language. Members are reached through size classes rather than a
cardinality, and ranks are size-major, so bounding the language with
'boundedStatic' keeps every rank it already had.
-}
data Recursive symbol constraint a = Recursive
    { recursiveSupport :: Node (Label symbol) constraint
    {- ^ The ECTA support is demand-driven. Counting, mass, and sampling
    interpret the same recursive declaration without forcing this field.
    A support observer builds it once when needed.
    -}
    , recursiveIndex :: SizeIndex a
    , recursiveSampling :: SampleIndex a
    -- ^ A valid sampler at every size, tied through the recursive knot.
    , recursiveWeighted :: !Bool
    {- ^ Whether any reachable atom is non-uniform. This is read from the
    non-knot body, so bounded lowering can choose the sampler without forcing
    a Boolean fixpoint. 'False' permits uniform rank selection instead.
    -}
    , recursiveOccurrence :: !Bool
    {- ^ Whether this language is, or is built from, the argument of a
    @recur@ or @recurGrouped@ body that is still being defined. Bounding such
    a language is ill-founded — its size classes are what the definition is
    computing — so 'boundedStatic' must not be reached through it. The flag is
    set on the placeholders and cleared on the finished result, and is
    therefore not the Boolean knot @usedOccurrence@ is.
    -}
    , recursiveTerm :: Maybe (a -> Tree.Tree (Label symbol))
    {- ^ How to read a member's ECTA term off its value, when the values are
    the accepted terms themselves. Every combinator drops it, because a
    mapped or combined value no longer stands for one term of the
    support.
    -}
    , recursiveInspection :: Inspection symbol constraint
    -- ^ A lazy diagnostic graph with occurrence labels and source values.
    }

-- | View a finite language as one size-stratified recursive component.
recursiveFromStatic :: Static symbol constraint a -> Recursive symbol constraint a
recursiveFromStatic static =
    Recursive
        (staticSupport static)
        index
        sampling
        weighted
        False
        Nothing
        (staticInspection static)
  where
    outcomes = staticOutcomes static
    index = outcomeSizeIndex outcomes
    (sampling, weighted)
        | staticAtomic static =
            ( atomicSampleIndex $ outcomeSampler outcomes
            , case outcomeUniformMass outcomes of
                Nothing -> True
                Just _ -> False
            )
        | otherwise = (uniformSampleIndex index, False)

{- | Bound a recursive language to its members of size at most the bound.

The result is an ordinary finite language with the same size-major ranks the
recursive language gives its members, so a rank replays through either. Size
classes retain their count-based probability. Finite choices closed with
'atomicStatic' retain their own distribution inside each class. The support
stays the recursive automaton — a size bound restricts the rank space, not the
set of terms the automaton accepts.

Members carry a retained t'Tree.Tree' only when the values are the accepted terms
themselves, as they are for an automaton read with @fromAutomaton@; otherwise
inspection through 'outcomeSelect' reports
'CannotInspectRecursiveGenerator', while sampling, unranking, and shrinking
go through the value decoder and the plan.
-}
boundedStatic :: Int -> Recursive symbol constraint a -> Either GenError (Static symbol constraint a)
boundedStatic bound recursive
    | totalOutcomes <= 0 = Left EmptyGenerator
    | otherwise =
        Right $
            Static
                (recursiveSupport recursive)
                ( mkOutcomeIndex
                    totalOutcomes
                    uniformMass
                    select
                    selectValue
                    sampler
                    plan
                )
                False
                (recursiveInspection recursive)
  where
    select index = case recursiveTerm recursive of
        Nothing -> Left CannotInspectRecursiveGenerator
        Just readTerm -> do
            checkIndex totalOutcomes index
            let value = selectValue index
            pure $
                Outcome
                    (readTerm value)
                    (1 / fromInteger totalOutcomes)
                    value
                    (fmap plainSymbol $ readTerm value)

    classes = sizeClasses bound $ recursiveIndex recursive
    plan = PlanSized classes
    totalOutcomes = sum [count | (_, count, _, _) <- classes]
    uniformMass
        | recursiveWeighted recursive = Nothing
        | otherwise = Just $ 1 / fromInteger totalOutcomes
    sampler
        | recursiveWeighted recursive =
            boundedSampler classes $ recursiveSampling recursive
        | otherwise = uniformSampler totalOutcomes selectValue

    selectValue = go classes
      where
        go [] _ =
            error
                "microcfta-generator bug in Data.CFTA.Gen.Equality.Internal.Recursive.boundedStatic: \
                \rank outside the bounded language"
        go ((_, count, decode, _) : rest) index
            | index < count = decode index
            | otherwise = go rest (index - count)

-- | Close one recursive child layer with a user-facing node label.
labelRecursive ::
    (Constraint constraint, Hashable symbol, Typeable symbol) =>
    symbol -> Recursive symbol constraint a -> Recursive symbol constraint a
labelRecursive symbol recursive =
    recursive
        { recursiveSupport = labelSupport symbol $ recursiveSupport recursive
        , recursiveTerm = fmap (labelTerm symbol .) $ recursiveTerm recursive
        , recursiveInspection = labelInspection symbol $ recursiveInspection recursive
        }

{- | One recursive language conditioned on a retained key.

The mass is unnormalized. Across all sibling keys it sums to the structural
member count at that size. This keeps language counts separate from sampler
probabilities while allowing keys to be merged without losing either.
-}
data KeyedRecursive symbol constraint a = KeyedRecursive
    { keyedRecursiveLanguage :: !(Recursive symbol constraint a)
    , keyedRecursiveMasses :: MassIndex
    , keyedRecursiveMassWeighted :: !Bool
    }

-- | Put a complete recursive language under one key.
keyedRecursive :: Recursive symbol constraint a -> KeyedRecursive symbol constraint a
keyedRecursive recursive =
    KeyedRecursive
        recursive
        (countMassIndex $ recursiveIndex recursive)
        False

-- | Turn every finite key bucket into one size-indexed recursive group.
keyedRecursiveFromBuckets ::
    Map.Map key (KeyedBucket symbol constraint a) -> Map.Map key (KeyedRecursive symbol constraint a)
keyedRecursiveFromBuckets buckets = fmap fromBucket buckets
  where
    totalCount =
        sum
            [ outcomeCardinality $ staticOutcomes $ keyedBucketStatic bucket
            | bucket <- Map.elems buckets
            ]

    fromBucket bucket =
        KeyedRecursive
            recursive
            masses
            massWeighted
      where
        static = keyedBucketStatic bucket
        recursive = recursiveFromStatic static
        bucketCount = outcomeCardinality $ staticOutcomes static
        masses
            | staticAtomic static =
                atomicMassIndex $ fromInteger totalCount * keyedBucketMass bucket
            | otherwise = countMassIndex $ recursiveIndex recursive
        massWeighted =
            staticAtomic static
                && fromInteger totalCount * keyedBucketMass bucket /= fromInteger bucketCount

{- | Merge recursive groups sharing a key into one alternative each.

Alternatives keep their order, as they do in the finite merge, so ranks stay
deterministic.
-}
mergeRecursiveGroups ::
    (Constraint constraint, Hashable symbol, Typeable symbol) =>
    [KeyedRecursive symbol constraint a] -> Maybe (KeyedRecursive symbol constraint a)
mergeRecursiveGroups [] = Nothing
mergeRecursiveGroups [only] = Just only
mergeRecursiveGroups alternatives =
    Just $
        KeyedRecursive
            ( Recursive
                ( Node
                    [ Edge (Choice branchIndex) [recursiveSupport $ keyedRecursiveLanguage alternative]
                    | (branchIndex, alternative) <- zip [0 ..] alternatives
                    ]
                )
                index
                (choiceMassSampleIndex indexedSamplers)
                weighted
                (any (recursiveOccurrence . keyedRecursiveLanguage) alternatives)
                Nothing
                (choiceInspection $ map (recursiveInspection . keyedRecursiveLanguage) alternatives)
            )
            masses
            massWeighted
  where
    index = choiceIndex $ map (recursiveIndex . keyedRecursiveLanguage) alternatives
    masses = sumMassIndexes $ map keyedRecursiveMasses alternatives
    massWeighted = any keyedRecursiveMassWeighted alternatives
    weighted =
        massWeighted
            || any (recursiveWeighted . keyedRecursiveLanguage) alternatives
    indexedSamplers =
        [ ( recursiveIndex $ keyedRecursiveLanguage alternative
          , keyedRecursiveMassAtSize alternative
          , recursiveSampling $ keyedRecursiveLanguage alternative
          )
        | alternative <- alternatives
        ]

-- | A memoized unnormalized mass for every positive structural size.
newtype MassIndex = MassIndex [Rational]

-- | Read one size, returning zero outside the positive size classes.
massAtSize :: MassIndex -> Int -> Rational
massAtSize _ size | size < 1 = 0
massAtSize (MassIndex masses) size = masses !! (size - 1)

-- | Read one recursive group's mass at a size.
keyedRecursiveMassAtSize :: KeyedRecursive symbol constraint a -> Int -> Rational
keyedRecursiveMassAtSize recursive = massAtSize $ keyedRecursiveMasses recursive

-- | A language with no members at any size.
emptyMassIndex :: MassIndex
emptyMassIndex = MassIndex $ repeat 0

-- | Structural counts interpreted as unnormalized uniform mass.
countMassIndex :: SizeIndex a -> MassIndex
countMassIndex index =
    MassIndex $ map fromInteger (sizeClassCounts index) <> repeat 0

-- | One finite atom's complete mass at size one.
atomicMassIndex :: Rational -> MassIndex
atomicMassIndex mass = MassIndex $ mass : repeat 0

-- | Add alternative masses pointwise.
sumMassIndexes :: [MassIndex] -> MassIndex
sumMassIndexes indexes =
    MassIndex
        [ sum [massAtSize index size | index <- indexes]
        | size <- [1 ..]
        ]

-- | Convolve two positive-size mass series.
productMassIndex :: MassIndex -> MassIndex -> MassIndex
productMassIndex left right =
    MassIndex
        [ sum
            [ massAtSize left leftSize * massAtSize right (size - leftSize)
            | leftSize <- [1 .. size - 1]
            ]
        | size <- [1 ..]
        ]
