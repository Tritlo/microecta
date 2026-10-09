{- | Recursive languages and the key masses that condition them.

A t'Recursive' is one @Mu@ automaton together with the size classes it
accepts. Members are reached through those classes rather than through a
cardinality, and 'boundedStatic' turns one back into a finite language that
keeps the ranks the recursive language already gave its members.
-}
module Data.CFTA.Gen.Internal.Recursive (
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

import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import Data.CFTA.Equality (Edge (Edge), Node (Node))
import Data.CFTA.Gen.Error (GenError (..))
import Data.CFTA.Gen.Internal.Bucket (KeyedBucket (..))
import Data.CFTA.Gen.Internal.Inspection
import Data.CFTA.Gen.Internal.Static
import Data.CFTA.Gen.Internal.Support (labelSupport, labelTerm)
import Data.CFTA.Gen.Label (Label (..))
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Rank (..), Size, everyRank)
import Data.CFTA.Ranked.Internal.Decoder (Plan (..), RankedValue (..), SizeClass (..))
import Data.CFTA.Ranked.Internal.Sampler
import Data.CFTA.Ranked.Internal.Size (
    SizeIndex (sizeClassCounts, sizeClassSelect),
    SizedRank (..),
    addSparse,
    choiceIndex,
    mapIndex,
    mulSparse,
    sizeClassOf,
    sizeClasses,
    valueAtSize,
 )

{- | One recursive ECTA and the size-stratified language it accepts.

The support is a @Mu@ node: a finite automaton standing for an unbounded
language. Members are reached through size classes rather than a
cardinality, and ranks are size-major, so bounding the language with
'boundedStatic' keeps every rank it already had.
-}
data Recursive symbol a = Recursive
    { recursiveSupport :: Node (Label symbol)
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
    , recursiveTerm :: Maybe (SizeIndex (Tree.Tree (Label symbol)))
    {- ^ The ECTA term of every member, indexed by the same size-major ranks
    as the values, when the language was read from an automaton. Mapping keeps
    it; combining languages drops it, because a combined member no longer
    stands for one term of the support.
    -}
    , recursiveInspection :: Inspection symbol
    -- ^ A lazy diagnostic graph with occurrence labels and source values.
    }

-- | View a finite language as one size-stratified recursive component.
recursiveFromStatic :: Static symbol a -> Recursive symbol a
recursiveFromStatic static =
    Recursive
        (staticSupport static)
        (outcomeSizeIndex $ staticOutcomes static)
        sampling
        (isJust weight)
        Nothing
        (staticInspection static)
  where
    (sampling, weight) = staticSampling static

{- | Bound a recursive language to its members of size at most the bound.

The result is an ordinary finite language with the same size-major ranks the
recursive language gives its members, so a rank replays through either. Size
classes retain their count-based probability. Finite choices closed with
'atomicStatic' retain their own distribution inside each class. The support
stays the recursive automaton. A size bound restricts the rank space, not the
set of terms the automaton accepts.

Members carry a retained t'Tree.Tree' only when the language was read from an
automaton with @fromAutomaton@, possibly mapped; otherwise inspection through
'outcomeSelect' reports 'CannotInspectRecursiveGenerator', while sampling,
unranking, and shrinking go through the value decoder and the plan.
-}
boundedStatic :: Size -> Recursive symbol a -> Either GenError (Static symbol a)
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
                    { outcomeSizeSampling = sizeSampling
                    }
                False
                (recursiveInspection recursive)
                -- A recursive language does not keep the root count of its members.
                ( commonRootCount
                    [either (const NoCommonCount) (RootCount . termRootCount . outcomeTerm) $ select rank | rank <- everyRank totalOutcomes]
                )
  where
    select index = case recursiveTerm recursive of
        Nothing -> Left CannotInspectRecursiveGenerator
        Just terms -> do
            checkIndex totalOutcomes index
            let term = case sizeClassOf terms index of
                    Just (SizedRank size position) -> rankedValue $ sizeClassSelect terms size position
                    Nothing ->
                        error
                            "microcfta-generator bug in Data.CFTA.Gen.Internal.Recursive.boundedStatic: \
                            \a member without a term"
            weight <- maybe (Right 1) (\(_, weightAt) -> weightAt index) sizeSampling
            pure $
                Outcome
                    term
                    (weight / toRational totalOutcomes)
                    (selectValue index)
                    (fmap plainSymbol term)

    -- The bounded language keeps the sampler of each size class, so a bound
    -- of it, or a recursion over it, keeps its atomic distributions.
    sizeSampling
        | recursiveWeighted recursive =
            Just (recursiveSampling recursive, Right . classWeight classMasses)
        | otherwise = Nothing
      where
        classWeight [] _ =
            error
                "microcfta-generator bug in Data.CFTA.Gen.Internal.Recursive.boundedStatic: \
                \rank outside the bounded language"
        classWeight ((Cardinality count, masses) : rest) index@(Rank rank)
            | rank < count = fromInteger count * Map.findWithDefault 0 index masses
            | otherwise = classWeight rest (Rank $ rank - count)
    -- The exact distribution of each class sampler, by position in the class.
    -- A recursive language has no finite weights to read, so this interprets
    -- the sampler. The exact interpretation gives one outcome for each value of
    -- an atomic choice, so the cost grows with the members of the class. It is
    -- computed once, on first use, and only an enumeration of the outcomes
    -- (such as 'pmf') reads it; sampling and ranking do not.
    classMasses =
        [ ( count
          , Map.fromListWith
                (+)
                [ (position, mass)
                | (mass, RankedValue position _) <-
                    runExact $ runRankSampler $ samplerAtSize (recursiveSampling recursive) size
                ]
          )
        | SizeClass{classSize = size, classCardinality = count} <- classes
        ]
    classes = sizeClasses bound $ recursiveIndex recursive
    plan = PlanSized classes
    totalOutcomes = sum $ map classCardinality classes
    uniformMass
        | recursiveWeighted recursive = Nothing
        | otherwise = Just $ 1 / toRational totalOutcomes
    sampler
        | recursiveWeighted recursive =
            boundedSampler classes $ recursiveSampling recursive
        | otherwise = uniformSampler totalOutcomes selectValue

    selectValue = go classes
      where
        go [] _ =
            error
                "microcfta-generator bug in Data.CFTA.Gen.Internal.Recursive.boundedStatic: \
                \rank outside the bounded language"
        go (SizeClass{classCardinality = Cardinality count, classMember = decode} : rest) (Rank index)
            | index < count = decode $ ClassRank index
            | otherwise = go rest (Rank $ index - count)

-- | Close one recursive child layer with a user-facing node label.
labelRecursive ::
    (Hashable symbol, Typeable symbol) =>
    symbol -> Recursive symbol a -> Recursive symbol a
labelRecursive symbol recursive =
    recursive
        { recursiveSupport = labelSupport symbol $ recursiveSupport recursive
        , recursiveTerm = mapIndex (labelTerm symbol) <$> recursiveTerm recursive
        , recursiveInspection = labelInspection symbol $ recursiveInspection recursive
        }

{- | One recursive language conditioned on a retained key.

The mass is unnormalized. Across all sibling keys it sums to the structural
member count at that size. This keeps language counts separate from sampler
probabilities while allowing keys to be merged without losing either.
-}
data KeyedRecursive symbol a = KeyedRecursive
    { keyedRecursiveLanguage :: !(Recursive symbol a)
    , keyedRecursiveMasses :: MassIndex
    , keyedRecursiveMassWeighted :: !Bool
    }

-- | Put a complete recursive language under one key.
keyedRecursive :: Recursive symbol a -> KeyedRecursive symbol a
keyedRecursive recursive =
    KeyedRecursive
        recursive
        (countMassIndex $ recursiveIndex recursive)
        False

-- | Turn every finite key bucket into one size-indexed recursive group.
keyedRecursiveFromBuckets ::
    Map.Map key (KeyedBucket symbol a) -> Map.Map key (KeyedRecursive symbol a)
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
                atomicMassIndex $ toRational totalCount * keyedBucketMass bucket
            | otherwise = countMassIndex $ recursiveIndex recursive
        massWeighted =
            staticAtomic static
                && toRational totalCount * keyedBucketMass bucket /= toRational bucketCount

{- | Merge recursive groups sharing a key into one alternative each.

Alternatives keep their order, as they do in the finite merge, so ranks stay
deterministic.
-}
mergeRecursiveGroups ::
    (Hashable symbol, Typeable symbol) =>
    [KeyedRecursive symbol a] -> Maybe (KeyedRecursive symbol a)
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

{- | A memoized unnormalized mass for sizes in ascending order. Sizes without
members are left out, except for the zero mass that a product starts with.
-}
newtype MassIndex = MassIndex [(Size, Rational)]

-- | Read one size, returning zero outside the sizes with mass.
massAtSize :: MassIndex -> Size -> Rational
massAtSize (MassIndex masses) = valueAtSize masses

-- | Read one recursive group's mass at a size.
keyedRecursiveMassAtSize :: KeyedRecursive symbol a -> Size -> Rational
keyedRecursiveMassAtSize recursive = massAtSize $ keyedRecursiveMasses recursive

-- | A language with no members at any size.
emptyMassIndex :: MassIndex
emptyMassIndex = MassIndex []

-- | Structural counts interpreted as unnormalized uniform mass.
countMassIndex :: SizeIndex a -> MassIndex
countMassIndex index =
    MassIndex [(size, toRational count) | (size, count) <- sizeClassCounts index]

-- | One finite atom's complete mass at size one.
atomicMassIndex :: Rational -> MassIndex
atomicMassIndex mass = MassIndex [(1, mass) | mass > 0]

-- | Add alternative masses by size.
sumMassIndexes :: [MassIndex] -> MassIndex
sumMassIndexes indexes = MassIndex $ foldr (\(MassIndex masses) -> addSparse masses) [] indexes

{- | Convolve two mass series: the sizes of a pair add, and the masses
multiply. The zero mass at size one lets a recursive knot of masses give its
smallest sizes before the product is computed, as for the size counts.
-}
productMassIndex :: MassIndex -> MassIndex -> MassIndex
productMassIndex (MassIndex left) (MassIndex right) = MassIndex $ (1, 0) : mulSparse left right
