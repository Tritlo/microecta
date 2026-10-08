{- | Recursive languages and the key masses that condition them.

A t'Recursive' is one @Mu@ automaton together with the size classes it
accepts. Members are reached through those classes rather than through a
cardinality, and 'boundedStatic' turns one back into a finite language that
keeps the ranks the recursive language already gave its members.
-}
module Data.CFTA.Gen.Internal.Recursive (
    -- * Recursive languages
    Recursive (..),
    RecursiveTerms (..),
    recursiveFromStatic,
    staticTerms,
    productTerms,
    choiceTerms,
    recursivePositions,
    boundedStatic,
    labelRecursive,
    mapRecursive,

    -- * Keyed recursive families
    KeyedRecursive (..),
    keyedRecursive,
    keyedRecursiveFromBuckets,
    mergeRecursiveGroups,
    choiceRecursive,

    -- * Masses
    MassIndex,
    massAtSize,
    keyedRecursiveMassAtSize,
    emptyMassIndex,
    productMassIndex,
) where

import Data.Hashable (Hashable)
import Data.List (sort)
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
import Data.CFTA.Gen.Label (ChoiceIndex (..), Label (..))
import Data.CFTA.Index (Cardinality (..), ClassRank (..), Rank (..), Size, everyRank)
import Data.CFTA.Ranked.Internal.Decoder (Plan (..), RankedValue (..), SizeClass (..))
import Data.CFTA.Ranked.Internal.Sampler
import Data.CFTA.Ranked.Internal.Size (
    SizeIndex (sizeClassCounts, sizeClassSelect),
    SizedRank (..),
    addSparse,
    choiceIndex,
    choicePosition,
    mapIndex,
    mapIndexWithRank,
    mulSparse,
    planPosition,
    productIndex,
    productPosition,
    sizeClassOf,
    sizeClasses,
    sizeMajorRank,
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
    , recursiveTerm :: Maybe (RecursiveTerms symbol)
    {- ^ The engine term of every member, indexed by the same size classes and
    positions as the values, and the members of a term. Every combinator keeps
    it; 'Nothing' means that a combinator does not track terms.
    -}
    , recursiveInspection :: Inspection symbol
    -- ^ A lazy diagnostic graph with occurrence labels and source values.
    }

{- | The terms of a recursive language.

A member is found by its size class and its position in that class, as in
'recursiveIndex'. Several members can have one term, as for a finite
language, so a term view gives a list of positions in ascending size-major
order.
-}
data RecursiveTerms symbol = RecursiveTerms
    { recursiveTermIndex :: SizeIndex (Tree.Tree (Label symbol))
    -- ^ The term of each member.
    , recursiveTermPositions :: TermView symbol -> [(SizedRank, Bool)]
    {- ^ The size class and position of each member whose term has the view,
    and whether the ranking checked every symbol of the term, as for
    'outcomeRanks'.
    -}
    }

-- | View a finite language as one size-stratified recursive component.
recursiveFromStatic :: Static symbol a -> Recursive symbol a
recursiveFromStatic static =
    Recursive
        (staticSupport static)
        (outcomeSizeIndex $ staticOutcomes static)
        sampling
        (isJust weight)
        (Just $ staticTerms static)
        (staticInspection static)
  where
    (sampling, weight) = staticSampling static

{- | The terms of a finite language, by the size classes of its plan. A rank
of the plan finds its size class and position with 'planPosition'.
-}
staticTerms :: Static symbol a -> RecursiveTerms symbol
staticTerms static =
    RecursiveTerms
        (mapIndexWithRank (\rank _ -> termOf rank) $ outcomeSizeIndex outcomes)
        ( \view ->
            sort
                [ (position, checked)
                | (rank, checked) <- outcomeRanks outcomes view
                , Just position <- [planPosition (outcomePlan outcomes) rank]
                ]
        )
  where
    outcomes = staticOutcomes static
    termOf rank = case outcomeSelect outcomes rank of
        Right outcome -> outcomeTerm outcome
        Left err ->
            error $
                "microcfta-generator bug in Data.CFTA.Gen.Internal.Recursive.staticTerms: \
                \a rank of the size index has no outcome: "
                    <> show err

{- | The terms of the applicative product of two recursive languages, whose
value indexes give the counts. The term of a member is the private
application of its function term to its argument term.
-}
productTerms ::
    SizeIndex f -> SizeIndex x -> RecursiveTerms symbol -> RecursiveTerms symbol -> RecursiveTerms symbol
productTerms indexF indexX termsF termsX =
    RecursiveTerms
        ( productIndex
            (mapIndex (\function argument -> Tree.Node Apply [function, argument]) $ recursiveTermIndex termsF)
            (recursiveTermIndex termsX)
        )
        positions
  where
    positions view = sort $ case view of
        WholeTerm (Tree.Node Apply [function, argument]) -> positionsFrom (WholeTerm function) argument
        WholeTerm _ -> []
        SpineView arguments -> spinePositions arguments
        LabelledView arguments -> spinePositions arguments
      where
        spinePositions arguments = case reverse arguments of
            argument : functionArguments -> positionsFrom (SpineView $ reverse functionArguments) argument
            [] -> []

        positionsFrom functionView argument =
            [ (productPosition indexF indexX functionPosition argumentPosition, functionChecked && argumentChecked)
            | (functionPosition, functionChecked) <- recursiveTermPositions termsF functionView
            , (argumentPosition, argumentChecked) <- recursiveTermPositions termsX $ WholeTerm argument
            ]

{- | The terms of ordered alternatives, whose value indexes give the counts.
The term of a member is the private choice wrapper of its alternative.
-}
choiceTerms :: [SizeIndex a] -> [RecursiveTerms symbol] -> RecursiveTerms symbol
choiceTerms indexes terms =
    RecursiveTerms
        ( choiceIndex
            [ mapIndex (\term -> Tree.Node (Choice branch) [term]) $ recursiveTermIndex branchTerms
            | (branch, branchTerms) <- zip [0 ..] terms
            ]
        )
        positions
  where
    positions view = sort $ case view of
        WholeTerm (Tree.Node (Choice branch) [child]) -> branchPositions branch $ WholeTerm child
        WholeTerm _ -> []
        SpineView [term] -> positions $ WholeTerm term
        SpineView _ -> []
        LabelledView _ -> concat [branchPositions branch view | branch <- map ChoiceIndex [0 .. length terms - 1]]
    branchPositions branch@(ChoiceIndex index) view = case drop index terms of
        branchTerms : _ ->
            [ (SizedRank size (choicePosition indexes branch size position), checked)
            | (SizedRank size position, checked) <- recursiveTermPositions branchTerms view
            ]
        [] -> []

{- | The size-major ranks of the members of a recursive language whose term
has the view, in ascending order, and whether the ranking checked every
symbol of the term.
-}
recursivePositions :: Recursive symbol a -> TermView symbol -> Maybe [(Rank, Bool)]
recursivePositions recursive view = do
    terms <- recursiveTerm recursive
    pure
        [ (sizeMajorRank (recursiveIndex recursive) position, checked)
        | (position, checked) <- recursiveTermPositions terms view
        ]

{- | Bound a recursive language to its members of size at most the bound.

The result is an ordinary finite language with the same size-major ranks the
recursive language gives its members, so a rank replays through either. Size
classes retain their count-based probability. Finite choices closed with
'atomicStatic' retain their own distribution inside each class. The support
stays the recursive automaton. A size bound restricts the rank space, not the
set of terms the automaton accepts.

Every member carries its engine term from the term index of the recursive
language, and a term ranks through its size class and position.
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
                    boundedRanks
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
    -- A bound keeps the size-major ranks of the members that it keeps.
    boundedRanks view =
        [ (sizeMajorRank (recursiveIndex recursive) position, checked)
        | Just terms <- [recursiveTerm recursive]
        , (position, checked) <- recursiveTermPositions terms view
        , rankSize position <= bound
        ]
    select index = case recursiveTermIndex <$> recursiveTerm recursive of
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
        , recursiveTerm = labelTerms <$> recursiveTerm recursive
        , recursiveInspection = labelInspection symbol $ recursiveInspection recursive
        }
  where
    -- The label replaces the private root of each term, so the inner
    -- language reads the children under it. The label checks its symbol.
    labelTerms terms = RecursiveTerms (mapIndex (labelTerm symbol) $ recursiveTermIndex terms) positions
      where
        positions view = case view of
            WholeTerm (Tree.Node (Label found) children) ->
                [ (position, checked && found == symbol)
                | (position, checked) <- recursiveTermPositions terms $ LabelledView children
                ]
            SpineView [term] -> positions $ WholeTerm term
            LabelledView [term] -> positions $ WholeTerm term
            _ -> []

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

{- | Map the values of a recursive language. The counts, ranks, terms,
support, and inspection do not change.
-}
mapRecursive :: (a -> b) -> Recursive symbol a -> Recursive symbol b
mapRecursive transform recursive =
    recursive
        { recursiveIndex = mapIndex transform $ recursiveIndex recursive
        , recursiveSampling = mapSampleIndex transform $ recursiveSampling recursive
        }

{- | A choice of recursive languages, in the order of the alternatives. The
caller gives the sampler, which selects an alternative by count or by mass,
and whether the choice keeps weights of its own.
-}
choiceRecursive ::
    (Hashable symbol, Typeable symbol) =>
    SampleIndex a -> Bool -> [Recursive symbol a] -> Recursive symbol a
choiceRecursive sampling weighted alternatives =
    Recursive
        (Node [Edge (Choice index) [recursiveSupport alternative] | (index, alternative) <- zip [0 ..] alternatives])
        (choiceIndex $ map recursiveIndex alternatives)
        sampling
        weighted
        (choiceTerms (map recursiveIndex alternatives) <$> traverse recursiveTerm alternatives)
        (choiceInspection $ map recursiveInspection alternatives)

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
            (choiceRecursive (choiceMassSampleIndex indexedSamplers) weighted $ map keyedRecursiveLanguage alternatives)
            masses
            massWeighted
  where
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
