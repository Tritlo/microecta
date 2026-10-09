{- | Finite languages and the builders that compose them.

A t'Static' is an ECTA support paired with an t'OutcomeIndex' that counts,
selects, decodes, and samples outcomes by rank. The basic finite combinators
of "Data.CFTA.Gen" are one function here: pure, elements, frequency, fmap,
application, atomic marking, and labelling. Joins, grouping, and recursion
live in "Data.CFTA.Gen.Internal.Join", "Data.CFTA.Gen.Internal.Grouped",
"Data.CFTA.Gen.Internal.Bucket", and "Data.CFTA.Gen.Internal.Recur". The
sampling engine itself lives in
"Data.CFTA.Ranked.Internal.Sampler".
-}
module Data.CFTA.Gen.Internal.Static (
    -- * Languages
    Outcome (..),
    OutcomeIndex (..),
    mkOutcomeIndex,
    seqPlan,
    Static (..),
    staticSampling,
    RootCount (..),
    termRootCount,
    addRootCounts,
    commonRootCount,

    -- * Building languages
    pureStatic,
    indexedStatic,
    indexedStaticWithLabels,
    termStatic,
    applyStatic,
    frequencyStatic,
    mapStatic,
    atomicStatic,
    labelStatic,

    -- * Sampling and lowering
    sequenceSampler,
    sampleStatic,
    sampleStaticWithRank,

    -- * Inspection
    enumerateOutcomeIndex,
    enumerateWeighted,
    compileOutcomes,
    commonValue,
    checkIndex,
    normalize,
    integerOutcomes,
) where

import qualified Data.Bifunctor as Bifunctor
import Data.Foldable (toList)
import Data.Hashable (Hashable)
import Data.Maybe (fromMaybe, isJust)
import Data.Sequence (Seq)
import qualified Data.Sequence as Sequence
import Data.Text (Text)
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import Data.CFTA.Equality (Edge (Edge), Node (Node))
import Data.CFTA.Gen.Error (GenError (..))
import Data.CFTA.Gen.Internal.Inspection
import Data.CFTA.Gen.Internal.Support (labelSupport, labelTerm, labelTermWith, relabel)
import Data.CFTA.Gen.Label (ChoiceIndex, Label (..))
import Data.CFTA.Index (
    Cardinality (..),
    Rank (..),
    RankOffset (..),
    Weight,
    everyRank,
    nextOffset,
    rebaseRank,
    splitRank,
 )
import Data.CFTA.Ranked.Internal (Indexed (..))
import qualified Data.CFTA.Ranked.Internal as Ranked
import Data.CFTA.Ranked.Internal.Decoder (
    Plan (..),
    RankDecoder (..),
    RankedValue (RankedValue, rankedValue),
    compilePlan,
    offsetRankedValue,
    sharedChoiceBound,
 )
import Data.CFTA.Ranked.Internal.Sampler
import Data.CFTA.Ranked.Internal.Size (SizeIndex, sizeIndex)

-- | One term, its normalized probability mass, and its decoded value.
data Outcome symbol a = Outcome
    { outcomeTerm :: Tree.Tree (Label symbol)
    , outcomeMass :: Rational
    , outcomeValue :: a
    , outcomeInspection :: Tree.Tree (InspectionSymbol symbol)
    -- ^ Source descriptions for a selected outcome, built only for inspection.
    }

-- | A finite language with exact cardinality and rank-based selection.
data OutcomeIndex symbol a = OutcomeIndex
    { outcomeCardinality :: !Cardinality
    , outcomeUniformMass :: !(Maybe Rational)
    , outcomeSelect :: Rank -> Either GenError (Outcome symbol a)
    , outcomeValueAt :: Rank -> a
    , outcomeSampler :: Sampler a
    {- ^ The compositional sampler is demand-driven. Uniform lowering uses the
    compiled rank plan instead, while weighted and atomic paths force this
    fallback once when they need it.
    -}
    , outcomePlan :: Plan a
    , outcomeSizeIndex :: SizeIndex a
    {- ^ The size classes of 'outcomePlan', built on first use and retained so
    a shrink loop builds them once. Construct through 'mkOutcomeIndex'.
    -}
    , outcomeDecoder :: RankDecoder a
    {- ^ The compiled 'outcomePlan', built on first use and retained.
    'sampleStatic' and 'sampleStaticWithRank' read this field, so every sample
    that they draw shares one decoder whatever the optimizer does with the
    sampler's function body. The samplers of the constructors do not read it.
    -}
    , outcomeSizeSampling :: Maybe (SampleIndex a, Rank -> Either GenError Rational)
    {- ^ The sampler of each size class, and the weight of each rank inside its
    size class, when a component atomic choice is not uniform. The weight of a
    rank is its mass inside its size class times the number of members of the
    class, so the weights of one size class add up to its member count. The
    positions of the sampler are the positions of 'outcomeSizeIndex'.
    'Nothing' means that every size class is uniform, and every rank has the
    weight one. 'mkOutcomeIndex' sets 'Nothing'; 'applyStatic' and
    'frequencyStatic' set a sampler and a weight from their components.
    -}
    }

-- | Build an outcome index whose size classes are derived from its plan.
mkOutcomeIndex ::
    Cardinality ->
    Maybe Rational ->
    (Rank -> Either GenError (Outcome symbol a)) ->
    (Rank -> a) ->
    Sampler a ->
    Plan a ->
    OutcomeIndex symbol a
mkOutcomeIndex total mass select valueAt sampler plan =
    OutcomeIndex total mass select valueAt sampler plan (sizeIndex plan) (compilePlan total plan) Nothing

-- | Decode positions of one enumerated outcome sequence.
seqPlan :: Seq (Outcome symbol a) -> Plan a
seqPlan outcomes =
    PlanSelect
        (toEnum $ Sequence.length outcomes)
        (outcomeValue . Sequence.index outcomes . fromEnum)

-- | One transparent ECTA with a matching indexed outcome language.
data Static symbol a = Static
    { staticSupport :: Node (Label symbol)
    {- ^ The ECTA support is demand-driven. Counting, mass, and sampling
    use the outcome index without forcing this field. A support observer builds
    it when needed; finite combinators retain their support work as a thunk.
    -}
    , staticOutcomes :: !(OutcomeIndex symbol a)
    , staticAtomic :: !Bool
    {- ^ Whether an explicit atomic boundary closes this finite language.

    Ordinary finite weights do not control recursive structure. 'atomicStatic'
    sets this marker so 'staticSampling' can preserve them as one source
    choice. The sampler itself already lives in 'staticOutcomes'.
    -}
    , staticInspection :: Inspection symbol
    -- ^ Diagnostic structure. Counting and decoding do not force this field.
    , staticRootCount :: RootCount
    {- ^ The number of user roots that the term of each member has, as
    'termRootCount' counts them, when all members have the same number, and
    'NoCommonCount' otherwise. Each combinator sets it from its parts, so
    reading it lists no member. A language that does not know it lists its
    members on first use.
    -}
    }

{- | The sampler of each size class of a finite language, and the weight of
each rank inside its size class when that sampler is not uniform.

Inside a size class, the ordinary finite weights of the language become
member counts. An atomic choice keeps its own distribution, also when it is
a component of a product or of a choice. 'outcomeSizeSampling' describes the
weight. The weight of an atomic choice comes from its exact outcome masses.
-}
staticSampling :: Static symbol a -> (SampleIndex a, Maybe (Rank -> Either GenError Rational))
staticSampling static
    | staticAtomic static =
        ( atomicSampleIndex $ outcomeSampler outcomes
        , case outcomeUniformMass outcomes of
            Nothing -> Just atomWeight
            Just _ -> Nothing
        )
    | Just (sampling, weight) <- outcomeSizeSampling outcomes = (sampling, Just weight)
    | otherwise = (uniformSampleIndex $ outcomeSizeIndex outcomes, Nothing)
  where
    outcomes = staticOutcomes static
    -- Every member of an atom has size one, so its mass inside its size class
    -- is its mass.
    atomWeight rank =
        (* toRational (outcomeCardinality outcomes)) . outcomeMass
            <$> outcomeSelect outcomes rank

-- | The one-outcome language of a single value.
pureStatic :: (Hashable symbol, Typeable symbol) => a -> Static symbol a
pureStatic value =
    Static
        (Node [Edge Pure []])
        ( mkOutcomeIndex
            1
            (Just 1)
            ( \index -> do
                checkIndex 1 index
                pure $ Outcome (Tree.Node Pure []) 1 value (Tree.Node (plainSymbol Pure) [])
            )
            (const value)
            (uniformSampler 1 $ const value)
            (PlanSelect 1 $ const value)
        )
        False
        (Inspection Nothing $ Node [Edge (plainSymbol Pure) []])
        (RootCount 0)

-- | The language of one finite indexed source.
indexedStatic :: (Hashable symbol, Typeable symbol) => Indexed a -> Static symbol a
indexedStatic = indexedStaticWithLabels $ const Nothing

-- | Retain source names independently of values and rank decoding.
indexedStaticWithLabels ::
    (Hashable symbol, Typeable symbol) =>
    (Rank -> Maybe Text) -> Indexed a -> Static symbol a
indexedStaticWithLabels label indexed =
    Static
        (Node [Edge (Index index) [] | index <- everyRank totalOutcomes])
        ( mkOutcomeIndex
            totalOutcomes
            (Just $ 1 / toRational totalOutcomes)
            select
            (indexedSelect indexed)
            (uniformSampler totalOutcomes $ indexedSelect indexed)
            (PlanSelect totalOutcomes $ indexedSelect indexed)
        )
        False
        (Inspection Nothing $ Node [Edge (namedSymbol index) [] | index <- everyRank totalOutcomes])
        (RootCount 0)
  where
    namedSymbol index = InspectionSymbol (Index index) (label index)
    totalOutcomes = indexedCardinality indexed
    select index = do
        checkIndex totalOutcomes index
        pure $
            Outcome
                (Tree.Node (Index index) [])
                (1 / toRational totalOutcomes)
                (indexedSelect indexed index)
                (Tree.Node (namedSymbol index) [])

{- | Retain a shared ranked term compiler and its exact equality support.

The values are the accepted terms of the automaton, and the support is the
automaton under user labels. Sampling is uniform over accepted terms. The
common plan supplies replay and structural shrinking. No term is decoded
while this adapter is constructed.
-}
termStatic ::
    (Hashable symbol, Typeable symbol) =>
    Node symbol -> Ranked.Ranked (Tree.Tree symbol) -> Static symbol (Tree.Tree symbol)
termStatic root ranked =
    Static
        supportNode
        (mkOutcomeIndex total (Just mass) select valueAt (uniformSampler total valueAt) (Ranked.rankedPlan ranked))
        False
        (plainInspection supportNode)
        (RootCount 1)
  where
    supportNode = relabel Label root
    total = Ranked.cardinality ranked
    mass = 1 / toRational total
    valueAt = Ranked.rankedValueAt ranked
    select rank = do
        checkIndex total rank
        let term = valueAt rank
            labelled = fmap Label term
        pure $ Outcome labelled mass term (fmap plainSymbol labelled)

-- | The applicative product of a function language and an argument language.
applyStatic ::
    (Hashable symbol, Typeable symbol) =>
    Static symbol (a -> b) -> Static symbol a -> Static symbol b
applyStatic functions values =
    Static
        ( Node
            [ Edge
                Apply
                [staticSupport functions, staticSupport values]
            ]
        )
        ( mkOutcomeIndex
            totalOutcomes
            ((*) <$> outcomeUniformMass functionOutcomes <*> outcomeUniformMass valueOutcomes)
            select
            selectValue
            ( productSampler
                valueCardinality
                (outcomeSampler functionOutcomes)
                (outcomeSampler valueOutcomes)
            )
            ( PlanAp
                valueCardinality
                (outcomePlan functionOutcomes)
                (outcomePlan valueOutcomes)
            )
        )
            { outcomeSizeSampling = sizeSampling
            }
        False
        ( Inspection Nothing $
            Node
                [ Edge (plainSymbol Apply) [inspectionGraph $ staticInspection functions, inspectionGraph $ staticInspection values]
                ]
        )
        (addRootCounts (staticRootCount functions) (staticRootCount values))
  where
    functionOutcomes = staticOutcomes functions
    valueOutcomes = staticOutcomes values
    valueCardinality = outcomeCardinality valueOutcomes
    totalOutcomes = outcomeCardinality functionOutcomes * valueCardinality

    -- Each side samples its own size class, so an atomic side keeps its
    -- distribution inside every size of the product.
    (functionSampling, functionWeight) = staticSampling functions
    (valueSampling, valueWeight) = staticSampling values
    sizeSampling = case (functionWeight, valueWeight) of
        (Nothing, Nothing) -> Nothing
        _ ->
            Just
                ( productSampleIndex
                    (outcomeSizeIndex functionOutcomes)
                    functionSampling
                    (outcomeSizeIndex valueOutcomes)
                    valueSampling
                , \index ->
                    let (functionIndex, valueIndex) = splitIndex index
                     in (*)
                            <$> maybe (Right 1) ($ functionIndex) functionWeight
                            <*> maybe (Right 1) ($ valueIndex) valueWeight
                )

    select index = do
        checkIndex totalOutcomes index
        let (functionIndex, valueIndex) = splitIndex index
        functionOutcome <- outcomeSelect functionOutcomes functionIndex
        valueOutcome <- outcomeSelect valueOutcomes valueIndex
        pure $
            Outcome
                ( Tree.Node
                    Apply
                    [outcomeTerm functionOutcome, outcomeTerm valueOutcome]
                )
                (outcomeMass functionOutcome * outcomeMass valueOutcome)
                (outcomeValue functionOutcome $ outcomeValue valueOutcome)
                (Tree.Node (plainSymbol Apply) [outcomeInspection functionOutcome, outcomeInspection valueOutcome])

    selectValue index =
        let (functionIndex, valueIndex) = splitIndex index
         in outcomeValueAt functionOutcomes functionIndex $
                outcomeValueAt valueOutcomes valueIndex

    splitIndex = splitRank valueCardinality

-- | Concatenate weighted alternatives with stable rank offsets.
frequencyStatic ::
    (Hashable symbol, Typeable symbol) =>
    [(Weight, Static symbol a)] -> Static symbol a
frequencyStatic alternatives =
    Static
        ( Node
            [ Edge (Choice index) [staticSupport static]
            | (index, (_, static)) <- numbered
            ]
        )
        ( mkOutcomeIndex
            totalOutcomes
            uniformMass
            select
            selectValue
            sampler
            ( PlanChoice
                [ ( outcomeCardinality $ staticOutcomes static
                  , alternativePlan $ staticOutcomes static
                  )
                | (_, static) <- alternatives
                ]
            )
        )
            { outcomeSizeSampling = sizeSampling
            }
        False
        (choiceInspection $ map (staticInspection . snd) alternatives)
        (commonRootCount $ map (staticRootCount . snd) alternatives)
  where
    totalWeight = sum $ map fst alternatives
    numbered = zip [0 :: ChoiceIndex ..] alternatives
    rankedBranches =
        [ ( nextOffset offset $ outcomeCardinality (staticOutcomes static)
          , offset
          , branchIndex
          , weight
          , static
          )
        | (branchIndex, (offset, (weight, static))) <-
            zip [0 :: ChoiceIndex ..] $ offsetAlternatives alternatives
        ]
    totalOutcomes = sum [outcomeCardinality $ staticOutcomes static | (_, static) <- alternatives]
    uniformMass = commonValue $ map branchUniformMass alternatives
      where
        branchUniformMass (weight, static) =
            (toRational weight / toRational totalWeight *)
                <$> outcomeUniformMass (staticOutcomes static)
    sampler = case uniformMass of
        Just _ -> uniformSampler totalOutcomes selectValue
        Nothing -> frequencySampler alternatives

    -- Member counts choose the alternative inside a size class, as in a
    -- recursive choice. An atomic alternative keeps its own distribution.
    samplings = map (staticSampling . snd) alternatives
    sizeSampling
        | any (isJust . snd) samplings =
            Just
                ( choiceSampleIndex
                    [ (outcomeSizeIndex $ staticOutcomes static, sampling)
                    | ((sampling, _), (_, static)) <- zip samplings alternatives
                    ]
                , \index ->
                    let (_, _, static, childIndex) = selectBranch index rankedBranches
                     in maybe (Right 1) ($ childIndex) $ snd $ staticSampling static
                )
        | otherwise = Nothing

    select index = do
        checkIndex totalOutcomes index
        let (branchIndex, weight, static, childIndex) = selectBranch index rankedBranches
        child <- outcomeSelect (staticOutcomes static) childIndex
        pure $
            Outcome
                (Tree.Node (Choice branchIndex) [outcomeTerm child])
                ( toRational weight
                    / toRational totalWeight
                    * outcomeMass child
                )
                (outcomeValue child)
                (Tree.Node (plainSymbol $ Choice branchIndex) [outcomeInspection child])

    selectValue index =
        let (_, _, static, childIndex) = selectBranch index rankedBranches
         in outcomeValueAt (staticOutcomes static) childIndex

    selectBranch _ [] =
        error
            "microcfta-generator bug in Data.CFTA.Gen.Internal.Static.frequencyStatic: \
            \rank outside the alternatives"
    selectBranch index@(Rank rank) ((RankOffset upperBound, offset, branchIndex, weight, static) : remaining)
        | rank < upperBound = (branchIndex, weight, static, rebaseRank offset index)
        | otherwise = selectBranch index remaining

{- | The plan of one alternative of a choice.

An alternative with more than 'sharedChoiceBound' members is a shared node:
the choice calls its compiled decoder and reads its size classes, and does not
copy its plan. A plan that is shared already stays as it is, because a second
shared node would add one call to each decode.
-}
alternativePlan :: OutcomeIndex symbol a -> Plan a
alternativePlan outcomes = case outcomePlan outcomes of
    plan@PlanShared{} -> plan
    plan
        | outcomeCardinality outcomes > sharedChoiceBound ->
            PlanShared (outcomeCardinality outcomes) (outcomeDecoder outcomes) (outcomeSizeIndex outcomes) plan
        | otherwise -> plan

-- | Map the values of a static language.
mapStatic :: (a -> b) -> Static symbol a -> Static symbol b
mapStatic transform static =
    Static
        (staticSupport static)
        (mapOutcomeIndex transform $ staticOutcomes static)
        (staticAtomic static)
        (staticInspection static)
        (staticRootCount static)

-- | Map the values of an outcome index.
mapOutcomeIndex :: (a -> b) -> OutcomeIndex symbol a -> OutcomeIndex symbol b
mapOutcomeIndex transform outcomes =
    ( mkOutcomeIndex
        (outcomeCardinality outcomes)
        (outcomeUniformMass outcomes)
        (fmap (mapOutcome transform) . outcomeSelect outcomes)
        (transform . outcomeValueAt outcomes)
        (mapSampler transform $ outcomeSampler outcomes)
        (PlanMap transform $ outcomePlan outcomes)
    )
        { outcomeSizeSampling =
            Bifunctor.first (mapSampleIndex transform) <$> outcomeSizeSampling outcomes
        }

-- | Map the value of one outcome.
mapOutcome :: (a -> b) -> Outcome symbol a -> Outcome symbol b
mapOutcome transform outcome =
    Outcome
        (outcomeTerm outcome)
        (outcomeMass outcome)
        (transform $ outcomeValue outcome)
        (outcomeInspection outcome)

-- | Make every outcome of a finite language contribute one unit of size.
atomicStatic :: Static symbol a -> Static symbol a
atomicStatic static =
    static
        { staticOutcomes =
            mkOutcomeIndex
                (outcomeCardinality outcomes)
                (outcomeUniformMass outcomes)
                (outcomeSelect outcomes)
                (outcomeValueAt outcomes)
                retainedSampler
                (PlanSelect (outcomeCardinality outcomes) (outcomeValueAt outcomes))
        , staticAtomic = True
        }
  where
    outcomes = staticOutcomes static
    retainedSampler =
        case compiledWeightedSampler outcomes of
            Just sampler -> sampler
            Nothing -> outcomeSampler outcomes

{- | Close an applicative or grouped child layer with one user-facing node
label.

The generator engine uses private symbols while a child product is still open.
Closing it removes that scaffolding from the root term: applicative spines
become direct children, grouped joins retain their equality constraints, and
choice wrappers distribute the new label over their alternatives.
-}
labelStatic ::
    (Hashable symbol, Typeable symbol) =>
    symbol -> Static symbol a -> Static symbol a
labelStatic symbol static =
    static
        { staticSupport = labelSupport symbol $ staticSupport static
        , staticOutcomes = labelOutcomeTerms symbol $ staticOutcomes static
        , staticInspection = labelInspection symbol $ staticInspection static
        , staticRootCount = RootCount 1
        }

-- | Relabel the retained term of every outcome that the index selects.
labelOutcomeTerms :: symbol -> OutcomeIndex symbol a -> OutcomeIndex symbol a
labelOutcomeTerms symbol outcomes =
    outcomes
        { outcomeSelect = fmap (labelOutcome symbol) . outcomeSelect outcomes
        }

-- | Relabel the retained term of one finite outcome.
labelOutcome :: symbol -> Outcome symbol a -> Outcome symbol a
labelOutcome symbol outcome =
    outcome
        { outcomeTerm = labelTerm symbol $ outcomeTerm outcome
        , outcomeInspection = labelTermWith originalSymbol (plainSymbol $ Label symbol) $ outcomeInspection outcome
        }

-- | Sample one outcome sequence by its masses.
sequenceSampler :: Seq (Outcome symbol a) -> Either GenError (Sampler a)
sequenceSampler outcomes
    | Just _ <- commonValue $ Just . outcomeMass <$> toList outcomes =
        pure $ uniformSampler totalOutcomes selectValue
    | otherwise = do
        weightedRanks <-
            integerOutcomes
                [ (outcomeMass outcome, RankedValue index (outcomeValue outcome))
                | (index, outcome) <- zip [0 ..] $ toList outcomes
                ]
        pure $
            Sampler
                (frequencyGen [(weight, pure value) | (weight, RankedValue _ value) <- weightedRanks])
                (frequencyGen [(weight, pure ranked) | (weight, ranked) <- weightedRanks])
  where
    totalOutcomes = toEnum $ Sequence.length outcomes
    selectValue = outcomeValue . Sequence.index outcomes . fromEnum

-- | Sample weighted alternatives with rank offsets.
frequencySampler :: [(Weight, Static symbol a)] -> Sampler a
frequencySampler alternatives =
    Sampler
        ( frequencyGen
            [ (weight, runValueSampler $ outcomeSampler $ staticOutcomes static)
            | (weight, static) <- alternatives
            ]
        )
        ( frequencyGen
            [ (weight, offsetRankedValue offset <$> runRankSampler (outcomeSampler $ staticOutcomes static))
            | (offset, (weight, static)) <- offsetAlternatives alternatives
            ]
        )

-- | Pair every alternative with its cumulative rank offset.
offsetAlternatives :: [(Weight, Static symbol a)] -> [(RankOffset, (Weight, Static symbol a))]
offsetAlternatives = go 0
  where
    go _ [] = []
    go offset (alternative@(_, static) : remaining) =
        (offset, alternative)
            : go
                (nextOffset offset $ outcomeCardinality (staticOutcomes static))
                remaining

-- | Largest non-uniform language compiled to one exact ticket selection.
weightedCompilationBound :: Cardinality
weightedCompilationBound = 32768

-- | Compile a small non-uniform language without aggregating equal values.
compiledWeightedSampler :: OutcomeIndex symbol a -> Maybe (Sampler a)
compiledWeightedSampler outcomes
    | Just _ <- outcomeUniformMass outcomes = Nothing
    | outcomeCardinality outcomes > weightedCompilationBound = Nothing
    | otherwise = do
        enumerated <- either (const Nothing) Just $ enumerateOutcomeIndex outcomes
        weighted <-
            either (const Nothing) Just $
                integerOutcomes
                    [ (outcomeMass outcome, RankedValue rank (outcomeValue outcome))
                    | (rank, outcome) <- zip [0 ..] enumerated
                    ]
        compiled <- compileWeighted weighted
        pure $
            Sampler
                (rankedValue <$> selectWeighted weighted compiled)
                (selectWeighted weighted compiled)

-- | Sample one value; uniform languages go through the compiled decoder.
sampleStatic ::
    (GenBackend gen) =>
    Static symbol a ->
    gen (Either GenError a)
sampleStatic static
    | Just _ <- outcomeUniformMass outcomes =
        case outcomeDecoder outcomes of
            SmallDecoder bound decode -> Right . decode <$> selectInt bound
            LargeDecoder bound decode -> Right . decode <$> selectInteger bound
    | otherwise =
        Right <$> runValueSampler (outcomeSampler outcomes)
  where
    outcomes = staticOutcomes static

-- | Sample one value together with its replay rank.
sampleStaticWithRank ::
    (GenBackend gen) =>
    Static symbol a ->
    gen (Either GenError (RankedValue a))
sampleStaticWithRank static
    | Just _ <- outcomeUniformMass outcomes =
        case outcomeDecoder outcomes of
            SmallDecoder bound decode ->
                (\index -> Right $ RankedValue (Rank $ toInteger index) (decode index)) <$> selectInt bound
            LargeDecoder bound decode ->
                (\rank -> Right $ RankedValue rank (decode rank)) <$> selectInteger bound
    | otherwise =
        Right <$> runRankSampler (outcomeSampler outcomes)
  where
    outcomes = staticOutcomes static

-- | Select every outcome in rank order.
enumerateOutcomeIndex :: OutcomeIndex symbol a -> Either GenError [Outcome symbol a]
enumerateOutcomeIndex outcomes =
    traverse
        (outcomeSelect outcomes)
        (everyRank $ outcomeCardinality outcomes)

{- | Select every outcome in rank order, with the weight of its rank inside
its size class.

'outcomeSizeSampling' describes the weight. Every outcome of a language with
uniform size classes has the weight one.
-}
enumerateWeighted :: Static symbol a -> Either GenError [(Rational, Outcome symbol a)]
enumerateWeighted static = do
    outcomes <- enumerateOutcomeIndex $ staticOutcomes static
    weights <-
        traverse
            (fromMaybe (const $ Right 1) $ snd $ staticSampling static)
            (everyRank $ toEnum $ length outcomes)
    pure $ zip weights outcomes

-- | Enumerate a language as normalized mass and value pairs.
compileOutcomes :: Static symbol a -> Either GenError [(Rational, a)]
compileOutcomes static = do
    outcomes <- enumerateOutcomeIndex $ staticOutcomes static
    normalize [(outcomeMass outcome, outcomeValue outcome) | outcome <- outcomes]

-- | The number of user roots of an engine term: the length of 'surface' of the term.
termRootCount :: Tree.Tree (Label symbol) -> Int
termRootCount (Tree.Node (Label _) _) = 1
termRootCount (Tree.Node _ children) = sum $ map termRootCount children

{- | The number of user roots that each member of a language gives its
constructor, or 'NoCommonCount'. 'NoCommonCount' is for a language whose
members give different numbers, and for a language that does not know the
number: a bounded recursive language without a term index, and, in the
refinement compiler, a recursive or opaque built language. Each reader
treats the two cases the same.
-}
data RootCount
    = NoCommonCount
    | RootCount !Int
    deriving (Eq, Show)

-- | The root count of a product: the sum of the root counts of its two parts.
addRootCounts :: RootCount -> RootCount -> RootCount
addRootCounts (RootCount left) (RootCount right) = RootCount $ left + right
addRootCounts _ _ = NoCommonCount

{- | The root count that every part gives, when the parts agree. A list
without parts gives one, so that a language without members does not refuse
a guard that reads its children.
-}
commonRootCount :: [RootCount] -> RootCount
commonRootCount counts = case counts of
    [] -> RootCount 1
    count : rest | all (== count) rest -> count
    _ -> NoCommonCount

-- | The value shared by every entry, if any.
commonValue :: (Eq a) => [Maybe a] -> Maybe a
commonValue [] = Nothing
commonValue (Just value : remaining)
    | all (== Just value) remaining = Just value
commonValue _ = Nothing

-- | Reject a rank outside the language.
checkIndex :: Cardinality -> Rank -> Either GenError ()
checkIndex totalOutcomes@(Cardinality total) index@(Rank rank)
    | rank < 0 = Left $ NegativeRank index
    | rank >= total = Left $ SelectionOutOfRange index totalOutcomes
    | otherwise = Right ()

-- | Scale masses so they sum to one.
normalize :: [(Rational, a)] -> Either GenError [(Rational, a)]
normalize [] = Left EmptyGenerator
normalize outcomes =
    let total = sum $ map fst outcomes
     in if total <= 0
            then Left EmptyGenerator
            else Right [(mass / total, value) | (mass, value) <- outcomes]

{- | Convert rational masses to the smallest equivalent integer weights,
rejecting a set that cannot be sampled.

This is 'integerMasses' with its positivity precondition checked: a language
with no outcomes, or one whose masses are not all positive, has nothing to
sample.
-}
integerOutcomes ::
    [(Rational, a)] ->
    Either GenError [(Weight, a)]
integerOutcomes [] = Left EmptyGenerator
integerOutcomes outcomes
    | any ((<= 0) . fst) outcomes = Left EmptyGenerator
    | otherwise = Right $ integerMasses outcomes
