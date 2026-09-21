{- | Finite languages and the builders that compose them.

A t'Static' is an ECTA support paired with an t'OutcomeIndex' that counts,
selects, decodes, and samples outcomes by rank. Every finite combinator of
"Data.CFTA.Gen.Equality" is one function here. The sampling engine itself lives in
"Data.CFTA.Ranked.Internal.Sampler".
-}
module Data.CFTA.Gen.Equality.Internal.Static (
    -- * Languages
    Outcome (..),
    OutcomeIndex (..),
    mkOutcomeIndex,
    seqPlan,
    Static (..),

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
    compiledDecoder,
    sampleStatic,
    sampleStaticWithRank,

    -- * Inspection
    enumerateOutcomeIndex,
    compileOutcomes,
    commonValue,
    checkIndex,
    normalize,
    integerOutcomes,
) where

import qualified Data.Bifunctor as Bifunctor
import Data.Foldable (toList)
import Data.Hashable (Hashable)
import Data.Sequence (Seq)
import qualified Data.Sequence as Sequence
import Data.Text (Text)
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import Data.CFTA.Equality (Edge (Edge), Node (Node))
import Data.CFTA.Equality.Constraint (EqConstraints)
import Data.CFTA.Gen.Equality.Internal.Inspection
import Data.CFTA.Gen.Equality.Internal.Support (labelSupport, labelTerm, labelTermWith, relabel)
import Data.CFTA.Gen.Error (GenError (..))
import Data.CFTA.Gen.Label (Label (..))
import Data.CFTA.Ranked.Internal (Indexed (..))
import qualified Data.CFTA.Ranked.Internal as Ranked
import Data.CFTA.Ranked.Internal.Decoder (
    Plan (..),
    RankDecoder (..),
    compilePlan,
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
    { outcomeCardinality :: !Integer
    , outcomeUniformMass :: !(Maybe Rational)
    , outcomeSelect :: Integer -> Either GenError (Outcome symbol a)
    , outcomeValueAt :: Integer -> a
    , outcomeSampler :: Sampler a
    {- ^ The compositional sampler is demand-driven. Uniform lowering uses the
    compiled rank plan instead, while weighted and atomic paths force this
    fallback once when they need it.
    -}
    , outcomePlan :: Plan a
    , outcomeSizeIndex :: SizeIndex a
    {- ^ The size classes of 'outcomePlan', built on first use and retained so
    a shrink loop pays for them once. Construct through 'mkOutcomeIndex'.
    -}
    }

-- | Build an outcome index whose size classes are derived from its plan.
mkOutcomeIndex ::
    Integer ->
    Maybe Rational ->
    (Integer -> Either GenError (Outcome symbol a)) ->
    (Integer -> a) ->
    Sampler a ->
    Plan a ->
    OutcomeIndex symbol a
mkOutcomeIndex total mass select valueAt sampler plan =
    OutcomeIndex total mass select valueAt sampler plan (sizeIndex plan)

-- | Decode positions of one enumerated outcome sequence.
seqPlan :: Seq (Outcome symbol a) -> Plan a
seqPlan outcomes =
    PlanSelect
        (toInteger $ Sequence.length outcomes)
        (outcomeValue . Sequence.index outcomes . fromInteger)

-- | One transparent ECTA with a matching indexed outcome language.
data Static symbol a = Static
    { staticSupport :: Node (Label symbol) EqConstraints
    {- ^ The ECTA support is demand-driven. Counting, mass, and sampling
    use the outcome index without forcing this field. A support observer builds
    it when needed; finite combinators retain their support work as a thunk.
    -}
    , staticOutcomes :: !(OutcomeIndex symbol a)
    , staticAtomic :: !Bool
    {- ^ Whether an explicit atomic boundary closes this finite language.

    Ordinary finite weights do not control recursive structure. 'atomicStatic'
    sets this marker so 'recursiveFromStatic' can preserve them as one source
    choice. The sampler itself already lives in 'staticOutcomes'.
    -}
    , staticInspection :: Inspection symbol
    -- ^ Diagnostic structure. Counting and decoding do not force this field.
    }

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

-- | The language of one finite indexed source.
indexedStatic :: (Hashable symbol, Typeable symbol) => Indexed a -> Static symbol a
indexedStatic = indexedStaticWithLabels $ const Nothing

-- | Retain source names independently of values and rank decoding.
indexedStaticWithLabels ::
    (Hashable symbol, Typeable symbol) => (Integer -> Maybe Text) -> Indexed a -> Static symbol a
indexedStaticWithLabels label indexed =
    Static
        (Node [Edge (Index index) [] | index <- [0 .. totalOutcomes - 1]])
        ( mkOutcomeIndex
            totalOutcomes
            (Just $ 1 / fromInteger totalOutcomes)
            select
            (indexedSelect indexed)
            (uniformSampler totalOutcomes $ indexedSelect indexed)
            (PlanSelect totalOutcomes $ indexedSelect indexed)
        )
        False
        (Inspection Nothing $ Node [Edge (namedSymbol index) [] | index <- [0 .. totalOutcomes - 1]])
  where
    namedSymbol index = InspectionSymbol (Index index) (label index)
    totalOutcomes = indexedCardinality indexed
    select index = do
        checkIndex totalOutcomes index
        pure $
            Outcome
                (Tree.Node (Index index) [])
                (1 / fromInteger totalOutcomes)
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
    Node symbol EqConstraints -> Ranked.Ranked (Tree.Tree symbol) -> Static symbol (Tree.Tree symbol)
termStatic root ranked =
    Static
        supportNode
        (mkOutcomeIndex total (Just mass) select valueAt (uniformSampler total valueAt) (Ranked.rankedPlan ranked))
        False
        (plainInspection supportNode)
  where
    supportNode = relabel Label root
    total = Ranked.cardinality ranked
    mass = 1 / fromInteger total
    valueAt = Ranked.rankedValueAt ranked
    select rank = do
        checkIndex total rank
        let term = valueAt rank
            labelled = fmap Label term
        pure $ Outcome labelled mass term (fmap plainSymbol labelled)

-- | The applicative product of a function language and an argument language.
applyStatic :: (Hashable symbol, Typeable symbol) => Static symbol (a -> b) -> Static symbol a -> Static symbol b
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
        False
        ( Inspection Nothing $
            Node
                [ Edge (plainSymbol Apply) [inspectionGraph $ staticInspection functions, inspectionGraph $ staticInspection values]
                ]
        )
  where
    functionOutcomes = staticOutcomes functions
    valueOutcomes = staticOutcomes values
    valueCardinality = outcomeCardinality valueOutcomes
    totalOutcomes = outcomeCardinality functionOutcomes * valueCardinality

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

    splitIndex index = index `quotRem` valueCardinality

-- | Concatenate weighted alternatives with stable rank offsets.
frequencyStatic :: (Hashable symbol, Typeable symbol) => [(Integer, Static symbol a)] -> Static symbol a
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
                  , outcomePlan $ staticOutcomes static
                  )
                | (_, static) <- alternatives
                ]
            )
        )
        False
        (choiceInspection $ map (staticInspection . snd) alternatives)
  where
    totalWeight = sum $ map fst alternatives
    numbered = zip [0 :: Int ..] alternatives
    rankedBranches =
        [ ( offset + outcomeCardinality (staticOutcomes static)
          , offset
          , branchIndex
          , weight
          , static
          )
        | (branchIndex, (offset, (weight, static))) <-
            zip [0 :: Int ..] $ offsetAlternatives alternatives
        ]
    totalOutcomes = sum [outcomeCardinality $ staticOutcomes static | (_, static) <- alternatives]
    uniformMass = commonValue $ map branchUniformMass alternatives
    sampler = case uniformMass of
        Just _ -> uniformSampler totalOutcomes selectValue
        Nothing -> frequencySampler alternatives

    branchUniformMass (weight, static) =
        (fromInteger weight / fromInteger totalWeight *)
            <$> outcomeUniformMass (staticOutcomes static)

    select index = do
        checkIndex totalOutcomes index
        let (branchIndex, weight, static, childIndex) = selectBranch index rankedBranches
        child <- outcomeSelect (staticOutcomes static) childIndex
        pure $
            Outcome
                (Tree.Node (Choice branchIndex) [outcomeTerm child])
                ( fromInteger weight
                    / fromInteger totalWeight
                    * outcomeMass child
                )
                (outcomeValue child)
                (Tree.Node (plainSymbol $ Choice branchIndex) [outcomeInspection child])

    selectValue index =
        let (_, _, static, childIndex) = selectBranch index rankedBranches
         in outcomeValueAt (staticOutcomes static) childIndex

    selectBranch _ [] =
        error
            "microcfta-generator bug in Data.CFTA.Gen.Equality.Internal.Static.frequencyStatic: \
            \rank outside the alternatives"
    selectBranch index ((upperBound, offset, branchIndex, weight, static) : remaining)
        | index < upperBound = (branchIndex, weight, static, index - offset)
        | otherwise = selectBranch index remaining

-- | Map the values of a static language.
mapStatic :: (a -> b) -> Static symbol a -> Static symbol b
mapStatic transform static =
    Static
        (staticSupport static)
        (mapOutcomeIndex transform $ staticOutcomes static)
        (staticAtomic static)
        (staticInspection static)

-- | Map the values of an outcome index.
mapOutcomeIndex :: (a -> b) -> OutcomeIndex symbol a -> OutcomeIndex symbol b
mapOutcomeIndex transform outcomes =
    mkOutcomeIndex
        (outcomeCardinality outcomes)
        (outcomeUniformMass outcomes)
        (fmap (mapOutcome transform) . outcomeSelect outcomes)
        (transform . outcomeValueAt outcomes)
        (mapSampler transform $ outcomeSampler outcomes)
        (PlanMap transform $ outcomePlan outcomes)

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
labelStatic :: (Hashable symbol, Typeable symbol) => symbol -> Static symbol a -> Static symbol a
labelStatic symbol static =
    static
        { staticSupport = labelSupport symbol $ staticSupport static
        , staticOutcomes = labelOutcomeTerms symbol $ staticOutcomes static
        , staticInspection = labelInspection symbol $ staticInspection static
        }

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
                [ (outcomeMass outcome, (index, outcomeValue outcome))
                | (index, outcome) <- zip [0 ..] $ toList outcomes
                ]
        pure $
            Sampler
                (frequencyGen [(weight, pure value) | (weight, (_, value)) <- weightedRanks])
                (frequencyGen [(weight, pure rankedValue) | (weight, rankedValue) <- weightedRanks])
  where
    totalOutcomes = toInteger $ Sequence.length outcomes
    selectValue = outcomeValue . Sequence.index outcomes . fromInteger

-- | Sample weighted alternatives with rank offsets.
frequencySampler :: [(Integer, Static symbol a)] -> Sampler a
frequencySampler alternatives =
    Sampler
        ( frequencyGen
            [ (weight, runValueSampler $ outcomeSampler $ staticOutcomes static)
            | (weight, static) <- alternatives
            ]
        )
        ( frequencyGen
            [ ( weight
              , (Bifunctor.first (offset +))
                    <$> runRankSampler (outcomeSampler $ staticOutcomes static)
              )
            | (offset, (weight, static)) <- offsetAlternatives alternatives
            ]
        )

-- | Pair every alternative with its cumulative rank offset.
offsetAlternatives :: [(Integer, Static symbol a)] -> [(Integer, (Integer, Static symbol a))]
offsetAlternatives = go 0
  where
    go _ [] = []
    go offset (alternative@(_, static) : remaining) =
        (offset, alternative)
            : go
                (offset + outcomeCardinality (staticOutcomes static))
                remaining

-- | Largest non-uniform language compiled to one exact ticket selection.
weightedCompilationBound :: Integer
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
                    [ (outcomeMass outcome, (rank, outcomeValue outcome))
                    | (rank, outcome) <- zip [0 ..] enumerated
                    ]
        (bound, decode) <- compileWeighted weighted
        pure $
            Sampler
                (snd . decode <$> selectInt bound)
                (decode <$> selectInt bound)

-- | Compile the retained plan once, at lowering time.
compiledDecoder :: OutcomeIndex symbol a -> RankDecoder a
compiledDecoder outcomes =
    compilePlan (outcomeCardinality outcomes) (outcomePlan outcomes)

-- | Sample one value; uniform languages go through the compiled decoder.
sampleStatic ::
    (GenBackend gen) =>
    Static symbol a ->
    gen (Either GenError a)
sampleStatic static
    | Just _ <- outcomeUniformMass outcomes =
        case compiledDecoder outcomes of
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
    gen (Either GenError (Integer, a))
sampleStaticWithRank static
    | Just _ <- outcomeUniformMass outcomes =
        case compiledDecoder outcomes of
            SmallDecoder bound decode ->
                (\index -> Right (toInteger index, decode index)) <$> selectInt bound
            LargeDecoder bound decode ->
                (\index -> Right (index, decode index)) <$> selectInteger bound
    | otherwise =
        Right <$> runRankSampler (outcomeSampler outcomes)
  where
    outcomes = staticOutcomes static

-- | Select every outcome in rank order.
enumerateOutcomeIndex :: OutcomeIndex symbol a -> Either GenError [Outcome symbol a]
enumerateOutcomeIndex outcomes =
    traverse
        (outcomeSelect outcomes)
        [0 .. outcomeCardinality outcomes - 1]

-- | Enumerate a language as normalized mass and value pairs.
compileOutcomes :: Static symbol a -> Either GenError [(Rational, a)]
compileOutcomes static = do
    outcomes <- enumerateOutcomeIndex $ staticOutcomes static
    normalize [(outcomeMass outcome, outcomeValue outcome) | outcome <- outcomes]

-- | The value shared by every entry, if any.
commonValue :: (Eq a) => [Maybe a] -> Maybe a
commonValue [] = Nothing
commonValue (Just value : remaining)
    | all (== Just value) remaining = Just value
commonValue _ = Nothing

-- | Reject a rank outside the language.
checkIndex :: Integer -> Integer -> Either GenError ()
checkIndex totalOutcomes index
    | index < 0 = Left $ NegativeRank index
    | index >= totalOutcomes =
        Left $ SelectionOutOfRange index totalOutcomes
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
    Either GenError [(Integer, a)]
integerOutcomes [] = Left EmptyGenerator
integerOutcomes outcomes
    | any ((<= 0) . fst) outcomes = Left EmptyGenerator
    | otherwise = Right $ integerMasses outcomes
