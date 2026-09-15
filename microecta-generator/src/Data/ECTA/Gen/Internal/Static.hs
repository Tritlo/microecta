{- | Finite languages and the builders that compose them.

A t'Static' is an ECTA support paired with an t'OutcomeIndex' that counts,
selects, decodes, and samples outcomes by rank. Every finite combinator of
"Data.ECTA.Gen" is one function here. The sampling engine itself lives in
"Data.Tree.Gen.Internal.Sampler".
-}
module Data.ECTA.Gen.Internal.Static (
    -- * Languages
    Outcome (..),
    OutcomeIndex (..),
    mkOutcomeIndex,
    seqPlan,
    Static (..),

    -- * Building languages
    pureStatic,
    indexedStatic,
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

import Data.Foldable (toList)
import Data.Sequence (Seq)
import qualified Data.Sequence as Sequence

import Data.ECTA (Edge (Edge), Node (Node))
import Data.ECTA.Gen.Internal.Error (ECTAGenError (..))
import Data.ECTA.Gen.Internal.Support (
    applySymbol,
    frequencySymbol,
    indexedSymbol,
    labelSupport,
    labelTerm,
    pureSymbol,
 )
import Data.ECTA.Term (Symbol, Term (Term))
import Data.Tree.Gen.Internal (Indexed (..))
import qualified Data.Tree.Gen.Internal as Ranked
import Data.Tree.Gen.Internal.Decoder (
    Plan (..),
    RankDecoder (..),
    compilePlan,
 )
import Data.Tree.Gen.Internal.Sampler
import Data.Tree.Gen.Internal.Size (SizeIndex, sizeIndex)

-- | One term, its normalized probability mass, and its decoded value.
data Outcome a = Outcome
    { outcomeTerm :: Term Symbol
    , outcomeMass :: Rational
    , outcomeValue :: a
    }

-- | A finite language with exact cardinality and rank-based selection.
data OutcomeIndex a = OutcomeIndex
    { outcomeCardinality :: !Integer
    , outcomeUniformMass :: !(Maybe Rational)
    , outcomeSelect :: Integer -> Either ECTAGenError (Outcome a)
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
    (Integer -> Either ECTAGenError (Outcome a)) ->
    (Integer -> a) ->
    Sampler a ->
    Plan a ->
    OutcomeIndex a
mkOutcomeIndex total mass select valueAt sampler plan =
    OutcomeIndex total mass select valueAt sampler plan (sizeIndex plan)

-- | Decode positions of one enumerated outcome sequence.
seqPlan :: Seq (Outcome a) -> Plan a
seqPlan outcomes =
    PlanSelect
        (toInteger $ Sequence.length outcomes)
        (outcomeValue . Sequence.index outcomes . fromInteger)

-- | One transparent ECTA with a matching indexed outcome language.
data Static a = Static
    { staticSupport :: Node Symbol
    {- ^ The ECTA support is demand-driven. Counting, mass, and sampling
    use the outcome index without forcing this field. A support observer builds
    it when needed; finite combinators retain their support work as a thunk.
    -}
    , staticOutcomes :: !(OutcomeIndex a)
    , staticAtomic :: !Bool
    {- ^ Whether an explicit atomic boundary closes this finite language.

    Ordinary finite weights do not control recursive structure. 'atomicStatic'
    sets this marker so 'recursiveFromStatic' can preserve them as one source
    choice. The sampler itself already lives in 'staticOutcomes'.
    -}
    }

-- | The one-outcome language of a single value.
pureStatic :: a -> Static a
pureStatic value =
    Static
        (Node [Edge pureSymbol []])
        ( mkOutcomeIndex
            1
            (Just 1)
            ( \index -> do
                checkIndex 1 index
                pure $ Outcome (Term pureSymbol []) 1 value
            )
            (\_ -> value)
            (uniformSampler 1 $ const value)
            (PlanSelect 1 $ const value)
        )
        False

-- | The language of one finite indexed source.
indexedStatic :: Indexed a -> Static a
indexedStatic indexed =
    Static
        (Node [Edge (indexedSymbol index) [] | index <- [0 .. totalOutcomes - 1]])
        ( mkOutcomeIndex
            totalOutcomes
            (Just $ 1 / fromInteger totalOutcomes)
            select
            (indexedSelect indexed)
            (uniformSampler totalOutcomes $ indexedSelect indexed)
            (PlanSelect totalOutcomes $ indexedSelect indexed)
        )
        False
  where
    totalOutcomes = indexedCardinality indexed
    select index = do
        checkIndex totalOutcomes index
        pure $
            Outcome
                (Term (indexedSymbol index) [])
                (1 / fromInteger totalOutcomes)
                (indexedSelect indexed index)

{- | Retain a shared ranked term compiler and its exact equality support.

Sampling is uniform over accepted terms. The common plan supplies replay and
structural shrinking. No term is decoded while this adapter is constructed.
-}
termStatic :: Node Symbol -> Ranked.Ranked (Term Symbol) -> Static (Term Symbol)
termStatic supportNode ranked =
    Static
        supportNode
        (mkOutcomeIndex total (Just mass) select valueAt (uniformSampler total valueAt) (Ranked.rankedPlan ranked))
        False
  where
    total = Ranked.cardinality ranked
    mass = 1 / fromInteger total
    valueAt = Ranked.rankedValueAt ranked
    select rank = do
        checkIndex total rank
        let term = valueAt rank
        pure $ Outcome term mass term

-- | The applicative product of a function language and an argument language.
applyStatic :: Static (a -> b) -> Static a -> Static b
applyStatic functions values =
    Static
        ( Node
            [ Edge
                applySymbol
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
                ( Term
                    applySymbol
                    [outcomeTerm functionOutcome, outcomeTerm valueOutcome]
                )
                (outcomeMass functionOutcome * outcomeMass valueOutcome)
                (outcomeValue functionOutcome $ outcomeValue valueOutcome)

    selectValue index =
        let (functionIndex, valueIndex) = splitIndex index
         in outcomeValueAt functionOutcomes functionIndex $
                outcomeValueAt valueOutcomes valueIndex

    splitIndex index = index `quotRem` valueCardinality

-- | Concatenate weighted alternatives with stable rank offsets.
frequencyStatic :: [(Integer, Static a)] -> Static a
frequencyStatic alternatives =
    Static
        ( Node
            [ Edge (frequencySymbol index) [staticSupport static]
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
                (Term (frequencySymbol branchIndex) [outcomeTerm child])
                ( fromInteger weight
                    / fromInteger totalWeight
                    * outcomeMass child
                )
                (outcomeValue child)

    selectValue index =
        let (_, _, static, childIndex) = selectBranch index rankedBranches
         in outcomeValueAt (staticOutcomes static) childIndex

    selectBranch _ [] =
        error
            "microecta-generator bug in Data.ECTA.Gen.Internal.Static.frequencyStatic: \
            \rank outside the alternatives"
    selectBranch index ((upperBound, offset, branchIndex, weight, static) : remaining)
        | index < upperBound = (branchIndex, weight, static, index - offset)
        | otherwise = selectBranch index remaining

-- | Map the values of a static language.
mapStatic :: (a -> b) -> Static a -> Static b
mapStatic transform static =
    Static
        (staticSupport static)
        (mapOutcomeIndex transform $ staticOutcomes static)
        (staticAtomic static)

-- | Map the values of an outcome index.
mapOutcomeIndex :: (a -> b) -> OutcomeIndex a -> OutcomeIndex b
mapOutcomeIndex transform outcomes =
    mkOutcomeIndex
        (outcomeCardinality outcomes)
        (outcomeUniformMass outcomes)
        (\index -> mapOutcome transform <$> outcomeSelect outcomes index)
        (transform . outcomeValueAt outcomes)
        (mapSampler transform $ outcomeSampler outcomes)
        (PlanMap transform $ outcomePlan outcomes)

-- | Map the value of one outcome.
mapOutcome :: (a -> b) -> Outcome a -> Outcome b
mapOutcome transform outcome =
    Outcome
        (outcomeTerm outcome)
        (outcomeMass outcome)
        (transform $ outcomeValue outcome)

-- | Make every outcome of a finite language contribute one unit of size.
atomicStatic :: Static a -> Static a
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
labelStatic :: Symbol -> Static a -> Static a
labelStatic symbol static =
    static
        { staticSupport = labelSupport symbol $ staticSupport static
        , staticOutcomes = labelOutcomeTerms symbol $ staticOutcomes static
        }

labelOutcomeTerms :: Symbol -> OutcomeIndex a -> OutcomeIndex a
labelOutcomeTerms symbol outcomes =
    outcomes
        { outcomeSelect = \index -> labelOutcome symbol <$> outcomeSelect outcomes index
        }

-- | Relabel the retained term of one finite outcome.
labelOutcome :: Symbol -> Outcome a -> Outcome a
labelOutcome symbol outcome =
    outcome{outcomeTerm = labelTerm symbol $ outcomeTerm outcome}

-- | Sample one outcome sequence by its masses.
sequenceSampler :: Seq (Outcome a) -> Either ECTAGenError (Sampler a)
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
frequencySampler :: [(Integer, Static a)] -> Sampler a
frequencySampler alternatives =
    Sampler
        ( frequencyGen
            [ (weight, runValueSampler $ outcomeSampler $ staticOutcomes static)
            | (weight, static) <- alternatives
            ]
        )
        ( frequencyGen
            [ ( weight
              , (\(rank, value) -> (offset + rank, value))
                    <$> runRankSampler (outcomeSampler $ staticOutcomes static)
              )
            | (offset, (weight, static)) <- offsetAlternatives alternatives
            ]
        )

-- | Pair every alternative with its cumulative rank offset.
offsetAlternatives :: [(Integer, Static a)] -> [(Integer, (Integer, Static a))]
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
compiledWeightedSampler :: OutcomeIndex a -> Maybe (Sampler a)
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
compiledDecoder :: OutcomeIndex a -> RankDecoder a
compiledDecoder outcomes =
    compilePlan (outcomeCardinality outcomes) (outcomePlan outcomes)

-- | Sample one value; uniform languages go through the compiled decoder.
sampleStatic ::
    (GenBackend gen) =>
    Static a ->
    gen (Either ECTAGenError a)
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
    Static a ->
    gen (Either ECTAGenError (Integer, a))
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
enumerateOutcomeIndex :: OutcomeIndex a -> Either ECTAGenError [Outcome a]
enumerateOutcomeIndex outcomes =
    traverse
        (outcomeSelect outcomes)
        [0 .. outcomeCardinality outcomes - 1]

-- | Enumerate a language as normalized mass and value pairs.
compileOutcomes :: Static a -> Either ECTAGenError [(Rational, a)]
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
checkIndex :: Integer -> Integer -> Either ECTAGenError ()
checkIndex totalOutcomes index
    | index < 0 = Left $ NegativeRank index
    | index >= totalOutcomes =
        Left $ SelectionOutOfRange index totalOutcomes
    | otherwise = Right ()

-- | Scale masses so they sum to one.
normalize :: [(Rational, a)] -> Either ECTAGenError [(Rational, a)]
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
    Either ECTAGenError [(Integer, a)]
integerOutcomes [] = Left EmptyGenerator
integerOutcomes outcomes
    | any ((<= 0) . fst) outcomes = Left EmptyGenerator
    | otherwise = Right $ integerMasses outcomes
