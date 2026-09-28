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
    TermView (..),
    mkOutcomeIndex,
    leafRanks,
    enumeratedRanks,
    seqPlan,
    Static (..),
    staticSampling,

    -- * Building languages
    pureStatic,
    indexedStatic,
    indexedStaticWithLabels,
    pointsStatic,
    holeStatic,
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
import Data.CFTA.Gen.Internal.Support (labelSupport, labelTerm, labelTermWith, labelledChildren, relabel, spineChildren)
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
    , outcomeRanks :: TermView symbol -> [Integer]
    {- ^ The ranks whose term has the given view, in ascending order. The
    inverse of 'outcomeSelect' on terms: one term can have several ranks,
    because a node label removes the choice wrapper of its alternatives.
    -}
    , outcomeValueAt :: Integer -> a
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
    , outcomeSizeSampling :: Maybe (SampleIndex a, Integer -> Either GenError Rational)
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
    Integer ->
    Maybe Rational ->
    (Integer -> Either GenError (Outcome symbol a)) ->
    (TermView symbol -> [Integer]) ->
    (Integer -> a) ->
    Sampler a ->
    Plan a ->
    OutcomeIndex symbol a
mkOutcomeIndex total mass select ranks valueAt sampler plan =
    OutcomeIndex total mass select ranks valueAt sampler plan (sizeIndex plan) (compilePlan total plan) Nothing

{- | A term as a language reads it when it ranks the term.

A language reads its own terms whole. The function side of an applicative
spine reads the arguments that the spine gives it, and a closed constructor
reads the children that 'labelTerm' gives its term: 'labelTerm' removes the
private labels of a spine, of an n-way join, and of a choice. The engine terms
carry these private labels, so ranking follows them and does not compare the
user symbols of the terms.
-}
data TermView symbol
    = -- | The whole term.
      WholeTerm (Tree.Tree (Label symbol))
    | -- | The arguments of an applicative spine on its function side.
      SpineView [Tree.Tree (Label symbol)]
    | -- | The children under a node label.
      LabelledView [Tree.Tree (Label symbol)]

{- | The ranks of a view, for a language whose terms have no private label at
their root: each view of such a term is the term itself.
-}
leafRanks :: (Tree.Tree (Label symbol) -> [Integer]) -> TermView symbol -> [Integer]
leafRanks ranksOfTerm view = case view of
    WholeTerm term -> ranksOfTerm term
    SpineView [term] -> ranksOfTerm term
    LabelledView [term] -> ranksOfTerm term
    _ -> []

{- | The ranks of a view for a language whose terms are listed in rank order.
This compares whole terms, so use it only where the terms came from the same
generator.
-}
enumeratedRanks :: (Eq symbol) => [Tree.Tree (Label symbol)] -> TermView symbol -> [Integer]
enumeratedRanks terms view = [rank | (rank, term) <- zip [0 ..] terms, matches term]
  where
    matches term = case view of
        WholeTerm wanted -> term == wanted
        SpineView wanted -> spineChildren term == wanted
        LabelledView wanted -> labelledChildren term == wanted

-- | Decode positions of one enumerated outcome sequence.
seqPlan :: Seq (Outcome symbol a) -> Plan a
seqPlan outcomes =
    PlanSelect
        (toInteger $ Sequence.length outcomes)
        (outcomeValue . Sequence.index outcomes . fromInteger)

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
    }

{- | The sampler of each size class of a finite language, and the weight of
each rank inside its size class when that sampler is not uniform.

Inside a size class, the ordinary finite weights of the language become
member counts. An atomic choice keeps its own distribution, also when it is
a component of a product or of a choice. 'outcomeSizeSampling' describes the
weight. The weight of an atomic choice comes from its exact outcome masses.
-}
staticSampling :: Static symbol a -> (SampleIndex a, Maybe (Integer -> Either GenError Rational))
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
        (* fromInteger (outcomeCardinality outcomes)) . outcomeMass
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
            pureRanks
            (const value)
            (uniformSampler 1 $ const value)
            (PlanSelect 1 $ const value)
        )
        False
        (Inspection Nothing $ Node [Edge (plainSymbol Pure) []])
  where
    -- A spine and a node label give pure no arguments.
    pureRanks view = case view of
        WholeTerm (Tree.Node Pure []) -> [0]
        SpineView [] -> [0]
        LabelledView [] -> [0]
        _ -> []

-- | The language of one finite indexed source.
indexedStatic :: (Hashable symbol, Typeable symbol) => Indexed a -> Static symbol a
indexedStatic = indexedStaticWithLabels $ const Nothing

-- | Retain source names independently of values and rank decoding.
indexedStaticWithLabels ::
    (Hashable symbol, Typeable symbol) =>
    (Integer -> Maybe Text) -> Indexed a -> Static symbol a
indexedStaticWithLabels label indexed =
    Static
        (Node [Edge (Index index) [] | index <- [0 .. totalOutcomes - 1]])
        ( mkOutcomeIndex
            totalOutcomes
            (Just $ 1 / fromInteger totalOutcomes)
            select
            (leafRanks indexRanks)
            (indexedSelect indexed)
            (uniformSampler totalOutcomes $ indexedSelect indexed)
            (PlanSelect totalOutcomes $ indexedSelect indexed)
        )
        False
        (Inspection Nothing $ Node [Edge (namedSymbol index) [] | index <- [0 .. totalOutcomes - 1]])
  where
    namedSymbol index = InspectionSymbol (Index index) (label index)
    totalOutcomes = indexedCardinality indexed
    indexRanks term = case term of
        Tree.Node (Index index) [] | index >= 0 && index < totalOutcomes -> [index]
        _ -> []
    select index = do
        checkIndex totalOutcomes index
        pure $
            Outcome
                (Tree.Node (Index index) [])
                (1 / fromInteger totalOutcomes)
                (indexedSelect indexed index)
                (Tree.Node (namedSymbol index) [])

{- | The language of one placeholder leaf with one value.

Its term is a private 'Placeholder', which a theory fills when it compiles. The
support is one leaf with the given symbol, which describes the values that
can fill the placeholder.
-}
holeStatic :: (Hashable symbol, Typeable symbol) => symbol -> a -> Static symbol a
holeStatic summary value =
    Static
        (Node [Edge (Label summary) []])
        ( mkOutcomeIndex
            1
            (Just 1)
            ( \index -> do
                checkIndex 1 index
                pure $ Outcome (Tree.Node Placeholder []) 1 value (Tree.Node (plainSymbol Placeholder) [])
            )
            -- A theory fills the placeholder with a leaf, so any leaf takes rank zero.
            (leafRanks $ \term -> [0 | null $ Tree.subForest term])
            (const value)
            (uniformSampler 1 $ const value)
            (PlanSelect 1 $ const value)
        )
        False
        (Inspection Nothing $ Node [Edge (plainSymbol $ Label summary) []])

{- | Apply each outcome, a function of a point, to every point of an indexed
source.

Ranks are outcome-major, so the point varies fastest, and the masses of the
outcomes are shared equally among their points. The given function rewrites
the term of an outcome for its point. The support stays the support of the
outcomes.
-}
pointsStatic ::
    (Hashable symbol, Typeable symbol) =>
    (p -> Tree.Tree (Label symbol) -> Tree.Tree (Label symbol)) ->
    Indexed p ->
    Static symbol (p -> a) ->
    Static symbol a
pointsStatic rewrite pointSource functions =
    applied
        { staticSupport = staticSupport functions
        , staticOutcomes = (staticOutcomes applied){outcomeSelect = select}
        , staticInspection = staticInspection functions
        }
  where
    applied = applyStatic functions $ indexedStatic pointSource
    select index = do
        outcome <- outcomeSelect (staticOutcomes applied) index
        let point = indexedSelect pointSource $ index `rem` indexedCardinality pointSource
            term = case outcomeTerm outcome of
                Tree.Node Apply [functionTerm, _] -> rewrite point functionTerm
                other -> other
        pure outcome{outcomeTerm = term, outcomeInspection = fmap plainSymbol term}

{- | Retain a shared ranked term compiler and its exact equality support.

The values are the accepted terms of the automaton, and the support is the
automaton under user labels. Sampling is uniform over accepted terms. The
common plan supplies replay and structural shrinking. No term is decoded
while this adapter is constructed.
-}
termStatic ::
    (Hashable symbol, Typeable symbol) =>
    Node symbol ->
    (Tree.Tree symbol -> Either GenError Integer) ->
    Ranked.Ranked (Tree.Tree symbol) ->
    Static symbol (Tree.Tree symbol)
termStatic root rankTerm ranked =
    Static
        supportNode
        ( mkOutcomeIndex
            total
            (Just mass)
            select
            (leafRanks termRanks)
            valueAt
            (uniformSampler total valueAt)
            (Ranked.rankedPlan ranked)
        )
        False
        (plainInspection supportNode)
  where
    supportNode = relabel Label root
    total = Ranked.cardinality ranked
    mass = 1 / fromInteger total
    valueAt = Ranked.rankedValueAt ranked
    -- The term of a member is the accepted user term under 'Label'.
    termRanks term = case traverse userSymbol term of
        Just user -> either (const []) pure $ rankTerm user
        Nothing -> []
      where
        userSymbol (Label symbol) = Just symbol
        userSymbol _ = Nothing
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
            productRanks
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

    splitIndex index = index `quotRem` valueCardinality

    -- A spine and a node label give the arguments of the spine in order: the
    -- last one is this product's argument, the others belong to its function.
    productRanks view = case view of
        WholeTerm (Tree.Node Apply [function, argument]) -> ranksFrom (WholeTerm function) argument
        WholeTerm _ -> []
        SpineView arguments -> spineRanks arguments
        LabelledView arguments -> spineRanks arguments
      where
        spineRanks arguments = case reverse arguments of
            argument : functionArguments -> ranksFrom (SpineView $ reverse functionArguments) argument
            [] -> []

        ranksFrom functionView argument =
            [ functionRank * valueCardinality + valueRank
            | functionRank <- outcomeRanks functionOutcomes functionView
            , valueRank <- outcomeRanks valueOutcomes (WholeTerm argument)
            ]

-- | Concatenate weighted alternatives with stable rank offsets.
frequencyStatic ::
    (Hashable symbol, Typeable symbol) =>
    [(Integer, Static symbol a)] -> Static symbol a
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
            choiceRanks
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
            { outcomeSizeSampling = sizeSampling
            }
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
      where
        branchUniformMass (weight, static) =
            (fromInteger weight / fromInteger totalWeight *)
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
                ( fromInteger weight
                    / fromInteger totalWeight
                    * outcomeMass child
                )
                (outcomeValue child)
                (Tree.Node (plainSymbol $ Choice branchIndex) [outcomeInspection child])

    selectValue index =
        let (_, _, static, childIndex) = selectBranch index rankedBranches
         in outcomeValueAt (staticOutcomes static) childIndex

    -- A node label removes the choice wrapper, so it can match every
    -- alternative; a spine gives the whole choice term as one argument.
    choiceRanks view = case view of
        WholeTerm (Tree.Node (Choice branchIndex) [child]) -> branchRanks branchIndex $ WholeTerm child
        WholeTerm _ -> []
        SpineView [term] -> choiceRanks $ WholeTerm term
        SpineView _ -> []
        LabelledView _ -> concat [branchRanks branchIndex view | (_, _, branchIndex, _, _) <- rankedBranches]
    branchRanks branchIndex view =
        [ offset + rank
        | (_, offset, index, _, static) <- rankedBranches
        , index == branchIndex
        , rank <- outcomeRanks (staticOutcomes static) view
        ]

    selectBranch _ [] =
        error
            "microcfta-generator bug in Data.CFTA.Gen.Internal.Static.frequencyStatic: \
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
    ( mkOutcomeIndex
        (outcomeCardinality outcomes)
        (outcomeUniformMass outcomes)
        (fmap (mapOutcome transform) . outcomeSelect outcomes)
        (outcomeRanks outcomes)
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
                (outcomeRanks outcomes)
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
        }

-- | Relabel the retained term of every outcome that the index selects.
labelOutcomeTerms :: symbol -> OutcomeIndex symbol a -> OutcomeIndex symbol a
labelOutcomeTerms symbol outcomes =
    outcomes
        { outcomeSelect = fmap (labelOutcome symbol) . outcomeSelect outcomes
        , outcomeRanks = leafRanks labelledRanks
        }
  where
    -- The label replaces the private root of the inner term, so the inner
    -- language reads the children under it.
    labelledRanks term = case term of
        Tree.Node (Label _) children -> outcomeRanks outcomes $ LabelledView children
        _ -> []

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
        compiled <- compileWeighted weighted
        pure $
            Sampler
                (snd <$> selectWeighted weighted compiled)
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
    gen (Either GenError (Integer, a))
sampleStaticWithRank static
    | Just _ <- outcomeUniformMass outcomes =
        case outcomeDecoder outcomes of
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
            [0 .. toInteger (length outcomes) - 1]
    pure $ zip weights outcomes

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
