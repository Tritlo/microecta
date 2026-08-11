{-# LANGUAGE OverloadedStrings #-}

{- | The transparent-generator engine behind "Data.ECTA.Gen".

Finite languages are represented as a 'Static': an ECTA support paired with
an 'OutcomeIndex' that counts, selects, decodes, and samples outcomes by
rank. This module holds the builders, joins, group buckets, samplers, and
symbols; the public generator types and combinators live in "Data.ECTA.Gen".
-}
module Data.ECTA.Gen.Internal where

import Data.Foldable (toList)
import Data.Kind (Type)
import qualified Data.Map.Strict as Map
import Data.Ratio (denominator, numerator)
import Data.Sequence (Seq)
import qualified Data.Sequence as Sequence
import qualified Data.Text as Text

import Data.ECTA (
    Edge (Edge),
    Node (EmptyNode, Node),
    mkEdge,
    reducePartially,
 )
import Data.ECTA.Gen.Internal.Decoder (
    Plan (..),
    RankDecoder (..),
    compilePlan,
 )
import Data.ECTA.Gen.Sig (Sig (..))
import Data.ECTA.Paths (mkEqConstraints, path)
import Data.ECTA.Term (Symbol (Symbol), Term (Term))

{- | A finite source addressed by a stable integer index.

The selector is called only with an index in @[0, indexedCardinality)@.
-}
data Indexed a = Indexed
    { indexedCardinality :: !Integer
    -- ^ Number of selectable values.
    , indexedSelect :: Integer -> a
    -- ^ Decode one valid index.
    }

-- | Backend operations needed only when sampling or crossing an opaque region.
class (Applicative gen) => GenBackend gen where
    -- | Select an integer in @[0, bound)@.
    selectInteger :: Integer -> gen Integer

    -- | Select a machine 'Int' in @[0, bound)@.
    selectInt :: Int -> gen Int
    selectInt bound = fromInteger <$> selectInteger (toInteger bound)

    -- | Select one backend generator with a positive relative weight.
    frequencyGen :: [(Integer, gen a)] -> gen a

    -- | Retry until the generated value satisfies a predicate.
    filterGen :: (a -> Bool) -> gen a -> gen a

-- | Backend-independent plans for sampling a value, with or without its rank.
data Sampler a = Sampler
    { runValueSampler :: forall gen. (GenBackend gen) => gen a
    , runRankSampler :: forall gen. (GenBackend gen) => gen (Integer, a)
    }

-- | Failure while constructing, inspecting, or sampling a generator.
data ECTAGenError
    = EmptyGenerator
    | NonPositiveWeight !Integer
    | CannotInspectOpaqueGenerator
    | SelectionOutOfRange !Integer !Integer
    deriving (Eq, Show)

-- | One term, its normalized probability mass, and its decoded value.
data Outcome a = Outcome
    { outcomeTerm :: Term
    , outcomeMass :: Rational
    , outcomeValue :: a
    }

-- | A finite language with exact cardinality and rank-based selection.
data OutcomeIndex a = OutcomeIndex
    { outcomeCardinality :: !Integer
    , outcomeUniformMass :: !(Maybe Rational)
    , outcomeSelect :: Integer -> Either ECTAGenError (Outcome a)
    , outcomeValueAt :: Integer -> a
    , outcomeSampler :: !(Sampler a)
    , outcomePlan :: Plan a
    }

-- | Decode positions of one enumerated outcome sequence.
seqPlan :: Seq (Outcome a) -> Plan a
seqPlan outcomes =
    PlanSelect
        (toInteger $ Sequence.length outcomes)
        (outcomeValue . Sequence.index outcomes . fromInteger)

-- | One equality-key bucket used to count and unrank a conditioned product.
data JoinGroup left right = JoinGroup
    { joinGroupIndex :: !Int
    , joinGroupLeft :: !(Seq (Outcome left))
    , joinGroupRight :: !(Seq (Outcome right))
    }

-- | One transparent ECTA with a matching indexed outcome language.
data Static a = Static
    { staticSupport :: !Node
    , staticOutcomes :: !(OutcomeIndex a)
    }

-- | One compact conditional generator and its mass in the whole distribution.
data KeyedBucket a = KeyedBucket
    { keyedBucketMass :: !Rational
    , keyedBucketStatic :: !(Static a)
    }

-- | Build one retained group from its outcomes, in rank order.
bucketFromOutcomes :: [Outcome a] -> Either ECTAGenError (KeyedBucket a)
bucketFromOutcomes outcomes = do
    sampler <- sequenceSampler conditional
    pure $
        KeyedBucket bucketMass $
            Static
                bucketSupport
                ( OutcomeIndex
                    totalOutcomes
                    uniformMass
                    select
                    selectValue
                    sampler
                    (PlanSelect totalOutcomes selectValue)
                )
  where
    bucketMass = sum $ map outcomeMass outcomes
    conditional =
        Sequence.fromList
            [ outcome{outcomeMass = outcomeMass outcome / bucketMass}
            | outcome <- outcomes
            ]
    totalOutcomes = toInteger $ length outcomes
    uniformMass = commonValue $ Just . outcomeMass <$> toList conditional
    bucketSupport = Node [termEdge $ outcomeTerm outcome | outcome <- outcomes]
    termEdge (Term symbol children) = Edge symbol $ map singletonNode children

    select index = do
        checkIndex totalOutcomes index
        pure $ Sequence.index conditional $ fromInteger index

    selectValue = outcomeValue . Sequence.index conditional . fromInteger

-- | Bucket maps of every argument family, threaded through the operation type.
data ArgMaps (argKeys :: [Type]) operation result where
    MapsNil :: ArgMaps '[] result result
    MapsCons ::
        (Ord argKey) =>
        Map.Map argKey (KeyedBucket arg) ->
        ArgMaps argKeys operation result ->
        ArgMaps (argKey ': argKeys) (arg -> operation) result

-- | The matched group of every argument family, in signature order.
data ArgStatics operation result where
    StaticsNil :: ArgStatics result result
    StaticsCons ::
        Static arg ->
        ArgStatics operation result ->
        ArgStatics (arg -> operation) result

lookupArgs ::
    Sig argKeys resultKey ->
    ArgMaps argKeys operation result ->
    Maybe (Rational, ArgStatics operation result)
lookupArgs (key :-> _) (MapsCons buckets MapsNil) = do
    bucket <- Map.lookup key buckets
    Just
        ( keyedBucketMass bucket
        , StaticsCons (keyedBucketStatic bucket) StaticsNil
        )
lookupArgs (key :* rest) (MapsCons buckets restMaps) = do
    bucket <- Map.lookup key buckets
    (mass, statics) <- lookupArgs rest restMaps
    Just
        ( keyedBucketMass bucket * mass
        , StaticsCons (keyedBucketStatic bucket) statics
        )

mapStatic :: (a -> b) -> Static a -> Static b
mapStatic transform static =
    Static
        (staticSupport static)
        (mapOutcomeIndex transform $ staticOutcomes static)

pureStatic :: a -> Static a
pureStatic value =
    Static
        (Node [Edge pureSymbol []])
        ( OutcomeIndex
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

indexedStatic :: Indexed a -> Static a
indexedStatic indexed =
    Static
        (Node [Edge (indexedSymbol index) [] | index <- [0 .. totalOutcomes - 1]])
        ( OutcomeIndex
            totalOutcomes
            (Just $ 1 / fromInteger totalOutcomes)
            select
            (indexedSelect indexed)
            (uniformSampler totalOutcomes $ indexedSelect indexed)
            (PlanSelect totalOutcomes $ indexedSelect indexed)
        )
  where
    totalOutcomes = indexedCardinality indexed
    select index = do
        checkIndex totalOutcomes index
        pure $
            Outcome
                (Term (indexedSymbol index) [])
                (1 / fromInteger totalOutcomes)
                (indexedSelect indexed index)

applyStatic :: Static (a -> b) -> Static a -> Static b
applyStatic functions values =
    Static
        ( Node
            [ Edge
                applySymbol
                [staticSupport functions, staticSupport values]
            ]
        )
        ( OutcomeIndex
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

frequencyStatic :: [(Integer, Static a)] -> Static a
frequencyStatic alternatives =
    Static
        ( Node
            [ Edge (frequencySymbol index) [staticSupport static]
            | (index, (_, static)) <- numbered
            ]
        )
        ( OutcomeIndex
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

    selectBranch _ [] = error "frequencyStatic: rank outside alternatives"
    selectBranch index ((upperBound, offset, branchIndex, weight, static) : remaining)
        | index < upperBound = (branchIndex, weight, static, index - offset)
        | otherwise = selectBranch index remaining

joinStatic ::
    (Ord key) =>
    (left -> key) ->
    (right -> key) ->
    Static left ->
    Static right ->
    Either ECTAGenError (Static (left, right))
joinStatic leftKey rightKey left right = do
    leftEntries <- keyedOutcomes leftKey left
    rightEntries <- keyedOutcomes rightKey right
    let shared =
            Map.intersectionWith
                (,)
                (groupOutcomes leftEntries)
                (groupOutcomes rightEntries)
    if Map.null shared
        then Left EmptyGenerator
        else
            let groups =
                    [ JoinGroup
                        keyIndex
                        (Sequence.fromList leftOutcomes)
                        (Sequence.fromList rightOutcomes)
                    | (keyIndex, (_, (leftOutcomes, rightOutcomes))) <-
                        zip [0 :: Int ..] $ Map.toAscList shared
                    ]
                leftNode =
                    Node
                        [ Edge
                            leftKeyedSymbol
                            [ keyNode $ joinGroupIndex group
                            , singletonNode $ outcomeTerm outcome
                            ]
                        | group <- groups
                        , outcome <- toList $ joinGroupLeft group
                        ]
                rightNode =
                    Node
                        [ Edge
                            rightKeyedSymbol
                            [ keyNode $ joinGroupIndex group
                            , singletonNode $ outcomeTerm outcome
                            ]
                        | group <- groups
                        , outcome <- toList $ joinGroupRight group
                        ]
                joined =
                    reducePartially $
                        Node
                            [ mkEdge
                                joinSymbol
                                [leftNode, rightNode]
                                (mkEqConstraints [[path [0, 0], path [1, 0]]])
                            ]
             in if joined == EmptyNode
                    then Left EmptyGenerator
                    else Static joined <$> joinOutcomeIndex left right groups

keyedOutcomes ::
    (value -> key) ->
    Static value ->
    Either ECTAGenError [(key, Outcome value)]
keyedOutcomes key static =
    map (\outcome -> (key $ outcomeValue outcome, outcome))
        <$> enumerateOutcomeIndex (staticOutcomes static)

groupOutcomes :: (Ord key) => [(key, Outcome value)] -> Map.Map key [Outcome value]
groupOutcomes = Map.fromListWith (<>) . map (fmap pure)

joinOutcomeIndex ::
    Static left ->
    Static right ->
    [JoinGroup left right] ->
    Either ECTAGenError (OutcomeIndex (left, right))
joinOutcomeIndex left right groups = do
    rankSampler <- case uniformMass of
        Just _ -> pure $ uniformSampler totalOutcomes selectValue
        Nothing -> joinSampler groups
    pure $
        OutcomeIndex
            totalOutcomes
            uniformMass
            select
            selectValue
            rankSampler
            ( PlanChoice
                [ ( joinGroupCardinality group
                  , PlanAp
                        (toInteger $ Sequence.length $ joinGroupRight group)
                        (PlanMap (,) $ seqPlan $ joinGroupLeft group)
                        (seqPlan $ joinGroupRight group)
                  )
                | group <- groups
                ]
            )
  where
    totalOutcomes = sum $ map joinGroupCardinality groups
    uniformMass = case (outcomeUniformMass $ staticOutcomes left, outcomeUniformMass $ staticOutcomes right) of
        (Just _, Just _) -> Just $ 1 / fromInteger totalOutcomes
        _ -> Nothing
    totalMass = sum $ map joinGroupMass groups

    select index = do
        checkIndex totalOutcomes index
        let (group, leftOutcome, rightOutcome) = selectPair index
            keyTerm = Term (keySymbol $ joinGroupIndex group) []
            leftTerm =
                Term leftKeyedSymbol [keyTerm, outcomeTerm leftOutcome]
            rightTerm =
                Term rightKeyedSymbol [keyTerm, outcomeTerm rightOutcome]
        pure $
            Outcome
                (Term joinSymbol [leftTerm, rightTerm])
                ( outcomeMass leftOutcome
                    * outcomeMass rightOutcome
                    / totalMass
                )
                (outcomeValue leftOutcome, outcomeValue rightOutcome)

    selectValue index =
        let (_, leftOutcome, rightOutcome) = selectPair index
         in (outcomeValue leftOutcome, outcomeValue rightOutcome)

    selectPair index =
        let (group, groupIndex) = selectJoinGroup index groups
            rightCardinality = toInteger $ Sequence.length $ joinGroupRight group
            (leftIndex, rightIndex) = groupIndex `quotRem` rightCardinality
            leftOutcome = Sequence.index (joinGroupLeft group) $ fromInteger leftIndex
            rightOutcome = Sequence.index (joinGroupRight group) $ fromInteger rightIndex
         in (group, leftOutcome, rightOutcome)

joinGroupCardinality :: JoinGroup left right -> Integer
joinGroupCardinality group =
    toInteger (Sequence.length $ joinGroupLeft group)
        * toInteger (Sequence.length $ joinGroupRight group)

joinGroupMass :: JoinGroup left right -> Rational
joinGroupMass group =
    sum (outcomeMass <$> joinGroupLeft group)
        * sum (outcomeMass <$> joinGroupRight group)

selectJoinGroup ::
    Integer ->
    [JoinGroup left right] ->
    (JoinGroup left right, Integer)
selectJoinGroup _ [] = error "selectJoinGroup: rank outside groups"
selectJoinGroup index (group : remaining)
    | index < groupSize = (group, index)
    | otherwise = selectJoinGroup (index - groupSize) remaining
  where
    groupSize = joinGroupCardinality group

joinSampler ::
    [JoinGroup left right] ->
    Either ECTAGenError (Sampler (left, right))
joinSampler groups = do
    weightedGroups <-
        integerOutcomes
            [ (joinGroupMass group, (offset, group))
            | (offset, group) <- offsetJoinGroups groups
            ]
    plans <- traverse branchPlan weightedGroups
    pure $
        Sampler
            ( frequencyGen
                [ ( weight
                  , liftA2
                        (,)
                        (runValueSampler leftSampler)
                        (runValueSampler rightSampler)
                  )
                | (weight, _, _, leftSampler, rightSampler) <- plans
                ]
            )
            ( frequencyGen
                [ ( weight
                  , liftA2
                        ( \(leftIndex, leftValue) (rightIndex, rightValue) ->
                            ( offset + leftIndex * rightCardinality + rightIndex
                            , (leftValue, rightValue)
                            )
                        )
                        (runRankSampler leftSampler)
                        (runRankSampler rightSampler)
                  )
                | (weight, offset, rightCardinality, leftSampler, rightSampler) <- plans
                ]
            )
  where
    branchPlan (weight, (offset, group)) = do
        leftSampler <- sequenceSampler $ joinGroupLeft group
        rightSampler <- sequenceSampler $ joinGroupRight group
        let rightCardinality = toInteger $ Sequence.length $ joinGroupRight group
        pure (weight, offset, rightCardinality, leftSampler, rightSampler)

offsetJoinGroups :: [JoinGroup left right] -> [(Integer, JoinGroup left right)]
offsetJoinGroups = go 0
  where
    go _ [] = []
    go offset (group : remaining) =
        (offset, group) : go (offset + joinGroupCardinality group) remaining

mergeKeyedBuckets :: Map.Map key (KeyedBucket a) -> Either ECTAGenError (Static a)
mergeKeyedBuckets buckets = do
    weightedBuckets <-
        integerOutcomes
            [ (keyedBucketMass bucket, keyedBucketStatic bucket)
            | bucket <- Map.elems buckets
            ]
    pure $ frequencyStatic weightedBuckets

mergeBucketGroup :: [(Rational, Static a)] -> Either ECTAGenError (KeyedBucket a)
mergeBucketGroup alternatives = do
    weightedAlternatives <- integerOutcomes alternatives
    pure $
        KeyedBucket
            (sum $ map fst alternatives)
            (frequencyStatic weightedAlternatives)

-- | Merge weighted joined components into normalized result-key groups.
mergeComponentsByKey ::
    (Ord resultKey) =>
    [(resultKey, Rational, Static a)] ->
    Either ECTAGenError (Map.Map resultKey (KeyedBucket a))
mergeComponentsByKey [] = Left EmptyGenerator
mergeComponentsByKey components = do
    unnormalized <- traverse mergeBucketGroup grouped
    let totalAcceptedMass = sum $ keyedBucketMass <$> unnormalized
    pure $ fmap (normalizeBucket totalAcceptedMass) unnormalized
  where
    grouped =
        foldl'
            ( \groups (resultKey, mass, static) ->
                Map.insertWith
                    (flip (<>))
                    resultKey
                    [(mass, static)]
                    groups
            )
            Map.empty
            components

    normalizeBucket totalAcceptedMass bucket =
        bucket
            { keyedBucketMass =
                keyedBucketMass bucket / totalAcceptedMass
            }

joinNBucketStatic ::
    Int ->
    Static operation ->
    ArgStatics operation result ->
    Either ECTAGenError (Static result)
joinNBucketStatic componentIndex operation arguments =
    if joined == EmptyNode
        then Left EmptyGenerator
        else
            Right $
                Static
                    joined
                    ( OutcomeIndex
                        totalOutcomes
                        uniformMass
                        select
                        selectValue
                        rankSampler
                        (chainPlan (outcomePlan operationOutcomes) arguments)
                    )
  where
    keyTerms =
        [ Term (argKeySymbol componentIndex position) []
        | position <- [0 .. chainLength arguments - 1]
        ]
    keyNodes = map singletonNode keyTerms
    operationNode =
        Node
            [ Edge
                centerKeyedSymbol
                (keyNodes <> [staticSupport operation])
            ]
    argumentNodes =
        [ Node [Edge argKeyedSymbol [argKeyNode, argSupport]]
        | (argKeyNode, argSupport) <- zip keyNodes (chainSupports arguments)
        ]
    joined =
        reducePartially $
            Node
                [ mkEdge
                    joinNSymbol
                    (operationNode : argumentNodes)
                    ( mkEqConstraints
                        [ [path [0, position], path [position + 1, 0]]
                        | position <- [0 .. chainLength arguments - 1]
                        ]
                    )
                ]
    operationOutcomes = staticOutcomes operation
    argumentsCardinality = chainCardinality arguments
    totalOutcomes = outcomeCardinality operationOutcomes * argumentsCardinality
    uniformMass =
        (*)
            <$> outcomeUniformMass operationOutcomes
            <*> chainUniformMass arguments
    rankSampler = chainSampler (outcomeSampler operationOutcomes) arguments
    decodeArguments = chainDecoder arguments

    select index = do
        checkIndex totalOutcomes index
        let (operationIndex, argumentIndex) = index `quotRem` argumentsCardinality
        operationOutcome <- outcomeSelect operationOutcomes operationIndex
        (argumentTerms, argumentsMass, value) <-
            selectChain (outcomeValue operationOutcome) arguments keyTerms argumentIndex
        let operationTerm =
                Term centerKeyedSymbol (keyTerms <> [outcomeTerm operationOutcome])
        pure $
            Outcome
                (Term joinNSymbol (operationTerm : argumentTerms))
                (outcomeMass operationOutcome * argumentsMass)
                value

    selectValue index =
        let (operationIndex, argumentIndex) = index `quotRem` argumentsCardinality
         in decodeArguments (outcomeValueAt operationOutcomes operationIndex) argumentIndex

chainLength :: ArgStatics operation result -> Int
chainLength StaticsNil = 0
chainLength (StaticsCons _ rest) = 1 + chainLength rest

chainSupports :: ArgStatics operation result -> [Node]
chainSupports StaticsNil = []
chainSupports (StaticsCons static rest) = staticSupport static : chainSupports rest

chainCardinality :: ArgStatics operation result -> Integer
chainCardinality StaticsNil = 1
chainCardinality (StaticsCons static rest) =
    outcomeCardinality (staticOutcomes static) * chainCardinality rest

chainUniformMass :: ArgStatics operation result -> Maybe Rational
chainUniformMass StaticsNil = Just 1
chainUniformMass (StaticsCons static rest) =
    (*)
        <$> outcomeUniformMass (staticOutcomes static)
        <*> chainUniformMass rest

{- | Compose the mixed-radix rank sampler as a left 'productSampler' fold.

The composed rank is @operationRank@ most significant, then argument ranks
left to right, matching 'chainDecoder'.
-}
chainSampler :: Sampler operation -> ArgStatics operation result -> Sampler result
chainSampler sampler StaticsNil = sampler
chainSampler sampler (StaticsCons static rest) =
    chainSampler
        ( productSampler
            (outcomeCardinality $ staticOutcomes static)
            sampler
            (outcomeSampler $ staticOutcomes static)
        )
        rest

-- | Mirror 'chainSampler' as plan structure, one product per argument.
chainPlan :: Plan operation -> ArgStatics operation result -> Plan result
chainPlan plan StaticsNil = plan
chainPlan plan (StaticsCons static rest) =
    chainPlan
        ( PlanAp
            (outcomeCardinality $ staticOutcomes static)
            plan
            (outcomePlan $ staticOutcomes static)
        )
        rest

-- | Build a rank decoder once, capturing every suffix cardinality.
chainDecoder :: ArgStatics operation result -> operation -> Integer -> result
chainDecoder StaticsNil = \value _ -> value
chainDecoder (StaticsCons static StaticsNil) =
    let valueAt = outcomeValueAt $ staticOutcomes static
     in \operation index -> operation $ valueAt index
chainDecoder (StaticsCons first (StaticsCons second StaticsNil)) =
    let firstValueAt = outcomeValueAt $ staticOutcomes first
        secondOutcomes = staticOutcomes second
        secondCardinality = outcomeCardinality secondOutcomes
        secondValueAt = outcomeValueAt secondOutcomes
     in \operation index ->
            let (firstIndex, secondIndex) = index `quotRem` secondCardinality
             in operation (firstValueAt firstIndex) (secondValueAt secondIndex)
chainDecoder (StaticsCons static rest) =
    let decodeRest = chainDecoder rest
        suffixCardinality = chainCardinality rest
        valueAt = outcomeValueAt $ staticOutcomes static
     in \partial index ->
            let (here, there) = index `quotRem` suffixCardinality
             in decodeRest (partial $ valueAt here) there

selectChain ::
    operation ->
    ArgStatics operation result ->
    [Term] ->
    Integer ->
    Either ECTAGenError ([Term], Rational, result)
selectChain value StaticsNil _ _ = Right ([], 1, value)
selectChain partial (StaticsCons static rest) (keyTerm : keyTerms) index = do
    let (here, there) = index `quotRem` chainCardinality rest
    outcome <- outcomeSelect (staticOutcomes static) here
    (terms, mass, value) <- selectChain (partial $ outcomeValue outcome) rest keyTerms there
    pure
        ( Term argKeyedSymbol [keyTerm, outcomeTerm outcome] : terms
        , outcomeMass outcome * mass
        , value
        )
selectChain _ (StaticsCons _ _) [] _ = error "selectChain: missing key terms"

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

keyNode :: Int -> Node
keyNode index = Node [Edge (keySymbol index) []]

singletonNode :: Term -> Node
singletonNode (Term symbol children) =
    Node [Edge symbol $ map singletonNode children]

compileOutcomes :: Static a -> Either ECTAGenError [(Rational, a)]
compileOutcomes static = do
    outcomes <- enumerateOutcomeIndex $ staticOutcomes static
    normalize [(outcomeMass outcome, outcomeValue outcome) | outcome <- outcomes]

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

-- | Compile the retained plan once, at lowering time.
compiledDecoder :: OutcomeIndex a -> RankDecoder a
compiledDecoder outcomes =
    compilePlan (outcomeCardinality outcomes) (outcomePlan outcomes)

uniformSampler :: Integer -> (Integer -> a) -> Sampler a
uniformSampler 1 valueAt = Sampler (pure $ valueAt 0) (pure (0, valueAt 0))
uniformSampler totalOutcomes valueAt =
    Sampler
        (valueAt <$> selectInteger totalOutcomes)
        ((\index -> (index, valueAt index)) <$> selectInteger totalOutcomes)

productSampler :: Integer -> Sampler (a -> b) -> Sampler a -> Sampler b
productSampler rightCardinality leftSampler rightSampler =
    Sampler
        (runValueSampler leftSampler <*> runValueSampler rightSampler)
        ( liftA2
            ( \(leftIndex, partial) (rightIndex, value) ->
                (leftIndex * rightCardinality + rightIndex, partial value)
            )
            (runRankSampler leftSampler)
            (runRankSampler rightSampler)
        )

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

offsetAlternatives :: [(Integer, Static a)] -> [(Integer, (Integer, Static a))]
offsetAlternatives = go 0
  where
    go _ [] = []
    go offset (alternative@(_, static) : remaining) =
        (offset, alternative)
            : go
                (offset + outcomeCardinality (staticOutcomes static))
                remaining

mapOutcomeIndex :: (a -> b) -> OutcomeIndex a -> OutcomeIndex b
mapOutcomeIndex transform outcomes =
    OutcomeIndex
        (outcomeCardinality outcomes)
        (outcomeUniformMass outcomes)
        (\index -> mapOutcome transform <$> outcomeSelect outcomes index)
        (transform . outcomeValueAt outcomes)
        ( Sampler
            (transform <$> runValueSampler (outcomeSampler outcomes))
            ( (\(rank, value) -> (rank, transform value))
                <$> runRankSampler (outcomeSampler outcomes)
            )
        )
        (PlanMap transform $ outcomePlan outcomes)

mapOutcome :: (a -> b) -> Outcome a -> Outcome b
mapOutcome transform outcome =
    Outcome
        (outcomeTerm outcome)
        (outcomeMass outcome)
        (transform $ outcomeValue outcome)

enumerateOutcomeIndex :: OutcomeIndex a -> Either ECTAGenError [Outcome a]
enumerateOutcomeIndex outcomes =
    traverse
        (outcomeSelect outcomes)
        [0 .. outcomeCardinality outcomes - 1]

commonValue :: (Eq a) => [Maybe a] -> Maybe a
commonValue [] = Nothing
commonValue (Just value : remaining)
    | all (== Just value) remaining = Just value
commonValue _ = Nothing

checkIndex :: Integer -> Integer -> Either ECTAGenError ()
checkIndex totalOutcomes index
    | index < 0 || index >= totalOutcomes =
        Left $ SelectionOutOfRange index totalOutcomes
    | otherwise = Right ()

normalize :: [(Rational, a)] -> Either ECTAGenError [(Rational, a)]
normalize [] = Left EmptyGenerator
normalize outcomes =
    let total = sum $ map fst outcomes
     in if total <= 0
            then Left EmptyGenerator
            else Right [(mass / total, value) | (mass, value) <- outcomes]

integerOutcomes ::
    [(Rational, a)] ->
    Either ECTAGenError [(Integer, a)]
integerOutcomes [] = Left EmptyGenerator
integerOutcomes outcomes =
    let masses = map fst outcomes
        commonDenominator = foldl lcm 1 $ map denominator masses
        unscaled =
            [ numerator mass * (commonDenominator `div` denominator mass)
            | mass <- masses
            ]
        commonFactor = foldl gcd 0 unscaled
     in if any (<= 0) unscaled
            then Left EmptyGenerator
            else
                Right $
                    zip
                        (map (`div` commonFactor) unscaled)
                        (map snd outcomes)

atIndex :: String -> Integer -> [a] -> a
atIndex label index values
    | index < 0 = error $ label <> ": negative index"
    | otherwise = case drop (fromInteger index) values of
        value : _ -> value
        [] -> error $ label <> ": index out of range"

pureSymbol, applySymbol, joinSymbol, joinNSymbol, centerKeyedSymbol, leftKeyedSymbol, rightKeyedSymbol, argKeyedSymbol :: Symbol
pureSymbol = "$ecta-gen/pure"
applySymbol = "$ecta-gen/apply"
joinSymbol = "$ecta-gen/join"
centerKeyedSymbol = "$ecta-gen/center-keyed"
leftKeyedSymbol = "$ecta-gen/left-keyed"
rightKeyedSymbol = "$ecta-gen/right-keyed"
joinNSymbol = "$ecta-gen/join-n"
argKeyedSymbol = "$ecta-gen/arg-keyed"

indexedSymbol :: Integer -> Symbol
indexedSymbol index = Symbol $ Text.pack $ "$ecta-gen/index/" <> show index

frequencySymbol :: Int -> Symbol
frequencySymbol index = Symbol $ Text.pack $ "$ecta-gen/frequency/" <> show index

keySymbol :: Int -> Symbol
keySymbol index = Symbol $ Text.pack $ "$ecta-gen/key/" <> show index

argKeySymbol :: Int -> Int -> Symbol
argKeySymbol componentIndex position =
    Symbol $
        Text.pack $
            "$ecta-gen/key/" <> show componentIndex <> "/" <> show position
