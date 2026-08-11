{-# LANGUAGE OverloadedStrings #-}

{- | Indexed generators whose transparent regions are represented as ECTAs.

An indexed source stores a finite cardinality and a function from indices to
values. Applicative composition tracks exact cardinalities and rank-based
selection alongside the ECTA, without materializing the product language.
Joins count matched key-bucket products and unrank directly within them.
-}
module Data.ECTA.Gen (
    Indexed (..),
    ECTAGen,
    KeyedECTAGen,
    ECTAGenError (..),
    GenBackend (..),
    fromIndexed,
    fromBackend,
    elements,
    keyedElements,
    mapKeyed,
    innerJoin3Keyed,
    forgetKey,
    frequency,
    innerJoinOn,
    innerJoin3On,
    support,
    cardinality,
    unrank,
    countBy,
    pmf,
    lower,
    lowerWithRank,
) where

import Control.Applicative (liftA3)
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

    -- | Select one backend generator with a positive relative weight.
    frequencyGen :: [(Integer, gen a)] -> gen a

    -- | Retry until the generated value satisfies a predicate.
    filterGen :: (a -> Bool) -> gen a -> gen a

-- | A backend-independent plan for sampling one rank and its decoded value.
newtype RankSampler a = RankSampler
    { runRankSampler :: forall gen. (GenBackend gen) => gen (Integer, a)
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
    , outcomeRankSampler :: !(RankSampler a)
    }

-- | One equality-key bucket used to count and unrank a conditioned product.
data JoinGroup left right = JoinGroup
    { joinGroupIndex :: !Int
    , joinGroupLeft :: !(Seq (Outcome left))
    , joinGroupRight :: !(Seq (Outcome right))
    }

-- | One pair-of-keys bucket used by a three-way conditioned product.
data Join3Group center left right = Join3Group
    { join3GroupIndex :: !Int
    , join3GroupCenter :: !(Seq (Outcome center))
    , join3GroupLeft :: !(Seq (Outcome left))
    , join3GroupRight :: !(Seq (Outcome right))
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

{- | A transparent generator whose distribution remains explicitly partitioned
by key.

Each partition retains compact ECTA support and indexed selection. It never
stores all outcomes in that partition.
-}
newtype KeyedECTAGen (gen :: Type -> Type) key a
    = KeyedECTAGen (Either ECTAGenError (Map.Map key (KeyedBucket a)))

-- | A generator is either inspectable ECTA structure or an opaque backend action.
data ECTAGen gen a
    = Transparent !(Either ECTAGenError (Static a))
    | Opaque !(gen (Either ECTAGenError a))

instance (Functor gen) => Functor (ECTAGen gen) where
    fmap apply (Transparent result) = Transparent $ fmap (mapStatic apply) result
    fmap apply (Opaque generated) = Opaque $ fmap (fmap apply) generated

instance (GenBackend gen) => Applicative (ECTAGen gen) where
    pure value = Transparent $ Right $ pureStatic value

    Transparent (Left err) <*> _ = Transparent $ Left err
    _ <*> Transparent (Left err) = Transparent $ Left err
    Transparent (Right functions) <*> Transparent (Right values) =
        Transparent $ Right $ applyStatic functions values
    functions <*> values =
        Opaque $ liftA2 (<*>) (lower functions) (lower values)

-- | Lift one finite indexed source into transparent ECTA structure.
fromIndexed :: Indexed a -> ECTAGen gen a
fromIndexed indexed
    | indexedCardinality indexed <= 0 = Transparent $ Left EmptyGenerator
    | otherwise = Transparent $ Right $ indexedStatic indexed

-- | Embed an opaque backend generator.
fromBackend :: (Functor gen) => gen a -> ECTAGen gen a
fromBackend generated = Opaque $ Right <$> generated

-- | Choose uniformly from a finite non-empty list.
elements :: [a] -> ECTAGen gen a
elements values =
    fromIndexed $
        Indexed
            (toInteger $ length values)
            (\index -> atIndex "elements" index values)

{- | Uniformly choose from a finite source while retaining its key partitions.

Keys are ordered by their 'Ord' instance. Values within each key retain their
source order.
-}
keyedElements :: (Ord key) => (a -> key) -> [a] -> KeyedECTAGen gen key a
keyedElements _ [] = KeyedECTAGen $ Left EmptyGenerator
keyedElements key values =
    KeyedECTAGen $
        Right $
            Map.map makeBucket $
                foldl' insertValue Map.empty values
  where
    totalOutcomes = toInteger $ length values

    insertValue buckets value =
        Map.insertWith (flip (<>)) (key value) [value] buckets

    makeBucket bucketValues =
        let bucketCardinality = toInteger $ length bucketValues
         in KeyedBucket
                (fromInteger bucketCardinality / fromInteger totalOutcomes)
                ( indexedStatic $
                    Indexed
                        bucketCardinality
                        (\index -> atIndex "keyedElements" index bucketValues)
                )

-- | Map partition values without changing their retained keys.
mapKeyed :: (a -> b) -> KeyedECTAGen gen key a -> KeyedECTAGen gen key b
mapKeyed apply (KeyedECTAGen result) =
    KeyedECTAGen $ fmap (fmap mapBucket) result
  where
    mapBucket bucket =
        KeyedBucket
            (keyedBucketMass bucket)
            (mapStatic apply $ keyedBucketStatic bucket)

{- | Join a keyed center with two keyed arguments and retain result-key
partitions.

The center key names the required left and right keys plus the result key.
Joined supports are built directly from compact bucket supports and contain two
real ECTA equality constraints. Ranks are ordered by result key, then center
key, then the three source ranks.
-}
innerJoin3Keyed ::
    (Ord leftKey, Ord rightKey, Ord resultKey) =>
    (centerKey -> (leftKey, rightKey, resultKey)) ->
    KeyedECTAGen gen centerKey center ->
    KeyedECTAGen gen leftKey left ->
    KeyedECTAGen gen rightKey right ->
    KeyedECTAGen gen resultKey (center, left, right)
innerJoin3Keyed _ (KeyedECTAGen (Left err)) _ _ = KeyedECTAGen $ Left err
innerJoin3Keyed _ _ (KeyedECTAGen (Left err)) _ = KeyedECTAGen $ Left err
innerJoin3Keyed _ _ _ (KeyedECTAGen (Left err)) = KeyedECTAGen $ Left err
innerJoin3Keyed partitionCenter (KeyedECTAGen (Right centers)) (KeyedECTAGen (Right lefts)) (KeyedECTAGen (Right rights)) =
    KeyedECTAGen $ join3KeyedBuckets partitionCenter centers lefts rights

-- | Forget retained keys while preserving the represented distribution.
forgetKey :: KeyedECTAGen gen key a -> ECTAGen gen a
forgetKey (KeyedECTAGen (Left err)) = Transparent $ Left err
forgetKey (KeyedECTAGen (Right buckets)) =
    Transparent $ mergeKeyedBuckets buckets

-- | Choose one generator with the supplied positive relative weight.
frequency ::
    (GenBackend gen) =>
    [(Integer, ECTAGen gen a)] ->
    ECTAGen gen a
frequency [] = Transparent $ Left EmptyGenerator
frequency alternatives
    | Just badWeight <- firstNonPositive alternatives =
        Transparent $ Left $ NonPositiveWeight badWeight
    | Just err <- firstError alternatives = Transparent $ Left err
    | Just staticAlternatives <- traverse getStatic alternatives =
        Transparent $ Right $ frequencyStatic staticAlternatives
    | otherwise =
        Opaque $
            frequencyGen
                [(weight, lower generator) | (weight, generator) <- alternatives]
  where
    firstNonPositive = go
      where
        go [] = Nothing
        go ((weight, _) : rest)
            | weight <= 0 = Just weight
            | otherwise = go rest

    firstError = go
      where
        go [] = Nothing
        go ((_, Transparent (Left err)) : _) = Just err
        go (_ : rest) = go rest

    getStatic (weight, Transparent (Right static)) = Just (weight, static)
    getStatic _ = Nothing

{- | Independently generate two values and condition their projected keys to
agree.

Transparent inputs are joined by adding an equality constraint between encoded
key indices. If either side is opaque, the backend performs rejection instead.
-}
innerJoinOn ::
    (GenBackend gen, Ord key) =>
    (left -> key) ->
    (right -> key) ->
    ECTAGen gen left ->
    ECTAGen gen right ->
    ECTAGen gen (left, right)
innerJoinOn _ _ (Transparent (Left err)) _ = Transparent $ Left err
innerJoinOn _ _ _ (Transparent (Left err)) = Transparent $ Left err
innerJoinOn leftKey rightKey (Transparent (Right left)) (Transparent (Right right)) =
    Transparent $ joinStatic leftKey rightKey left right
innerJoinOn leftKey rightKey left right =
    Opaque $ filterGen matches generatedPairs
  where
    generatedPairs = liftA2 (liftA2 (,)) (lower left) (lower right)
    matches (Left _) = True
    matches (Right (leftValue, rightValue)) =
        leftKey leftValue == rightKey rightValue

{- | Independently generate a center value and two arguments, conditioning
each projected center key to agree with the corresponding argument key.

Transparent inputs use one ECTA edge with two equality constraints. If any
input is opaque, the backend performs rejection instead.
-}
innerJoin3On ::
    (GenBackend gen, Ord leftKey, Ord rightKey) =>
    (center -> (leftKey, rightKey)) ->
    (left -> leftKey) ->
    (right -> rightKey) ->
    ECTAGen gen center ->
    ECTAGen gen left ->
    ECTAGen gen right ->
    ECTAGen gen (center, left, right)
innerJoin3On _ _ _ (Transparent (Left err)) _ _ = Transparent $ Left err
innerJoin3On _ _ _ _ (Transparent (Left err)) _ = Transparent $ Left err
innerJoin3On _ _ _ _ _ (Transparent (Left err)) = Transparent $ Left err
innerJoin3On centerKeys leftKey rightKey (Transparent (Right center)) (Transparent (Right left)) (Transparent (Right right)) =
    Transparent $ join3Static centerKeys leftKey rightKey center left right
innerJoin3On centerKeys leftKey rightKey center left right =
    Opaque $ filterGen matches generatedTriples
  where
    generatedTriples =
        liftA3 (liftA3 (,,)) (lower center) (lower left) (lower right)
    matches (Left _) = True
    matches (Right (centerValue, leftValue, rightValue)) =
        let (expectedLeft, expectedRight) = centerKeys centerValue
         in expectedLeft == leftKey leftValue
                && expectedRight == rightKey rightValue

-- | Return the ECTA support of a fully transparent generator.
support :: ECTAGen gen a -> Either ECTAGenError Node
support (Transparent result) = staticSupport <$> result
support (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Return the exact number of ranks in a transparent generator.
cardinality :: ECTAGen gen a -> Either ECTAGenError Integer
cardinality (Transparent result) =
    outcomeCardinality . staticOutcomes <$> result
cardinality (Opaque _) = Left CannotInspectOpaqueGenerator

{- | Decode one stable rank from a transparent generator.

Ranks are stable while the generator definition and the ordering of its finite
sources remain unchanged.
-}
unrank :: ECTAGen gen a -> Integer -> Either ECTAGenError a
unrank (Transparent result) index = do
    static <- result
    let outcomes = staticOutcomes static
    checkIndex (outcomeCardinality outcomes) index
    pure $ outcomeValueAt outcomes index
unrank (Opaque _) _ = Left CannotInspectOpaqueGenerator

-- | Count ranked outcomes by a projected key without aggregating equal values.
countBy :: (Ord key) => (a -> key) -> ECTAGen gen a -> Either ECTAGenError (Map.Map key Integer)
countBy key (Transparent result) = do
    static <- result
    outcomes <- enumerateOutcomeIndex $ staticOutcomes static
    pure $
        Map.fromListWith
            (+)
            [(key $ outcomeValue outcome, 1) | outcome <- outcomes]
countBy _ (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Aggregate the exact probability mass of every transparent result.
pmf :: (Ord a) => ECTAGen gen a -> Either ECTAGenError [(a, Rational)]
pmf (Transparent result) = do
    static <- result
    outcomes <- compileOutcomes static
    pure $
        Map.toAscList $
            Map.fromListWith (+) [(value, mass) | (mass, value) <- outcomes]
pmf (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Lower to the backend, preserving construction and decoding errors.
lower :: (GenBackend gen) => ECTAGen gen a -> gen (Either ECTAGenError a)
lower (Transparent (Left err)) = pure $ Left err
lower (Transparent (Right static)) = sampleStatic static
lower (Opaque generated) = generated

-- | Lower a transparent generator while retaining the sampled rank.
lowerWithRank ::
    (GenBackend gen) =>
    ECTAGen gen a ->
    gen (Either ECTAGenError (Integer, a))
lowerWithRank (Transparent (Left err)) = pure $ Left err
lowerWithRank (Transparent (Right static)) = sampleStaticWithRank static
lowerWithRank (Opaque _) = pure $ Left CannotInspectOpaqueGenerator

mapStatic :: (a -> b) -> Static a -> Static b
mapStatic apply static =
    Static
        (staticSupport static)
        (mapOutcomeIndex apply $ staticOutcomes static)

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
            (uniformRankSampler 1 $ const value)
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
            (uniformRankSampler totalOutcomes $ indexedSelect indexed)
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
            ( productRankSampler
                valueCardinality
                (outcomeRankSampler functionOutcomes)
                (outcomeRankSampler valueOutcomes)
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

    splitIndex index = index `divMod` valueCardinality

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
            (frequencyRankSampler alternatives)
        )
  where
    totalWeight = sum $ map fst alternatives
    numbered = zip [0 :: Int ..] alternatives
    totalOutcomes = sum [outcomeCardinality $ staticOutcomes static | (_, static) <- alternatives]
    uniformMass = commonValue $ map branchUniformMass alternatives

    branchUniformMass (weight, static) =
        (fromInteger weight / fromInteger totalWeight *)
            <$> outcomeUniformMass (staticOutcomes static)

    select index = do
        checkIndex totalOutcomes index
        let (branchIndex, weight, static, childIndex) = selectBranch index numbered
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
        let (_, _, static, childIndex) = selectBranch index numbered
         in outcomeValueAt (staticOutcomes static) childIndex

    selectBranch _ [] = error "frequencyStatic: rank outside alternatives"
    selectBranch index ((branchIndex, (weight, static)) : remaining)
        | index < branchCardinality = (branchIndex, weight, static, index)
        | otherwise = selectBranch (index - branchCardinality) remaining
      where
        branchCardinality = outcomeCardinality $ staticOutcomes static

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
        Just _ -> pure $ uniformRankSampler totalOutcomes selectValue
        Nothing -> joinRankSampler groups
    pure $
        OutcomeIndex
            totalOutcomes
            uniformMass
            select
            selectValue
            rankSampler
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
            (leftIndex, rightIndex) = groupIndex `divMod` rightCardinality
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

joinRankSampler ::
    [JoinGroup left right] ->
    Either ECTAGenError (RankSampler (left, right))
joinRankSampler groups = do
    weightedGroups <-
        integerOutcomes
            [ (joinGroupMass group, (offset, group))
            | (offset, group) <- offsetJoinGroups groups
            ]
    plans <- traverse branchPlan weightedGroups
    pure $
        RankSampler $
            frequencyGen
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
  where
    branchPlan (weight, (offset, group)) = do
        leftSampler <- sequenceRankSampler $ joinGroupLeft group
        rightSampler <- sequenceRankSampler $ joinGroupRight group
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

join3KeyedBuckets ::
    (Ord leftKey, Ord rightKey, Ord resultKey) =>
    (centerKey -> (leftKey, rightKey, resultKey)) ->
    Map.Map centerKey (KeyedBucket center) ->
    Map.Map leftKey (KeyedBucket left) ->
    Map.Map rightKey (KeyedBucket right) ->
    Either ECTAGenError (Map.Map resultKey (KeyedBucket (center, left, right)))
join3KeyedBuckets partitionCenter centers lefts rights = do
    components <- traverse buildComponent matchingBuckets
    if null components
        then Left EmptyGenerator
        else do
            unnormalized <- traverse mergeComponents $ groupComponents components
            let totalAcceptedMass = sum $ keyedBucketMass <$> unnormalized
            pure $ fmap (normalizeBucket totalAcceptedMass) unnormalized
  where
    matchingBuckets =
        [ (componentIndex, resultKey, center, left, right)
        | (componentIndex, (centerKey, center)) <-
            zip [0 :: Int ..] $ Map.toAscList centers
        , let (leftKey, rightKey, resultKey) = partitionCenter centerKey
        , Just left <- [Map.lookup leftKey lefts]
        , Just right <- [Map.lookup rightKey rights]
        ]

    buildComponent (componentIndex, resultKey, center, left, right) = do
        joined <-
            join3BucketStatic
                componentIndex
                (keyedBucketStatic center)
                (keyedBucketStatic left)
                (keyedBucketStatic right)
        pure
            ( resultKey
            , keyedBucketMass center
                * keyedBucketMass left
                * keyedBucketMass right
            , joined
            )

    groupComponents =
        foldl'
            ( \grouped (resultKey, mass, static) ->
                Map.insertWith
                    (flip (<>))
                    resultKey
                    [(mass, static)]
                    grouped
            )
            Map.empty

    mergeComponents alternatives = do
        weightedAlternatives <- integerOutcomes alternatives
        pure $
            KeyedBucket
                (sum $ map fst alternatives)
                (frequencyStatic weightedAlternatives)

    normalizeBucket totalAcceptedMass bucket =
        bucket
            { keyedBucketMass =
                keyedBucketMass bucket / totalAcceptedMass
            }

join3BucketStatic ::
    Int ->
    Static center ->
    Static left ->
    Static right ->
    Either ECTAGenError (Static (center, left, right))
join3BucketStatic componentIndex center left right =
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
                        ( product3RankSampler
                            childCardinality
                            rightCardinality
                            (outcomeRankSampler centerOutcomes)
                            (outcomeRankSampler leftOutcomes)
                            (outcomeRankSampler rightOutcomes)
                        )
                    )
  where
    leftKeyTerm = Term (join3LeftKeySymbol componentIndex) []
    rightKeyTerm = Term (join3RightKeySymbol componentIndex) []
    leftKeyNode = singletonNode leftKeyTerm
    rightKeyNode = singletonNode rightKeyTerm
    centerNode =
        Node
            [ Edge
                centerKeyedSymbol
                [leftKeyNode, rightKeyNode, staticSupport center]
            ]
    leftNode =
        Node
            [ Edge
                leftKeyedSymbol
                [leftKeyNode, staticSupport left]
            ]
    rightNode =
        Node
            [ Edge
                rightKeyedSymbol
                [rightKeyNode, staticSupport right]
            ]
    joined =
        reducePartially $
            Node
                [ mkEdge
                    join3Symbol
                    [centerNode, leftNode, rightNode]
                    ( mkEqConstraints
                        [ [path [0, 0], path [1, 0]]
                        , [path [0, 1], path [2, 0]]
                        ]
                    )
                ]
    centerOutcomes = staticOutcomes center
    leftOutcomes = staticOutcomes left
    rightOutcomes = staticOutcomes right
    leftCardinality = outcomeCardinality leftOutcomes
    rightCardinality = outcomeCardinality rightOutcomes
    childCardinality = leftCardinality * rightCardinality
    totalOutcomes = outcomeCardinality centerOutcomes * childCardinality
    uniformMass =
        (\centerMass leftMass rightMass -> centerMass * leftMass * rightMass)
            <$> outcomeUniformMass centerOutcomes
            <*> outcomeUniformMass leftOutcomes
            <*> outcomeUniformMass rightOutcomes

    select index = do
        checkIndex totalOutcomes index
        let (centerIndex, leftIndex, rightIndex) = splitIndex index
        centerOutcome <- outcomeSelect centerOutcomes centerIndex
        leftOutcome <- outcomeSelect leftOutcomes leftIndex
        rightOutcome <- outcomeSelect rightOutcomes rightIndex
        let centerTerm =
                Term
                    centerKeyedSymbol
                    [leftKeyTerm, rightKeyTerm, outcomeTerm centerOutcome]
            leftTerm =
                Term leftKeyedSymbol [leftKeyTerm, outcomeTerm leftOutcome]
            rightTerm =
                Term rightKeyedSymbol [rightKeyTerm, outcomeTerm rightOutcome]
        pure $
            Outcome
                (Term join3Symbol [centerTerm, leftTerm, rightTerm])
                ( outcomeMass centerOutcome
                    * outcomeMass leftOutcome
                    * outcomeMass rightOutcome
                )
                (outcomeValue centerOutcome, outcomeValue leftOutcome, outcomeValue rightOutcome)

    selectValue index =
        let (centerIndex, leftIndex, rightIndex) = splitIndex index
         in ( outcomeValueAt centerOutcomes centerIndex
            , outcomeValueAt leftOutcomes leftIndex
            , outcomeValueAt rightOutcomes rightIndex
            )

    splitIndex index =
        let (centerIndex, childIndex) = index `divMod` childCardinality
            (leftIndex, rightIndex) = childIndex `divMod` rightCardinality
         in (centerIndex, leftIndex, rightIndex)

join3Static ::
    (Ord leftKey, Ord rightKey) =>
    (center -> (leftKey, rightKey)) ->
    (left -> leftKey) ->
    (right -> rightKey) ->
    Static center ->
    Static left ->
    Static right ->
    Either ECTAGenError (Static (center, left, right))
join3Static centerKeys leftKey rightKey center left right = do
    centerEntries <- keyedOutcomes centerKeys center
    leftEntries <- keyedOutcomes leftKey left
    rightEntries <- keyedOutcomes rightKey right
    let centerGroups = groupOutcomes centerEntries
        leftGroups = groupOutcomes leftEntries
        rightGroups = groupOutcomes rightEntries
        shared =
            [ (centerOutcomes, leftOutcomes, rightOutcomes)
            | ((expectedLeft, expectedRight), centerOutcomes) <-
                Map.toAscList centerGroups
            , Just leftOutcomes <- [Map.lookup expectedLeft leftGroups]
            , Just rightOutcomes <- [Map.lookup expectedRight rightGroups]
            ]
    if null shared
        then Left EmptyGenerator
        else
            let groups =
                    [ Join3Group
                        groupIndex
                        (Sequence.fromList centerOutcomes)
                        (Sequence.fromList leftOutcomes)
                        (Sequence.fromList rightOutcomes)
                    | (groupIndex, (centerOutcomes, leftOutcomes, rightOutcomes)) <-
                        zip [0 :: Int ..] shared
                    ]
                centerNode =
                    Node
                        [ Edge
                            centerKeyedSymbol
                            [ join3LeftKeyNode $ join3GroupIndex group
                            , join3RightKeyNode $ join3GroupIndex group
                            , singletonNode $ outcomeTerm outcome
                            ]
                        | group <- groups
                        , outcome <- toList $ join3GroupCenter group
                        ]
                leftNode =
                    Node
                        [ Edge
                            leftKeyedSymbol
                            [ join3LeftKeyNode $ join3GroupIndex group
                            , singletonNode $ outcomeTerm outcome
                            ]
                        | group <- groups
                        , outcome <- toList $ join3GroupLeft group
                        ]
                rightNode =
                    Node
                        [ Edge
                            rightKeyedSymbol
                            [ join3RightKeyNode $ join3GroupIndex group
                            , singletonNode $ outcomeTerm outcome
                            ]
                        | group <- groups
                        , outcome <- toList $ join3GroupRight group
                        ]
                joined =
                    reducePartially $
                        Node
                            [ mkEdge
                                join3Symbol
                                [centerNode, leftNode, rightNode]
                                ( mkEqConstraints
                                    [ [path [0, 0], path [1, 0]]
                                    , [path [0, 1], path [2, 0]]
                                    ]
                                )
                            ]
             in if joined == EmptyNode
                    then Left EmptyGenerator
                    else Static joined <$> join3OutcomeIndex center left right groups

join3OutcomeIndex ::
    Static center ->
    Static left ->
    Static right ->
    [Join3Group center left right] ->
    Either ECTAGenError (OutcomeIndex (center, left, right))
join3OutcomeIndex center left right groups = do
    rankSampler <- case uniformMass of
        Just _ -> pure $ uniformRankSampler totalOutcomes selectValue
        Nothing -> join3RankSampler groups
    pure $
        OutcomeIndex
            totalOutcomes
            uniformMass
            select
            selectValue
            rankSampler
  where
    totalOutcomes = sum $ map join3GroupCardinality groups
    uniformMass = case (outcomeUniformMass $ staticOutcomes center, outcomeUniformMass $ staticOutcomes left, outcomeUniformMass $ staticOutcomes right) of
        (Just _, Just _, Just _) -> Just $ 1 / fromInteger totalOutcomes
        _ -> Nothing
    totalMass = sum $ map join3GroupMass groups

    select index = do
        checkIndex totalOutcomes index
        let (group, centerOutcome, leftOutcome, rightOutcome) = selectTriple index
            leftKeyTerm = Term (join3LeftKeySymbol $ join3GroupIndex group) []
            rightKeyTerm = Term (join3RightKeySymbol $ join3GroupIndex group) []
            centerTerm =
                Term
                    centerKeyedSymbol
                    [leftKeyTerm, rightKeyTerm, outcomeTerm centerOutcome]
            leftTerm =
                Term leftKeyedSymbol [leftKeyTerm, outcomeTerm leftOutcome]
            rightTerm =
                Term rightKeyedSymbol [rightKeyTerm, outcomeTerm rightOutcome]
        pure $
            Outcome
                (Term join3Symbol [centerTerm, leftTerm, rightTerm])
                ( outcomeMass centerOutcome
                    * outcomeMass leftOutcome
                    * outcomeMass rightOutcome
                    / totalMass
                )
                (outcomeValue centerOutcome, outcomeValue leftOutcome, outcomeValue rightOutcome)

    selectValue index =
        let (_, centerOutcome, leftOutcome, rightOutcome) = selectTriple index
         in (outcomeValue centerOutcome, outcomeValue leftOutcome, outcomeValue rightOutcome)

    selectTriple index =
        let (group, groupIndex) = selectJoin3Group index groups
            leftCardinality = toInteger $ Sequence.length $ join3GroupLeft group
            rightCardinality = toInteger $ Sequence.length $ join3GroupRight group
            childCardinality = leftCardinality * rightCardinality
            (centerIndex, childIndex) = groupIndex `divMod` childCardinality
            (leftIndex, rightIndex) = childIndex `divMod` rightCardinality
            centerOutcome = Sequence.index (join3GroupCenter group) $ fromInteger centerIndex
            leftOutcome = Sequence.index (join3GroupLeft group) $ fromInteger leftIndex
            rightOutcome = Sequence.index (join3GroupRight group) $ fromInteger rightIndex
         in (group, centerOutcome, leftOutcome, rightOutcome)

join3GroupCardinality :: Join3Group center left right -> Integer
join3GroupCardinality group =
    toInteger (Sequence.length $ join3GroupCenter group)
        * toInteger (Sequence.length $ join3GroupLeft group)
        * toInteger (Sequence.length $ join3GroupRight group)

join3GroupMass :: Join3Group center left right -> Rational
join3GroupMass group =
    sum (outcomeMass <$> join3GroupCenter group)
        * sum (outcomeMass <$> join3GroupLeft group)
        * sum (outcomeMass <$> join3GroupRight group)

selectJoin3Group ::
    Integer ->
    [Join3Group center left right] ->
    (Join3Group center left right, Integer)
selectJoin3Group _ [] = error "selectJoin3Group: rank outside groups"
selectJoin3Group index (group : remaining)
    | index < groupSize = (group, index)
    | otherwise = selectJoin3Group (index - groupSize) remaining
  where
    groupSize = join3GroupCardinality group

join3RankSampler ::
    [Join3Group center left right] ->
    Either ECTAGenError (RankSampler (center, left, right))
join3RankSampler groups = do
    weightedGroups <-
        integerOutcomes
            [ (join3GroupMass group, (offset, group))
            | (offset, group) <- offsetJoin3Groups groups
            ]
    plans <- traverse branchPlan weightedGroups
    pure $
        RankSampler $
            frequencyGen
                [ ( weight
                  , liftA3
                        ( \(centerIndex, centerValue) (leftIndex, leftValue) (rightIndex, rightValue) ->
                            ( offset
                                + centerIndex * childCardinality
                                + leftIndex * rightCardinality
                                + rightIndex
                            , (centerValue, leftValue, rightValue)
                            )
                        )
                        (runRankSampler centerSampler)
                        (runRankSampler leftSampler)
                        (runRankSampler rightSampler)
                  )
                | ( weight
                    , offset
                    , childCardinality
                    , rightCardinality
                    , centerSampler
                    , leftSampler
                    , rightSampler
                    ) <-
                    plans
                ]
  where
    branchPlan (weight, (offset, group)) = do
        centerSampler <- sequenceRankSampler $ join3GroupCenter group
        leftSampler <- sequenceRankSampler $ join3GroupLeft group
        rightSampler <- sequenceRankSampler $ join3GroupRight group
        let leftCardinality = toInteger $ Sequence.length $ join3GroupLeft group
            rightCardinality = toInteger $ Sequence.length $ join3GroupRight group
            childCardinality = leftCardinality * rightCardinality
        pure
            ( weight
            , offset
            , childCardinality
            , rightCardinality
            , centerSampler
            , leftSampler
            , rightSampler
            )

offsetJoin3Groups ::
    [Join3Group center left right] ->
    [(Integer, Join3Group center left right)]
offsetJoin3Groups = go 0
  where
    go _ [] = []
    go offset (group : remaining) =
        (offset, group) : go (offset + join3GroupCardinality group) remaining

sequenceRankSampler :: Seq (Outcome a) -> Either ECTAGenError (RankSampler a)
sequenceRankSampler outcomes
    | Just _ <- commonValue $ Just . outcomeMass <$> toList outcomes =
        pure $ uniformRankSampler totalOutcomes selectValue
    | otherwise = do
        weightedRanks <-
            integerOutcomes
                [ (outcomeMass outcome, (index, outcomeValue outcome))
                | (index, outcome) <- zip [0 ..] $ toList outcomes
                ]
        pure $ RankSampler $ frequencyGen [(weight, pure rankedValue) | (weight, rankedValue) <- weightedRanks]
  where
    totalOutcomes = toInteger $ Sequence.length outcomes
    selectValue = outcomeValue . Sequence.index outcomes . fromInteger

keyNode :: Int -> Node
keyNode index = Node [Edge (keySymbol index) []]

join3LeftKeyNode :: Int -> Node
join3LeftKeyNode index = Node [Edge (join3LeftKeySymbol index) []]

join3RightKeyNode :: Int -> Node
join3RightKeyNode index = Node [Edge (join3RightKeySymbol index) []]

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
sampleStatic static = fmap (fmap snd) $ sampleStaticWithRank static

sampleStaticWithRank ::
    (GenBackend gen) =>
    Static a ->
    gen (Either ECTAGenError (Integer, a))
sampleStaticWithRank static =
    Right <$> runRankSampler (outcomeRankSampler $ staticOutcomes static)

uniformRankSampler :: Integer -> (Integer -> a) -> RankSampler a
uniformRankSampler 1 valueAt = RankSampler $ pure (0, valueAt 0)
uniformRankSampler totalOutcomes valueAt =
    RankSampler $
        (\index -> (index, valueAt index)) <$> selectInteger totalOutcomes

productRankSampler :: Integer -> RankSampler (a -> b) -> RankSampler a -> RankSampler b
productRankSampler rightCardinality leftSampler rightSampler =
    RankSampler $
        liftA2
            ( \(leftIndex, apply) (rightIndex, value) ->
                (leftIndex * rightCardinality + rightIndex, apply value)
            )
            (runRankSampler leftSampler)
            (runRankSampler rightSampler)

product3RankSampler ::
    Integer ->
    Integer ->
    RankSampler center ->
    RankSampler left ->
    RankSampler right ->
    RankSampler (center, left, right)
product3RankSampler childCardinality rightCardinality centerSampler leftSampler rightSampler =
    RankSampler $
        liftA3
            ( \(centerIndex, centerValue) (leftIndex, leftValue) (rightIndex, rightValue) ->
                ( centerIndex * childCardinality
                    + leftIndex * rightCardinality
                    + rightIndex
                , (centerValue, leftValue, rightValue)
                )
            )
            (runRankSampler centerSampler)
            (runRankSampler leftSampler)
            (runRankSampler rightSampler)

frequencyRankSampler :: [(Integer, Static a)] -> RankSampler a
frequencyRankSampler alternatives =
    RankSampler $
        frequencyGen
            [ ( weight
              , (\(rank, value) -> (offset + rank, value))
                    <$> runRankSampler (outcomeRankSampler $ staticOutcomes static)
              )
            | (offset, (weight, static)) <- offsetAlternatives alternatives
            ]

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
mapOutcomeIndex apply outcomes =
    OutcomeIndex
        (outcomeCardinality outcomes)
        (outcomeUniformMass outcomes)
        (\index -> mapOutcome apply <$> outcomeSelect outcomes index)
        (apply . outcomeValueAt outcomes)
        ( RankSampler $
            (\(rank, value) -> (rank, apply value))
                <$> runRankSampler (outcomeRankSampler outcomes)
        )

mapOutcome :: (a -> b) -> Outcome a -> Outcome b
mapOutcome apply outcome =
    Outcome
        (outcomeTerm outcome)
        (outcomeMass outcome)
        (apply $ outcomeValue outcome)

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

pureSymbol, applySymbol, joinSymbol, join3Symbol, centerKeyedSymbol, leftKeyedSymbol, rightKeyedSymbol :: Symbol
pureSymbol = "$ecta-gen/pure"
applySymbol = "$ecta-gen/apply"
joinSymbol = "$ecta-gen/join"
join3Symbol = "$ecta-gen/join3"
centerKeyedSymbol = "$ecta-gen/center-keyed"
leftKeyedSymbol = "$ecta-gen/left-keyed"
rightKeyedSymbol = "$ecta-gen/right-keyed"

indexedSymbol :: Integer -> Symbol
indexedSymbol index = Symbol $ Text.pack $ "$ecta-gen/index/" <> show index

frequencySymbol :: Int -> Symbol
frequencySymbol index = Symbol $ Text.pack $ "$ecta-gen/frequency/" <> show index

keySymbol :: Int -> Symbol
keySymbol index = Symbol $ Text.pack $ "$ecta-gen/key/" <> show index

join3LeftKeySymbol :: Int -> Symbol
join3LeftKeySymbol index =
    Symbol $ Text.pack $ "$ecta-gen/join3-left-key/" <> show index

join3RightKeySymbol :: Int -> Symbol
join3RightKeySymbol index =
    Symbol $ Text.pack $ "$ecta-gen/join3-right-key/" <> show index
