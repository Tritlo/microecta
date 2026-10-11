{- | Joins that correlate two languages, or one operation and its arguments.

A join encodes membership with ECTA equality constraints and counts the
matched group products, so it visits no pair of members of the joined language
while it is built. The two-way joins still enumerate the outcomes of both
operand languages once. The n-way bucket join enumerates none.
-}
module Data.CFTA.Gen.Internal.Join (
    joinStatic,
    relateStatic,
    joinNBucketStatic,
    recursiveJoin,
) where

import Data.CFTA.Constraint (equalityConstraint)
import qualified Data.CFTA.Term as Term
import Data.Foldable (toList)
import Data.Hashable (Hashable)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Sequence
import Data.Typeable (Typeable)

import Data.CFTA.Equality (Edge (Edge), Node (Node), mkEdge, numNestedMu, reducePartially)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Gen.Error (GenError (..))
import Data.CFTA.Gen.Internal.Bucket
import Data.CFTA.Gen.Internal.Chain
import Data.CFTA.Gen.Internal.Inspection
import Data.CFTA.Gen.Internal.Recursive
import Data.CFTA.Gen.Internal.Static
import Data.CFTA.Gen.Internal.Support
import Data.CFTA.Gen.Label (ComponentIndex, GroupIndex (..), Label (..))
import Data.CFTA.Index (
    ArgumentIndex (..),
    Cardinality,
    ClassRank (..),
    Rank (..),
    RankOffset (..),
    Size,
    everyRank,
    nextOffset,
    offsetRank,
    pairRank,
    rebaseRank,
    splitRank,
 )
import Data.CFTA.Path (path)
import Data.CFTA.Ranked.Internal.Decoder (Plan (..), RankedValue (..), SizeClass (..))
import Data.CFTA.Ranked.Internal.Sampler
import Data.CFTA.Ranked.Internal.Shrink (planMemberSize)
import Data.CFTA.Ranked.Internal.Size (countAtSize, sizeClassCounts, sizeIndex)

-- | One compatible key-pair bucket used to count and unrank a conditioned product.
data JoinGroup symbol left right = JoinGroup
    { joinGroupIndex :: !GroupIndex
    , joinGroupLeft :: !(Seq (Outcome symbol left))
    , joinGroupRight :: !(Seq (Outcome symbol right))
    , joinGroupLeftWeights :: !(Seq Rational)
    -- ^ The weight of each left outcome inside its size class, as 'staticSampling' gives it.
    , joinGroupRightWeights :: !(Seq Rational)
    -- ^ The weight of each right outcome inside its size class.
    , joinGroupLeftSizes :: !(Seq Size)
    -- ^ The size of each left outcome. The left outcomes are in size order.
    , joinGroupRightSizes :: !(Seq Size)
    -- ^ The size of each right outcome. The right outcomes are in size order.
    }

-- | One side of a matched group: its outcomes in size order, with the weight and the size of each.
data JoinSide symbol a = JoinSide !(Seq (Outcome symbol a)) !(Seq Rational) !(Seq Size)

-- | Join two languages on equal projected keys with one ECTA equality constraint.
joinStatic ::
    (Ord key, Hashable symbol, Typeable symbol) =>
    (left -> key) ->
    (right -> key) ->
    Static symbol left ->
    Static symbol right ->
    Either GenError (Static symbol (left, right))
joinStatic leftKey rightKey left right = do
    leftEntries <- keyedOutcomes leftKey left
    rightEntries <- keyedOutcomes rightKey right
    -- Only the shared keys become join sides.
    let shared =
            Map.intersectionWith
                (\lefts rights -> (joinSide lefts, joinSide rights))
                (groupOutcomes leftEntries)
                (groupOutcomes rightEntries)
    joinGroupedStatic left right $ map snd $ Map.toAscList shared

-- | Join two languages on a relation between their projected keys.
relateStatic ::
    (Ord leftKey, Ord rightKey, Hashable symbol, Typeable symbol) =>
    (left -> leftKey) ->
    (right -> rightKey) ->
    (leftKey -> rightKey -> Bool) ->
    Static symbol left ->
    Static symbol right ->
    Either GenError (Static symbol (left, right))
relateStatic leftKey rightKey relation left right = do
    leftEntries <- keyedOutcomes leftKey left
    rightEntries <- keyedOutcomes rightKey right
    let leftGroups = joinSide <$> groupOutcomes leftEntries
        rightGroups = joinSide <$> groupOutcomes rightEntries
        related =
            [ (leftSide, rightSide)
            | (leftGroupKey, leftSide) <- Map.toAscList leftGroups
            , (rightGroupKey, rightSide) <- Map.toAscList rightGroups
            , relation leftGroupKey rightGroupKey
            ]
    joinGroupedStatic left right related

{- | Compile selected group products with one equality witness per product.
Each side of a group is in size order, as 'joinSide' gives it.
-}
joinGroupedStatic ::
    (Hashable symbol, Typeable symbol) =>
    Static symbol left ->
    Static symbol right ->
    [(JoinSide symbol left, JoinSide symbol right)] ->
    Either GenError (Static symbol (left, right))
joinGroupedStatic left right related =
    if null related
        then Left EmptyGenerator
        else
            let groups =
                    [ JoinGroup groupIndex leftOutcomes rightOutcomes leftWeights rightWeights leftSizes rightSizes
                    | (groupIndex, (JoinSide leftOutcomes leftWeights leftSizes, JoinSide rightOutcomes rightWeights rightSizes)) <-
                        zip [0 :: GroupIndex ..] related
                    ]
                leftNode =
                    Node
                        [ Edge
                            LeftKeyed
                            [ keyNode $ joinGroupIndex group
                            , singletonNode $ outcomeTerm outcome
                            ]
                        | group <- groups
                        , outcome <- toList $ joinGroupLeft group
                        ]
                rightNode =
                    Node
                        [ Edge
                            RightKeyed
                            [ keyNode $ joinGroupIndex group
                            , singletonNode $ outcomeTerm outcome
                            ]
                        | group <- groups
                        , outcome <- toList $ joinGroupRight group
                        ]
                joined =
                    reducePartially $
                        Node
                            [mkEdge Join [leftNode, rightNode] keysEqual]
                -- The private join labels flatten into the roots of the two sides.
                sideRootCount terms = commonRootCount $ map (RootCount . termRootCount) terms
                rootCount =
                    addRootCounts
                        (sideRootCount [outcomeTerm outcome | group <- groups, outcome <- toList $ joinGroupLeft group])
                        (sideRootCount [outcomeTerm outcome | group <- groups, outcome <- toList $ joinGroupRight group])
             in -- Every group came from two non-empty outcome buckets. Keep
                -- support reduction lazy; the outcome index already proves
                -- that the joined language is non-empty.
                (\outcomes -> Static joined outcomes False (inspectionJoined groups) rootCount)
                    <$> joinOutcomeIndex left right groups
  where
    -- The two sides of a pair have the same group key.
    keysEqual = equalityConstraint $ mkEqConstraints [[path [0, 0], path [1, 0]]]
    inspectionJoined groups =
        Inspection Nothing $
            Node
                [ mkEdge
                    (plainSymbol Join)
                    [ side LeftKeyed (fmap outcomeInspection . joinGroupLeft)
                    , side RightKeyed (fmap outcomeInspection . joinGroupRight)
                    ]
                    keysEqual
                ]
      where
        side symbol outcomes =
            Node
                [ Edge
                    (plainSymbol symbol)
                    [ singletonNode $ Term.Node (plainSymbol $ Group $ joinGroupIndex group) []
                    , singletonNode outcome
                    ]
                | group <- groups
                , outcome <- toList $ outcomes group
                ]

{- | One side of a matched group from the outcomes of one key, in size order.
The sort is stable, so the outcomes of one size keep their rank order.
-}
joinSide :: Seq (Size, Rational, Outcome symbol a) -> JoinSide symbol a
joinSide entries =
    JoinSide
        ((\(_, _, outcome) -> outcome) <$> ordered)
        ((\(_, weight, _) -> weight) <$> ordered)
        (sizeOf <$> ordered)
  where
    sizes = sizeOf <$> entries
    ordered
        | and $ Sequence.zipWith (<=) sizes (Sequence.drop 1 sizes) = entries
        | otherwise = Sequence.sortOn sizeOf entries
    sizeOf (size, _, _) = size

{- | Enumerate a language and pair every outcome with its projected key, the
size of its rank, and the weight of its rank inside its size class.
-}
keyedOutcomes ::
    (value -> key) ->
    Static symbol value ->
    Either GenError [(key, (Size, Rational, Outcome symbol value))]
keyedOutcomes key static = do
    weighted <- enumerateWeighted static
    pure
        [ (key $ outcomeValue outcome, (sizeOf rank, weight, outcome))
        | (rank, (weight, outcome)) <- zip (everyRank $ toEnum $ length weighted) weighted
        ]
  where
    outcomes = staticOutcomes static
    -- A language of one size class needs no plan walk for each rank.
    sizeOf = case sizeClassCounts $ outcomeSizeIndex outcomes of
        [(size, _)] -> const size
        _ -> planMemberSize $ outcomePlan outcomes

-- | Count, select, and sample the matched groups of a two-way join.
joinOutcomeIndex ::
    (Eq symbol) =>
    Static symbol left ->
    Static symbol right ->
    [JoinGroup symbol left right] ->
    Either GenError (OutcomeIndex symbol (left, right))
joinOutcomeIndex left right groups = do
    rankSampler <- case uniformMass of
        Just _ -> pure $ uniformSampler totalOutcomes selectValue
        Nothing -> joinSampler groups
    -- A pair has the sizes of its two sides added, as a product has. When a
    -- side has a non-uniform atomic choice, the pairs of one size class are
    -- sampled in proportion to the product of the weights of their two sides,
    -- as the size class of a product is.
    sizeSampling <-
        if isJust (snd $ staticSampling left) || isJust (snd $ staticSampling right)
            then do
                samplings <- sequence $ zipWith3 groupSampling groups sidePlans pairWeights
                -- Build the sampler of each size class once.
                let sampling = choiceMassSampleIndex samplings
                    bySize = Map.fromSet (samplerAtSize sampling) (Map.keysSet classWeights)
                pure $ Just (SampleIndex $ \size -> Map.findWithDefault (samplerAtSize sampling size) size bySize, Right . weight)
            else pure Nothing
    pure $
        ( mkOutcomeIndex
            totalOutcomes
            uniformMass
            select
            (leafRanks pairRanks)
            selectValue
            rankSampler
            plan
        )
            { outcomeSizeSampling = sizeSampling
            }
  where
    plan = PlanChoice [(joinGroupCardinality group, groupPlan) | (group, (_, _, groupPlan)) <- zip groups sidePlans]
    -- The plans of the two sides of each group, and of the group.
    sidePlans =
        [ (leftPlan, rightPlan, PlanAp (toEnum $ Sequence.length $ joinGroupRight group) (PlanMap (,) leftPlan) rightPlan)
        | group <- groups
        , let leftPlan = sidePlan (joinGroupLeftSizes group) (joinGroupLeft group)
              rightPlan = sidePlan (joinGroupRightSizes group) (joinGroupRight group)
        ]

    -- The size index, the weight at each size, and the weighted sampler of one group.
    groupSampling group (leftPlan, rightPlan, groupPlan) weights = do
        (leftMass, leftSampling) <- weightedSide (joinGroupLeftSizes group) (joinGroupLeftWeights group) (joinGroupLeft group)
        (rightMass, rightSampling) <-
            weightedSide (joinGroupRightSizes group) (joinGroupRightWeights group) (joinGroupRight group)
        pure
            ( sizeIndex groupPlan
            , \size -> Map.findWithDefault 0 size weights
            , productMassSampleIndex
                (sizeIndex $ PlanMap (,) leftPlan)
                leftMass
                (mapSampleIndex (,) leftSampling)
                (sizeIndex rightPlan)
                rightMass
                rightSampling
            )
    -- The weight of the pairs of each size, for each group and for all groups.
    pairWeights = map groupPairWeights groups
    classWeights = Map.unionsWith (+) pairWeights
    groupPairWeights group =
        Map.fromListWith
            (+)
            [ (leftSize + rightSize, leftWeight * rightWeight)
            | (leftSize, leftWeight) <- sideWeights (joinGroupLeftSizes group) (joinGroupLeftWeights group)
            , (rightSize, rightWeight) <- sideWeights (joinGroupRightSizes group) (joinGroupRightWeights group)
            ]
    sideWeights sizes weights = Map.toList $ Map.fromListWith (+) $ zip (toList sizes) (toList weights)
    -- The weight of a pair in its size class: the product of the weights of
    -- its sides, scaled so that the weights of a size class add up to its count.
    weight index =
        let (group, leftIndex, rightIndex) = selectIndexes index
            size = Sequence.index (joinGroupLeftSizes group) leftIndex + Sequence.index (joinGroupRightSizes group) rightIndex
         in toRational (countAtSize joinedSizes size)
                * Sequence.index (joinGroupLeftWeights group) leftIndex
                * Sequence.index (joinGroupRightWeights group) rightIndex
                / Map.findWithDefault 0 size classWeights
    joinedSizes = sizeIndex plan

    totalOutcomes = sum $ map joinGroupCardinality groups
    uniformMass = case (outcomeUniformMass $ staticOutcomes left, outcomeUniformMass $ staticOutcomes right) of
        (Just _, Just _) -> Just $ 1 / toRational totalOutcomes
        _ -> Nothing
    totalMass = sum $ map joinGroupMass groups

    select index = do
        checkIndex totalOutcomes index
        let (group, leftOutcome, rightOutcome) = selectPair index
            keyTerm = Term.Node (Group $ joinGroupIndex group) []
            leftTerm =
                Term.Node LeftKeyed [keyTerm, outcomeTerm leftOutcome]
            rightTerm =
                Term.Node RightKeyed [keyTerm, outcomeTerm rightOutcome]
        pure $
            Outcome
                (Term.Node Join [leftTerm, rightTerm])
                ( outcomeMass leftOutcome
                    * outcomeMass rightOutcome
                    / totalMass
                )
                (outcomeValue leftOutcome, outcomeValue rightOutcome)
                ( Term.Node
                    (plainSymbol Join)
                    [ Term.Node (plainSymbol LeftKeyed) [fmap plainSymbol keyTerm, outcomeInspection leftOutcome]
                    , Term.Node (plainSymbol RightKeyed) [fmap plainSymbol keyTerm, outcomeInspection rightOutcome]
                    ]
                )

    selectValue index =
        let (_, leftOutcome, rightOutcome) = selectPair index
         in (outcomeValue leftOutcome, outcomeValue rightOutcome)

    -- The key of a pair names its group, and each side is one enumerated outcome of its group.
    pairRanks term = case term of
        Term.Node
            Join
            [ Term.Node LeftKeyed [Term.Node (Group (GroupIndex key)) [], leftTerm]
                , Term.Node RightKeyed [Term.Node (Group (GroupIndex key')) [], rightTerm]
                ]
                | key == key' ->
                    [ CheckedRank (offsetRank offset $ pairRank (toEnum $ Sequence.length $ joinGroupRight group) leftIndex rightIndex) True
                    | Just (offset, group) <- [IntMap.lookup key groupsByIndex]
                    , leftIndex <- positionsIn (joinGroupLeft group) leftTerm
                    , rightIndex <- positionsIn (joinGroupRight group) rightTerm
                    ]
        _ -> []
      where
        positionsIn outcomes wanted = [index | (index, outcome) <- zip [0 ..] $ toList outcomes, outcomeTerm outcome == wanted]
    groupsByIndex =
        IntMap.fromList
            [(index, entry) | entry@(_, group) <- offsetJoinGroups groups, let GroupIndex index = joinGroupIndex group]
    groupsByOffset = joinGroupsByOffset groups
    selectIndexes index =
        let (group, groupIndex) = selectJoinGroup index groupsByOffset
            (leftIndex, rightIndex) = splitRank (toEnum $ Sequence.length $ joinGroupRight group) groupIndex
         in (group, fromEnum leftIndex, fromEnum rightIndex)
    selectPair index =
        let (group, leftIndex, rightIndex) = selectIndexes index
         in (group, Sequence.index (joinGroupLeft group) leftIndex, Sequence.index (joinGroupRight group) rightIndex)

{- | The plan of one side of a join group whose outcomes are in size order:
one size class for each size, so a pair has the sizes of its two sides. A
side of atoms of size one keeps its plain plan.
-}
sidePlan :: Seq Size -> Seq (Outcome symbol a) -> Plan a
sidePlan sizes outcomes
    | all (== 1) sizes = seqPlan outcomes
    | otherwise =
        PlanSized
            [ SizeClass size (toEnum count) (\(ClassRank position) -> valueAt $ start + fromInteger position) (valueAt . (start +))
            | (size, start, count) <- sizeRuns sizes
            ]
  where
    valueAt = outcomeValue . Sequence.index outcomes

{- | Sample the outcomes of one size of a join side in proportion to their
weights, with the weight of each size. The side is in size order, so the rank
of an outcome in its size class is its position after the first outcome of
that size.
-}
weightedSide ::
    Seq Size ->
    Seq Rational ->
    Seq (Outcome symbol a) ->
    Either GenError (Size -> Rational, SampleIndex a)
weightedSide sizes weights outcomes = do
    samplers <- traverse classSampler $ sizeRuns sizes
    let bySize = Map.fromList samplers
    pure
        ( \size -> Map.findWithDefault 0 size masses
        , SampleIndex $ \size -> Map.findWithDefault (noClass size) size bySize
        )
  where
    masses = Map.fromListWith (+) $ zip (toList sizes) (toList weights)
    classSampler (size, start, count) =
        (size,) <$> sequenceSampler (Sequence.zipWith withMass (slice start count weights) (slice start count outcomes))
    slice start count = Sequence.take count . Sequence.drop start
    withMass mass outcome = outcome{outcomeMass = mass}
    noClass size =
        error $
            "cfta-generator bug in Data.CFTA.Gen.Internal.Join.weightedSide: no outcome of size "
                <> show size

-- | The runs of one size in sizes in order: each size, its first position, and its count.
sizeRuns :: Seq Size -> [(Size, Int, Int)]
sizeRuns = go 0 . toList
  where
    go _ [] = []
    go start (size : rest) =
        let (same, others) = span (== size) rest
            count = 1 + length same
         in (size, start, count) : go (start + count) others

-- | Number of pairs in one matched group.
joinGroupCardinality :: JoinGroup symbol left right -> Cardinality
joinGroupCardinality group =
    toEnum (Sequence.length $ joinGroupLeft group)
        * toEnum (Sequence.length $ joinGroupRight group)

-- | Probability mass of one matched group.
joinGroupMass :: JoinGroup symbol left right -> Rational
joinGroupMass group =
    sum (outcomeMass <$> joinGroupLeft group)
        * sum (outcomeMass <$> joinGroupRight group)

-- | The matched groups with pairs, by the first rank of each.
joinGroupsByOffset :: [JoinGroup symbol left right] -> Map.Map RankOffset (JoinGroup symbol left right)
joinGroupsByOffset groups = Map.fromList [entry | entry@(_, group) <- offsetJoinGroups groups, joinGroupCardinality group > 0]

-- | Find the group holding a rank, with the rank rebased into it.
selectJoinGroup ::
    Rank ->
    Map.Map RankOffset (JoinGroup symbol left right) ->
    (JoinGroup symbol left right, Rank)
selectJoinGroup index@(Rank rank) groups = case Map.lookupLE (RankOffset rank) groups of
    Just (offset, group) -> (group, rebaseRank offset index)
    Nothing ->
        error
            "cfta-generator bug in Data.CFTA.Gen.Internal.Join.selectJoinGroup: \
            \rank outside the matched groups"

-- | Sample a weighted two-way join, group by group.
joinSampler ::
    [JoinGroup symbol left right] ->
    Either GenError (Sampler (left, right))
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
                        ( \(RankedValue leftIndex leftValue) (RankedValue rightIndex rightValue) ->
                            RankedValue (offsetRank offset $ pairRank rightCardinality leftIndex rightIndex) (leftValue, rightValue)
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
        let rightCardinality = toEnum $ Sequence.length $ joinGroupRight group
        pure (weight, offset, rightCardinality, leftSampler, rightSampler)

-- | Pair every join group with its cumulative rank offset.
offsetJoinGroups :: [JoinGroup symbol left right] -> [(RankOffset, JoinGroup symbol left right)]
offsetJoinGroups = go 0
  where
    go _ [] = []
    go offset (group : remaining) =
        (offset, group) : go (nextOffset offset $ joinGroupCardinality group) remaining

-- | Join one operation group with its argument groups in one ECTA edge, with one equality constraint per argument.
joinNBucketStatic ::
    (Hashable symbol, Typeable symbol) =>
    ComponentIndex ->
    Static symbol operation ->
    ArgStatics symbol operation result ->
    Static symbol result
joinNBucketStatic componentIndex operation arguments =
    -- This cannot fail: signature lookup supplies one non-empty bucket per
    -- component, so the outcome product proves non-emptiness without forcing
    -- support reduction.
    Static
        joined
        ( mkOutcomeIndex
            totalOutcomes
            uniformMass
            select
            joinRanks
            selectValue
            rankSampler
            (chainPlan (outcomePlan operationOutcomes) arguments)
        )
            { outcomeSizeSampling = outcomeSizeSampling $ staticOutcomes $ applyChain operation arguments
            }
        False
        (joinInspection componentIndex (staticInspection operation) $ chainInspections arguments)
        -- The private join labels flatten into the roots of the operation and the arguments.
        (foldr addRootCounts (RootCount 0) (staticRootCount operation : chainRootCounts arguments))
  where
    keyTerms =
        [ Term.Node (ArgKey componentIndex position) []
        | position <- map ArgumentIndex [0 .. chainLength arguments - 1]
        ]
    unreduced = joinNode componentIndex (staticSupport operation) (chainSupports arguments)
    -- A bounded member of a recursive family keeps its recursive support.
    -- Propagating constraints through a recursive node is not sound, so
    -- such a join stays unreduced, as 'recursiveJoin' does.
    joined
        | numNestedMu unreduced > 0 = unreduced
        | otherwise = reducePartially unreduced
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
        let (operationIndex, argumentIndex) = splitRank argumentsCardinality index
        operationOutcome <- outcomeSelect operationOutcomes operationIndex
        (argumentTerms, argumentInspections, argumentsMass, value) <-
            selectChain (outcomeValue operationOutcome) arguments keyTerms argumentIndex
        let operationTerm =
                Term.Node CenterKeyed (outcomeTerm operationOutcome : keyTerms)
        pure $
            Outcome
                (Term.Node JoinN (operationTerm : argumentTerms))
                (outcomeMass operationOutcome * argumentsMass)
                value
                ( Term.Node (plainSymbol JoinN) $
                    Term.Node
                        (plainSymbol CenterKeyed)
                        ( outcomeInspection operationOutcome
                            : zipWith
                                (\term inspection -> fmap (\symbol -> InspectionSymbol symbol $ inspectionName inspection) term)
                                keyTerms
                                (chainInspections arguments)
                        )
                        : argumentInspections
                )

    selectValue index =
        let (operationIndex, argumentIndex) = splitRank argumentsCardinality index
         in decodeArguments (outcomeValueAt operationOutcomes operationIndex) argumentIndex

    -- A node label replaces the private n-way join label and keeps its children.
    joinRanks view = case view of
        WholeTerm (Term.Node JoinN children) -> childrenRanks children
        WholeTerm _ -> []
        LabelledView children -> childrenRanks children
        SpineView (term :<| Empty) -> joinRanks $ WholeTerm term
        SpineView _ -> []
      where
        childrenRanks (Term.Node CenterKeyed centre : argumentTerms) = case centre of
            operationTerm : keys ->
                let keysChecked = joinKeysMatch componentIndex keys argumentTerms
                 in [ CheckedRank
                        (pairRank argumentsCardinality operationRank argumentRank)
                        (operationChecked && argumentsChecked && keysChecked)
                    | CheckedRank operationRank operationChecked <- outcomeRanks operationOutcomes $ WholeTerm operationTerm
                    , CheckedRank argumentRank argumentsChecked <- chainRanks arguments argumentTerms
                    ]
            [] -> []
        childrenRanks _ = []

{- | Apply an operation to every argument of a chain with 'applyStatic'.

The plan of the result is 'chainPlan', so its ranks are the ranks of the
join. The join reads only the sampler and the weight of each size class from
it.
-}
applyChain ::
    (Hashable symbol, Typeable symbol) =>
    Static symbol operation ->
    ArgStatics symbol operation result ->
    Static symbol result
applyChain static ChainNil = static
applyChain static (ChainCons argument rest) = applyChain (applyStatic static argument) rest

{- | One joined component of a recursive keyed application.

Sizes match the finite join, and the choices come in the same order: the
operation is one choice and the arguments follow it left to right. The ranks
are size-major, not the mixed-radix ranks of the finite join; see
'Data.CFTA.Gen.Internal.Grouped.applyRecursive'. The joined edge is not reduced,
since propagating constraints through a recursive node is not sound.
-}
recursiveJoin ::
    (Hashable symbol, Typeable symbol) =>
    ComponentIndex ->
    KeyedRecursive symbol operation ->
    ArgChain (KeyedRecursive symbol) operation result ->
    KeyedRecursive symbol result
recursiveJoin componentIndex operation arguments =
    KeyedRecursive
        ( Recursive
            (joinNode componentIndex (recursiveSupport operationRecursive) (recursiveSupports arguments))
            joinedIndex
            joinedSampling
            joinedWeighted
            (recursiveTerm operationRecursive >>= \terms -> recursiveChainTerms componentIndex operationIndex terms arguments)
            (joinInspection componentIndex (recursiveInspection operationRecursive) $ recursiveInspections arguments)
        )
        joinedMasses
        joinedMassWeighted
  where
    operationRecursive = keyedRecursiveLanguage operation
    operationIndex = recursiveIndex operationRecursive
    -- Lazy: the knot of a recursive family reads the index before the sampler.
    ~(joinedIndex, joinedMasses, joinedSampling) =
        recursiveChainProduct
            operationIndex
            (keyedRecursiveMasses operation)
            (recursiveSampling operationRecursive)
            arguments
    joinedWeighted =
        recursiveWeighted operationRecursive
            || recursiveChainWeighted arguments
            || joinedMassWeighted
    joinedMassWeighted =
        keyedRecursiveMassWeighted operation
            || recursiveChainMassWeighted arguments
