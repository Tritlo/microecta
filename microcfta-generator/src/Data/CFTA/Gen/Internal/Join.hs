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
import Data.Foldable (toList)
import Data.Hashable (Hashable)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import Data.Sequence (Seq)
import qualified Data.Sequence as Sequence
import qualified Data.Tree as Tree
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
    Rank (..),
    RankOffset (..),
    nextOffset,
    offsetRank,
    pairRank,
    rebaseRank,
    splitRank,
 )
import Data.CFTA.Path (path)
import Data.CFTA.Ranked.Internal.Decoder (Plan (..), RankedValue (..))
import Data.CFTA.Ranked.Internal.Sampler

-- | One compatible key-pair bucket used to count and unrank a conditioned product.
data JoinGroup symbol left right = JoinGroup
    { joinGroupIndex :: !GroupIndex
    , joinGroupLeft :: !(Seq (Outcome symbol left))
    , joinGroupRight :: !(Seq (Outcome symbol right))
    , joinGroupLeftWeights :: !(Seq Rational)
    -- ^ The weight of each left outcome inside its size class, as 'staticSampling' gives it.
    , joinGroupRightWeights :: !(Seq Rational)
    -- ^ The weight of each right outcome inside its size class.
    }

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
    let shared =
            Map.intersectionWith
                (,)
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
    let leftGroups = groupOutcomes leftEntries
        rightGroups = groupOutcomes rightEntries
        related =
            [ (leftOutcomes, rightOutcomes)
            | (leftGroupKey, leftOutcomes) <- Map.toAscList leftGroups
            , (rightGroupKey, rightOutcomes) <- Map.toAscList rightGroups
            , relation leftGroupKey rightGroupKey
            ]
    joinGroupedStatic left right related

-- | Compile selected group products with one equality witness per product.
joinGroupedStatic ::
    (Hashable symbol, Typeable symbol) =>
    Static symbol left ->
    Static symbol right ->
    [(Seq (Rational, Outcome symbol left), Seq (Rational, Outcome symbol right))] ->
    Either GenError (Static symbol (left, right))
joinGroupedStatic left right related =
    if null related
        then Left EmptyGenerator
        else
            let groups =
                    [ JoinGroup
                        groupIndex
                        (fmap snd leftOutcomes)
                        (fmap snd rightOutcomes)
                        (fmap fst leftOutcomes)
                        (fmap fst rightOutcomes)
                    | (groupIndex, (leftOutcomes, rightOutcomes)) <-
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
                            [ mkEdge
                                Join
                                [leftNode, rightNode]
                                (equalityConstraint $ mkEqConstraints [[path [0, 0], path [1, 0]]])
                            ]
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
    inspectionJoined groups =
        Inspection Nothing $
            Node
                [ mkEdge
                    (plainSymbol Join)
                    [ side LeftKeyed (fmap outcomeInspection . joinGroupLeft)
                    , side RightKeyed (fmap outcomeInspection . joinGroupRight)
                    ]
                    (equalityConstraint $ mkEqConstraints [[path [0, 0], path [1, 0]]])
                ]
      where
        side symbol outcomes =
            Node
                [ Edge
                    (plainSymbol symbol)
                    [ singletonNode $ Tree.Node (plainSymbol $ Group $ joinGroupIndex group) []
                    , singletonNode outcome
                    ]
                | group <- groups
                , outcome <- toList $ outcomes group
                ]

{- | Enumerate a language and pair every outcome with its projected key and
the weight of its rank inside its size class.
-}
keyedOutcomes ::
    (value -> key) ->
    Static symbol value ->
    Either GenError [(key, (Rational, Outcome symbol value))]
keyedOutcomes key static =
    map (\entry@(_, outcome) -> (key $ outcomeValue outcome, entry))
        <$> enumerateWeighted static

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
    -- Every pair has size two. When a side has a non-uniform atomic choice,
    -- the pairs of that size class are sampled in proportion to the product
    -- of the weights of their two sides, as the size class of a product is.
    sizeSampling <-
        if isJust (snd $ staticSampling left) || isJust (snd $ staticSampling right)
            then do
                sampler <- joinSampler weightGroups
                pure $ Just (SampleIndex $ const sampler, Right . weight)
            else pure Nothing
    pure $
        ( mkOutcomeIndex
            totalOutcomes
            uniformMass
            select
            (leafRanks pairRanks)
            selectValue
            rankSampler
            ( PlanChoice
                [ ( joinGroupCardinality group
                  , PlanAp
                        (toEnum $ Sequence.length $ joinGroupRight group)
                        (PlanMap (,) $ seqPlan $ joinGroupLeft group)
                        (seqPlan $ joinGroupRight group)
                  )
                | group <- groups
                ]
            )
        )
            { outcomeSizeSampling = sizeSampling
            }
  where
    -- The groups with the weight of each outcome in place of its mass.
    weightGroups =
        [ group
            { joinGroupLeft = Sequence.zipWith withMass (joinGroupLeftWeights group) (joinGroupLeft group)
            , joinGroupRight = Sequence.zipWith withMass (joinGroupRightWeights group) (joinGroupRight group)
            }
        | group <- groups
        ]
      where
        withMass mass outcome = outcome{outcomeMass = mass}
    totalWeight = sum $ map joinGroupMass weightGroups
    weight index =
        let (_, leftOutcome, rightOutcome) = selectPairIn weightGroupsByOffset index
         in toRational totalOutcomes * outcomeMass leftOutcome * outcomeMass rightOutcome / totalWeight
    weightGroupsByOffset = joinGroupsByOffset weightGroups

    totalOutcomes = sum $ map joinGroupCardinality groups
    uniformMass = case (outcomeUniformMass $ staticOutcomes left, outcomeUniformMass $ staticOutcomes right) of
        (Just _, Just _) -> Just $ 1 / toRational totalOutcomes
        _ -> Nothing
    totalMass = sum $ map joinGroupMass groups

    select index = do
        checkIndex totalOutcomes index
        let (group, leftOutcome, rightOutcome) = selectPair index
            keyTerm = Tree.Node (Group $ joinGroupIndex group) []
            leftTerm =
                Tree.Node LeftKeyed [keyTerm, outcomeTerm leftOutcome]
            rightTerm =
                Tree.Node RightKeyed [keyTerm, outcomeTerm rightOutcome]
        pure $
            Outcome
                (Tree.Node Join [leftTerm, rightTerm])
                ( outcomeMass leftOutcome
                    * outcomeMass rightOutcome
                    / totalMass
                )
                (outcomeValue leftOutcome, outcomeValue rightOutcome)
                ( Tree.Node
                    (plainSymbol Join)
                    [ Tree.Node (plainSymbol LeftKeyed) [fmap plainSymbol keyTerm, outcomeInspection leftOutcome]
                    , Tree.Node (plainSymbol RightKeyed) [fmap plainSymbol keyTerm, outcomeInspection rightOutcome]
                    ]
                )

    selectValue index =
        let (_, leftOutcome, rightOutcome) = selectPair index
         in (outcomeValue leftOutcome, outcomeValue rightOutcome)

    -- The key of a pair names its group, and each side is one enumerated outcome of its group.
    pairRanks term = case term of
        Tree.Node
            Join
            [ Tree.Node LeftKeyed [Tree.Node (Group (GroupIndex key)) [], leftTerm]
                , Tree.Node RightKeyed [Tree.Node (Group (GroupIndex key')) [], rightTerm]
                ]
                | key == key' ->
                    [ (offsetRank offset $ pairRank (toEnum $ Sequence.length $ joinGroupRight group) leftIndex rightIndex, True)
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
    selectPair = selectPairIn groupsByOffset
    selectPairIn byOffset index =
        let (group, groupIndex) = selectJoinGroup index byOffset
            rightCardinality = toEnum $ Sequence.length $ joinGroupRight group
            (leftIndex, rightIndex) = splitRank rightCardinality groupIndex
            leftOutcome = Sequence.index (joinGroupLeft group) $ fromEnum leftIndex
            rightOutcome = Sequence.index (joinGroupRight group) $ fromEnum rightIndex
         in (group, leftOutcome, rightOutcome)

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
            "microcfta-generator bug in Data.CFTA.Gen.Internal.Join.selectJoinGroup: \
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
        [ Tree.Node (ArgKey componentIndex position) []
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
                Tree.Node CenterKeyed (outcomeTerm operationOutcome : keyTerms)
        pure $
            Outcome
                (Tree.Node JoinN (operationTerm : argumentTerms))
                (outcomeMass operationOutcome * argumentsMass)
                value
                ( Tree.Node (plainSymbol JoinN) $
                    Tree.Node
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
        WholeTerm (Tree.Node JoinN children) -> childrenRanks children
        WholeTerm _ -> []
        LabelledView children -> childrenRanks children
        SpineView [term] -> joinRanks $ WholeTerm term
        SpineView _ -> []
      where
        childrenRanks (Tree.Node CenterKeyed centre : argumentTerms) = case centre of
            operationTerm : keys ->
                let keysChecked = joinKeysMatch componentIndex keys argumentTerms
                 in [ (pairRank argumentsCardinality operationRank argumentRank, operationChecked && argumentsChecked && keysChecked)
                    | (operationRank, operationChecked) <- outcomeRanks operationOutcomes $ WholeTerm operationTerm
                    , (argumentRank, argumentsChecked) <- chainRanks arguments argumentTerms
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
    joinedIndex = recursiveChainIndex operationIndex arguments
    joinedMasses =
        recursiveChainMass
            (keyedRecursiveMasses operation)
            arguments
    joinedSampling =
        recursiveChainSampling
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
