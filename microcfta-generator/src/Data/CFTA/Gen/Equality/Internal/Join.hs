{- | Joins that correlate two languages, or one operation and its arguments.

A join encodes membership with ECTA equality constraints and counts the
matched group products, so it visits no member of the joined language while it
is built.
-}
module Data.CFTA.Gen.Equality.Internal.Join (
    joinStatic,
    relateStatic,
    joinNBucketStatic,
    recursiveJoin,
) where

import Data.Foldable (toList)
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Sequence
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import Data.CFTA.Equality (Edge (Edge), Node (Node), mkEdge, reducePartially)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Gen.Equality.Internal.Bucket
import Data.CFTA.Gen.Equality.Internal.Chain
import Data.CFTA.Gen.Equality.Internal.Inspection
import Data.CFTA.Gen.Equality.Internal.Recursive
import Data.CFTA.Gen.Equality.Internal.Static
import Data.CFTA.Gen.Equality.Internal.Support
import Data.CFTA.Gen.Error (GenError (..))
import Data.CFTA.Gen.Label (Label (..))
import Data.CFTA.Path (path)
import Data.CFTA.Ranked.Internal.Decoder (Plan (..))
import Data.CFTA.Ranked.Internal.Sampler

-- | One compatible key-pair bucket used to count and unrank a conditioned product.
data JoinGroup symbol left right = JoinGroup
    { joinGroupIndex :: !Int
    , joinGroupLeft :: !(Seq (Outcome symbol left))
    , joinGroupRight :: !(Seq (Outcome symbol right))
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
    [([Outcome symbol left], [Outcome symbol right])] ->
    Either GenError (Static symbol (left, right))
joinGroupedStatic left right related =
    if null related
        then Left EmptyGenerator
        else
            let groups =
                    [ JoinGroup
                        keyIndex
                        (Sequence.fromList leftOutcomes)
                        (Sequence.fromList rightOutcomes)
                    | (keyIndex, (leftOutcomes, rightOutcomes)) <-
                        zip [0 :: Int ..] related
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
                                (mkEqConstraints [[path [0, 0], path [1, 0]]])
                            ]
             in -- Every group came from two non-empty outcome buckets. Keep
                -- support reduction lazy; the outcome index already proves
                -- that the joined language is non-empty.
                (\outcomes -> Static joined outcomes False $ inspectionJoined groups)
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
                    (mkEqConstraints [[path [0, 0], path [1, 0]]])
                ]
      where
        side symbol outcomes =
            Node
                [ Edge
                    (plainSymbol symbol)
                    [ singletonNode $ Tree.Node (plainSymbol $ Key $ joinGroupIndex group) []
                    , singletonNode outcome
                    ]
                | group <- groups
                , outcome <- toList $ outcomes group
                ]

-- | Enumerate a language and pair every outcome with its projected key.
keyedOutcomes ::
    (value -> key) ->
    Static symbol value ->
    Either GenError [(key, Outcome symbol value)]
keyedOutcomes key static =
    map (\outcome -> (key $ outcomeValue outcome, outcome))
        <$> enumerateOutcomeIndex (staticOutcomes static)

-- | Count, select, and sample the matched groups of a two-way join.
joinOutcomeIndex ::
    Static symbol left ->
    Static symbol right ->
    [JoinGroup symbol left right] ->
    Either GenError (OutcomeIndex symbol (left, right))
joinOutcomeIndex left right groups = do
    rankSampler <- case uniformMass of
        Just _ -> pure $ uniformSampler totalOutcomes selectValue
        Nothing -> joinSampler groups
    pure $
        mkOutcomeIndex
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
            keyTerm = Tree.Node (Key $ joinGroupIndex group) []
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

    selectPair index =
        let (group, groupIndex) = selectJoinGroup index groups
            rightCardinality = toInteger $ Sequence.length $ joinGroupRight group
            (leftIndex, rightIndex) = groupIndex `quotRem` rightCardinality
            leftOutcome = Sequence.index (joinGroupLeft group) $ fromInteger leftIndex
            rightOutcome = Sequence.index (joinGroupRight group) $ fromInteger rightIndex
         in (group, leftOutcome, rightOutcome)

-- | Number of pairs in one matched group.
joinGroupCardinality :: JoinGroup symbol left right -> Integer
joinGroupCardinality group =
    toInteger (Sequence.length $ joinGroupLeft group)
        * toInteger (Sequence.length $ joinGroupRight group)

-- | Probability mass of one matched group.
joinGroupMass :: JoinGroup symbol left right -> Rational
joinGroupMass group =
    sum (outcomeMass <$> joinGroupLeft group)
        * sum (outcomeMass <$> joinGroupRight group)

-- | Find the group holding a rank, with the rank rebased into it.
selectJoinGroup ::
    Integer ->
    [JoinGroup symbol left right] ->
    (JoinGroup symbol left right, Integer)
selectJoinGroup _ [] =
    error
        "microcfta-generator bug in Data.CFTA.Gen.Equality.Internal.Join.selectJoinGroup: \
        \rank outside the matched groups"
selectJoinGroup index (group : remaining)
    | index < groupSize = (group, index)
    | otherwise = selectJoinGroup (index - groupSize) remaining
  where
    groupSize = joinGroupCardinality group

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

-- | Pair every join group with its cumulative rank offset.
offsetJoinGroups :: [JoinGroup symbol left right] -> [(Integer, JoinGroup symbol left right)]
offsetJoinGroups = go 0
  where
    go _ [] = []
    go offset (group : remaining) =
        (offset, group) : go (offset + joinGroupCardinality group) remaining

-- | Join one operation group with its argument groups in one ECTA edge, with one equality constraint per argument.
joinNBucketStatic ::
    (Hashable symbol, Typeable symbol) =>
    Int ->
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
            selectValue
            rankSampler
            (chainPlan (outcomePlan operationOutcomes) arguments)
        )
        False
        (joinInspection componentIndex (staticInspection operation) $ chainInspections arguments)
  where
    keyTerms =
        [ Tree.Node (ArgKey componentIndex position) []
        | position <- [0 .. chainLength arguments - 1]
        ]
    joined =
        reducePartially $
            joinNode componentIndex (staticSupport operation) (chainSupports arguments)
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
        (argumentTerms, argumentInspections, argumentsMass, value) <-
            selectChain (outcomeValue operationOutcome) arguments keyTerms argumentIndex
        let operationTerm =
                Tree.Node CenterKeyed (keyTerms <> [outcomeTerm operationOutcome])
        pure $
            Outcome
                (Tree.Node JoinN (operationTerm : argumentTerms))
                (outcomeMass operationOutcome * argumentsMass)
                value
                ( Tree.Node (plainSymbol JoinN) $
                    Tree.Node
                        (plainSymbol CenterKeyed)
                        ( zipWith
                            (\term inspection -> fmap (\symbol -> InspectionSymbol symbol $ inspectionName inspection) term)
                            keyTerms
                            (chainInspections arguments)
                            <> [outcomeInspection operationOutcome]
                        )
                        : argumentInspections
                )

    selectValue index =
        let (operationIndex, argumentIndex) = index `quotRem` argumentsCardinality
         in decodeArguments (outcomeValueAt operationOutcomes operationIndex) argumentIndex

{- | One joined component of a recursive keyed application.

Sizes and rank order match the finite join: the operation is one choice and
the arguments follow it left to right. The joined edge is not reduced, since
propagating constraints through a recursive node is not sound.
-}
recursiveJoin ::
    (Hashable symbol, Typeable symbol) =>
    Int ->
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
            joinedOccurrence
            Nothing
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
    joinedOccurrence =
        recursiveOccurrence operationRecursive
            || recursiveChainOccurrence arguments
