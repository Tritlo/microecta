{- | The argument chains of a grouped application.

One chain holds the matched group of every signature component, in order. The
folds over a chain count, sample, and decode the joined ranks. Only
'lookupArgs' and 'mapChain' are shared by finite and recursive argument
families. The support, inspection, and counting folds have one version for each.
-}
module Data.CFTA.Gen.Internal.Chain (
    -- * Chains
    ArgMaps (..),
    ArgChain (..),
    ArgStatics,
    lookupArgs,
    mapChain,
    chainMass,

    -- * Finite chains
    chainLength,
    chainSupports,
    chainInspections,
    chainCardinality,
    chainUniformMass,
    chainSampler,
    chainPlan,
    chainDecoder,
    selectChain,
    chainRanks,
    recursiveChainTerms,

    -- * Recursive chains
    recursiveSupports,
    recursiveInspections,
    recursiveChainIndex,
    recursiveChainMass,
    recursiveChainSampling,
    recursiveChainWeighted,
    recursiveChainMassWeighted,
) where

import Data.Kind (Type)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Tree as Tree

import Data.CFTA.Equality (Node)
import Data.CFTA.Gen.Error (GenError (..))
import Data.CFTA.Gen.Internal.Bucket (KeyedBucket (..))
import Data.CFTA.Gen.Internal.Inspection
import Data.CFTA.Gen.Internal.Recursive
import Data.CFTA.Gen.Internal.Static
import Data.CFTA.Gen.Label (Label (..))
import Data.CFTA.Gen.Sig (Sig (..))
import Data.CFTA.Ranked.Internal.Decoder (Plan (..))
import Data.CFTA.Ranked.Internal.Sampler
import Data.CFTA.Ranked.Internal.Size (SizeIndex, mapIndex, productIndex, productPosition)

{- | Group maps of every argument family, threaded through the operation type.

The group payload is a parameter: finite argument families carry a
@KeyedBucket@, recursive ones a @KeyedRecursive@. Only the functions that do not
depend on the payload are shared. The other folds have one version for each.
-}
data ArgMaps f (argKeys :: [Type]) operation result where
    MapsNil :: ArgMaps f '[] result result
    MapsCons ::
        (Ord argKey) =>
        Map.Map argKey (f arg) ->
        ArgMaps f argKeys operation result ->
        ArgMaps f (argKey ': argKeys) (arg -> operation) result

-- | The matched group of every argument family, in signature order.
data ArgChain f operation result where
    ChainNil :: ArgChain f result result
    ChainCons ::
        f arg ->
        ArgChain f operation result ->
        ArgChain f (arg -> operation) result

-- | The matched finite group of every argument family, in signature order.
type ArgStatics symbol = ArgChain (Static symbol)

-- | Find the argument group for every signature key.
lookupArgs ::
    Sig argKeys resultKey ->
    ArgMaps f argKeys operation result ->
    Maybe (ArgChain f operation result)
lookupArgs (key :-> _) (MapsCons groups MapsNil) = do
    group <- Map.lookup key groups
    Just $ ChainCons group ChainNil
lookupArgs (key :* rest) (MapsCons groups restMaps) = do
    group <- Map.lookup key groups
    chain <- lookupArgs rest restMaps
    Just $ ChainCons group chain

-- | Replace every group in a chain, keeping its shape.
mapChain :: (forall x. f x -> g x) -> ArgChain f operation result -> ArgChain g operation result
mapChain _ ChainNil = ChainNil
mapChain transform (ChainCons group rest) =
    ChainCons (transform group) (mapChain transform rest)

-- | The product of the matched groups' probability masses.
chainMass :: ArgChain (KeyedBucket symbol) operation result -> Rational
chainMass ChainNil = 1
chainMass (ChainCons bucket rest) = keyedBucketMass bucket * chainMass rest

-- | Number of arguments in the chain.
chainLength :: ArgStatics symbol operation result -> Int
chainLength ChainNil = 0
chainLength (ChainCons _ rest) = 1 + chainLength rest

-- | ECTA support of every argument group, in order.
chainSupports ::
    ArgStatics symbol operation result -> [Node (Label symbol)]
chainSupports ChainNil = []
chainSupports (ChainCons static rest) = staticSupport static : chainSupports rest

-- | Diagnostic metadata of each matched finite argument group.
chainInspections ::
    ArgStatics symbol operation result -> [Inspection symbol]
chainInspections ChainNil = []
chainInspections (ChainCons static rest) = staticInspection static : chainInspections rest

-- | Product of the argument group cardinalities.
chainCardinality :: ArgStatics symbol operation result -> Integer
chainCardinality ChainNil = 1
chainCardinality (ChainCons static rest) =
    outcomeCardinality (staticOutcomes static) * chainCardinality rest

-- | Product of the argument uniform masses, when all are uniform.
chainUniformMass :: ArgStatics symbol operation result -> Maybe Rational
chainUniformMass ChainNil = Just 1
chainUniformMass (ChainCons static rest) =
    (*)
        <$> outcomeUniformMass (staticOutcomes static)
        <*> chainUniformMass rest

{- | Compose the mixed-radix rank sampler as a left 'productSampler' fold.

The composed rank is @operationRank@ most significant, then argument ranks
left to right, matching 'chainDecoder'.
-}
chainSampler ::
    Sampler operation -> ArgStatics symbol operation result -> Sampler result
chainSampler sampler ChainNil = sampler
chainSampler sampler (ChainCons static rest) =
    chainSampler
        ( productSampler
            (outcomeCardinality $ staticOutcomes static)
            sampler
            (outcomeSampler $ staticOutcomes static)
        )
        rest

{- | Mirror 'chainSampler' as plan structure, one product per argument.

Each argument is a shared plan: the compiled decoder of the join calls the
compiled decoder of the argument group. Many joins use the same group, for
example every step of a trace uses the groups of the step before it. A plan
that copied the group's plan into each join would compile one copy for each
path to the group, and the decoder would keep each copy that a sample reached.
For 20,000 traces of length 20, that kept 414 MB, against 2.3 MB with sharing.
-}
chainPlan :: Plan operation -> ArgStatics symbol operation result -> Plan result
chainPlan plan ChainNil = plan
chainPlan plan (ChainCons static rest) =
    chainPlan
        ( PlanAp
            (outcomeCardinality outcomes)
            plan
            (PlanShared (outcomeCardinality outcomes) (outcomeDecoder outcomes) (outcomePlan outcomes))
        )
        rest
  where
    outcomes = staticOutcomes static

-- | Build a rank decoder once, capturing every suffix cardinality.
chainDecoder ::
    ArgStatics symbol operation result -> operation -> Integer -> result
chainDecoder ChainNil = const
chainDecoder (ChainCons static ChainNil) =
    let valueAt = outcomeValueAt $ staticOutcomes static
     in \operation index -> operation $ valueAt index
chainDecoder (ChainCons first (ChainCons second ChainNil)) =
    let firstValueAt = outcomeValueAt $ staticOutcomes first
        secondOutcomes = staticOutcomes second
        secondCardinality = outcomeCardinality secondOutcomes
        secondValueAt = outcomeValueAt secondOutcomes
     in \operation index ->
            let (firstIndex, secondIndex) = index `quotRem` secondCardinality
             in operation (firstValueAt firstIndex) (secondValueAt secondIndex)
chainDecoder (ChainCons static rest) =
    let decodeRest = chainDecoder rest
        suffixCardinality = chainCardinality rest
        valueAt = outcomeValueAt $ staticOutcomes static
     in \partial index ->
            let (here, there) = index `quotRem` suffixCardinality
             in decodeRest (partial $ valueAt here) there

{- | The mixed-radix ranks of the argument terms of a join, in ascending
order: the argument ranks left to right, as 'selectChain' reads them.
-}
chainRanks ::
    ArgStatics symbol operation result -> [Tree.Tree (Label symbol)] -> [Integer]
chainRanks ChainNil [] = [0]
chainRanks (ChainCons static rest) (Tree.Node ArgKeyed [_, term] : terms) =
    [ here * chainCardinality rest + there
    | here <- outcomeRanks (staticOutcomes static) $ WholeTerm term
    , there <- chainRanks rest terms
    ]
chainRanks _ _ = []

selectChain ::
    operation ->
    ArgStatics symbol operation result ->
    [Tree.Tree (Label symbol)] ->
    Integer ->
    Either GenError ([Tree.Tree (Label symbol)], [Tree.Tree (InspectionSymbol symbol)], Rational, result)
selectChain value ChainNil _ _ = Right ([], [], 1, value)
selectChain partial (ChainCons static rest) (keyTerm : keyTerms) index = do
    let (here, there) = index `quotRem` chainCardinality rest
    outcome <- outcomeSelect (staticOutcomes static) here
    (terms, inspections, mass, value) <- selectChain (partial $ outcomeValue outcome) rest keyTerms there
    pure
        ( Tree.Node ArgKeyed [keyTerm, outcomeTerm outcome] : terms
        , Tree.Node
            (plainSymbol ArgKeyed)
            [ fmap (\symbol -> InspectionSymbol symbol $ inspectionName $ staticInspection static) keyTerm
            , outcomeInspection outcome
            ]
            : inspections
        , outcomeMass outcome * mass
        , value
        )
selectChain _ (ChainCons _ _) [] _ =
    error
        "microcfta-generator bug in Data.CFTA.Gen.Internal.Chain.selectChain: \
        \fewer key terms than arguments"

{- | The terms of one joined component of a recursive keyed application.

The term of a member is an n-way join, as for a finite join: the operation
term after the argument keys, then each argument term with its key. The value
indexes of the operation and of the arguments give the counts of the product
chain. 'Nothing' means that an argument does not track terms.
-}
recursiveChainTerms ::
    Int ->
    SizeIndex operation ->
    RecursiveTerms symbol ->
    ArgChain (KeyedRecursive symbol) operation result ->
    Maybe (RecursiveTerms symbol)
recursiveChainTerms componentIndex operationIndex operationTerms arguments = do
    argumentTerms <- chainTerms arguments
    let keyTerms = [Tree.Node (ArgKey componentIndex position) [] | position <- [0 .. length argumentTerms - 1]]
        -- The term index accumulates the argument terms in order.
        accumulated =
            foldl
                ( \partial (_, terms) ->
                    productIndex
                        (mapIndex (\(operation, earlier) argument -> (operation, earlier <> [argument])) partial)
                        (recursiveTermIndex terms)
                )
                (mapIndex (,[]) $ recursiveTermIndex operationTerms)
                argumentTerms
        joinTerm (operation, argumentTerms') =
            Tree.Node JoinN $
                Tree.Node CenterKeyed (keyTerms <> [operation])
                    : zipWith (\key argument -> Tree.Node ArgKeyed [key, argument]) keyTerms argumentTerms'
        -- The counts of the product chain after each argument.
        chainIndexes =
            scanl
                (\partial (index, _) -> productIndex (mapIndex const partial) index)
                (mapIndex (const ()) operationIndex)
                argumentTerms
        positions view = sort $ case view of
            WholeTerm (Tree.Node JoinN children) -> childrenPositions children
            WholeTerm _ -> []
            LabelledView children -> childrenPositions children
            SpineView [term] -> positions $ WholeTerm term
            SpineView _ -> []
        childrenPositions (Tree.Node CenterKeyed centre : argumentNodes)
            | operation : _ <- reverse centre
            , Just arguments' <- traverse argumentOf argumentNodes
            , length arguments' == length argumentTerms =
                foldl
                    ( \partialPositions (partialIndex, (argumentIndex, terms), argument) ->
                        [ productPosition partialIndex argumentIndex partialPosition argumentPosition
                        | partialPosition <- partialPositions
                        , argumentPosition <- recursiveTermPositions terms $ WholeTerm argument
                        ]
                    )
                    (recursiveTermPositions operationTerms $ WholeTerm operation)
                    (zip3 chainIndexes argumentTerms arguments')
        childrenPositions _ = []
        argumentOf (Tree.Node ArgKeyed [_, argument]) = Just argument
        argumentOf _ = Nothing
    pure $ RecursiveTerms (mapIndex joinTerm accumulated) positions
  where
    chainTerms ::
        ArgChain (KeyedRecursive symbol) operation' result' -> Maybe [(SizeIndex (), RecursiveTerms symbol)]
    chainTerms ChainNil = Just []
    chainTerms (ChainCons recursive rest) = do
        let language = keyedRecursiveLanguage recursive
        terms <- recursiveTerm language
        ((mapIndex (const ()) $ recursiveIndex language, terms) :) <$> chainTerms rest

-- | The support of every matched recursive argument group, in order.
recursiveSupports ::
    ArgChain (KeyedRecursive symbol) operation result -> [Node (Label symbol)]
recursiveSupports ChainNil = []
recursiveSupports (ChainCons recursive rest) =
    recursiveSupport (keyedRecursiveLanguage recursive) : recursiveSupports rest

-- | Diagnostic metadata of each matched recursive argument group.
recursiveInspections ::
    ArgChain (KeyedRecursive symbol) operation result -> [Inspection symbol]
recursiveInspections ChainNil = []
recursiveInspections (ChainCons recursive rest) =
    recursiveInspection (keyedRecursiveLanguage recursive) : recursiveInspections rest

-- | Consume the argument groups into the operation, left to right.
recursiveChainIndex ::
    SizeIndex operation ->
    ArgChain (KeyedRecursive symbol) operation result ->
    SizeIndex result
recursiveChainIndex index ChainNil = index
recursiveChainIndex index (ChainCons recursive rest) =
    recursiveChainIndex
        (productIndex index $ recursiveIndex $ keyedRecursiveLanguage recursive)
        rest

-- | Multiply group masses through an applicative chain.
recursiveChainMass ::
    MassIndex ->
    ArgChain (KeyedRecursive symbol) operation result ->
    MassIndex
recursiveChainMass mass ChainNil = mass
recursiveChainMass mass (ChainCons recursive rest) =
    recursiveChainMass
        (productMassIndex mass $ keyedRecursiveMasses recursive)
        rest

-- | Consume recursive argument samplers in the same product order as ranks.
recursiveChainSampling ::
    SizeIndex operation ->
    MassIndex ->
    SampleIndex operation ->
    ArgChain (KeyedRecursive symbol) operation result ->
    SampleIndex result
recursiveChainSampling _ _ sampling ChainNil = sampling
recursiveChainSampling index mass sampling (ChainCons recursive rest) =
    recursiveChainSampling nextIndex nextMass nextSampling rest
  where
    recursive' = keyedRecursiveLanguage recursive
    nextIndex = productIndex index $ recursiveIndex recursive'
    nextMass = productMassIndex mass $ keyedRecursiveMasses recursive
    nextSampling =
        productMassSampleIndex
            index
            (massAtSize mass)
            sampling
            (recursiveIndex recursive')
            (keyedRecursiveMassAtSize recursive)
            (recursiveSampling recursive')

-- | Whether any recursive argument contains a weighted atomic choice.
recursiveChainWeighted ::
    ArgChain (KeyedRecursive symbol) operation result -> Bool
recursiveChainWeighted ChainNil = False
recursiveChainWeighted (ChainCons recursive rest) =
    recursiveWeighted (keyedRecursiveLanguage recursive) || recursiveChainWeighted rest

-- | Whether a recursive argument's key mass differs from structural counts.
recursiveChainMassWeighted ::
    ArgChain (KeyedRecursive symbol) operation result -> Bool
recursiveChainMassWeighted ChainNil = False
recursiveChainMassWeighted (ChainCons recursive rest) =
    keyedRecursiveMassWeighted recursive || recursiveChainMassWeighted rest
