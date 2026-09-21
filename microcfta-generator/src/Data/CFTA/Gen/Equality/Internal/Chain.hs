{- | The argument chains of a grouped application.

One chain holds the matched group of every signature component, in order. The
folds over a chain count, sample, and decode the joined ranks, and they are
written once for finite and for recursive argument families.
-}
module Data.CFTA.Gen.Equality.Internal.Chain (
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

    -- * Recursive chains
    recursiveSupports,
    recursiveInspections,
    recursiveChainIndex,
    recursiveChainMass,
    recursiveChainSampling,
    recursiveChainWeighted,
    recursiveChainOccurrence,
    recursiveChainMassWeighted,
) where

import Data.Kind (Type)
import qualified Data.Map.Strict as Map
import qualified Data.Tree as Tree

import Data.CFTA.Equality (Node)
import Data.CFTA.Equality.Constraint (EqConstraints)
import Data.CFTA.Gen.Equality.Internal.Bucket (KeyedBucket (..))
import Data.CFTA.Gen.Equality.Internal.Inspection
import Data.CFTA.Gen.Equality.Internal.Recursive
import Data.CFTA.Gen.Equality.Internal.Static
import Data.CFTA.Gen.Equality.Sig (Sig (..))
import Data.CFTA.Gen.Error (GenError (..))
import Data.CFTA.Gen.Label (Label (..))
import Data.CFTA.Ranked.Internal.Decoder (Plan (..))
import Data.CFTA.Ranked.Internal.Sampler
import Data.CFTA.Ranked.Internal.Size (SizeIndex, productIndex)

{- | Group maps of every argument family, threaded through the operation type.

The group payload is a parameter: finite argument families carry a
@KeyedBucket@, recursive ones a t'Recursive', and everything that only walks
the chain is written once for both.
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
chainSupports :: ArgStatics symbol operation result -> [Node (Label symbol) EqConstraints]
chainSupports ChainNil = []
chainSupports (ChainCons static rest) = staticSupport static : chainSupports rest

-- | Diagnostic metadata of each matched finite argument group.
chainInspections :: ArgStatics symbol operation result -> [Inspection symbol]
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
chainSampler :: Sampler operation -> ArgStatics symbol operation result -> Sampler result
chainSampler sampler ChainNil = sampler
chainSampler sampler (ChainCons static rest) =
    chainSampler
        ( productSampler
            (outcomeCardinality $ staticOutcomes static)
            sampler
            (outcomeSampler $ staticOutcomes static)
        )
        rest

-- | Mirror 'chainSampler' as plan structure, one product per argument.
chainPlan :: Plan operation -> ArgStatics symbol operation result -> Plan result
chainPlan plan ChainNil = plan
chainPlan plan (ChainCons static rest) =
    chainPlan
        ( PlanAp
            (outcomeCardinality $ staticOutcomes static)
            plan
            (outcomePlan $ staticOutcomes static)
        )
        rest

-- | Build a rank decoder once, capturing every suffix cardinality.
chainDecoder :: ArgStatics symbol operation result -> operation -> Integer -> result
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

-- | Select one outcome per argument, threading terms, mass, and the applied value.
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
        "microcfta-generator bug in Data.CFTA.Gen.Equality.Internal.Chain.selectChain: \
        \fewer key terms than arguments"

-- | The support of every matched recursive argument group, in order.
recursiveSupports :: ArgChain (KeyedRecursive symbol) operation result -> [Node (Label symbol) EqConstraints]
recursiveSupports ChainNil = []
recursiveSupports (ChainCons recursive rest) =
    recursiveSupport (keyedRecursiveLanguage recursive) : recursiveSupports rest

-- | Diagnostic metadata of each matched recursive argument group.
recursiveInspections :: ArgChain (KeyedRecursive symbol) operation result -> [Inspection symbol]
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
recursiveChainWeighted :: ArgChain (KeyedRecursive symbol) operation result -> Bool
recursiveChainWeighted ChainNil = False
recursiveChainWeighted (ChainCons recursive rest) =
    recursiveWeighted (keyedRecursiveLanguage recursive) || recursiveChainWeighted rest

-- | Whether any recursive argument is still a recursive occurrence.
recursiveChainOccurrence :: ArgChain (KeyedRecursive symbol) operation result -> Bool
recursiveChainOccurrence ChainNil = False
recursiveChainOccurrence (ChainCons recursive rest) =
    recursiveOccurrence (keyedRecursiveLanguage recursive) || recursiveChainOccurrence rest

-- | Whether a recursive argument's key mass differs from structural counts.
recursiveChainMassWeighted :: ArgChain (KeyedRecursive symbol) operation result -> Bool
recursiveChainMassWeighted ChainNil = False
recursiveChainMassWeighted (ChainCons recursive rest) =
    keyedRecursiveMassWeighted recursive || recursiveChainMassWeighted rest
