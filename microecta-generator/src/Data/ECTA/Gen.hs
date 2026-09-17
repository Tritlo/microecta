{- | Indexed generators whose transparent regions are represented as ECTAs.

An indexed source stores a finite cardinality and a function from indices to
values. Applicative composition tracks exact cardinalities and rank-based
selection alongside the ECTA, without materializing the product language.
Joins count matched group products and unrank directly within them.
-}
module Data.ECTA.Gen (
    -- * Generators
    ECTAGen,
    Grouped,
    ECTAGenError (..),
    explain,
    GenBackend (..),

    -- * Sources
    Indexed (..),
    fromIndexed,
    elements,
    fromECTA,
    fromBackend,

    -- * Composing
    frequency,
    oneof,
    uniformly,
    On (..),
    match,
    relate,

    -- * The grouped layer
    Sig (..),
    sigResult,
    Args (..),
    keyed,
    groupBy,
    regroupBy,
    mapWithKey,
    atKey,
    apply,
    frequencies,
    oneofGrouped,
    uniformlyGrouped,
    ungroup,

    -- * Recursion
    atomic,
    recur,
    recurGrouped,
    upToSize,
    isRecursive,
    isOpaque,

    -- * Inspection
    support,
    cardinality,
    sizes,
    countsAtSize,
    massesAtSize,
    countAtSize,
    minimumSize,
    countBy,
    pmf,
    pmfAtSize,
    smallest,
    unrank,
    sizeOfRank,
    smallerMembers,
    shrinkRank,

    -- * Lowering
    lower,
    lowerWithRank,
    lowerUniform,
    lowerUniformWithRank,
) where

import qualified Data.Array as Array
import qualified Data.Tree as Tree

import Data.ECTA (Edge (Edge), Node (Node))
import Data.ECTA.Gen.Internal
import Data.ECTA.Gen.Internal.Automaton (automatonIndex)
import Data.ECTA.Gen.Internal.Grouped
import Data.ECTA.Gen.Internal.Inspect
import Data.ECTA.Gen.Internal.Recursion
import Data.ECTA.Gen.Internal.Types
import Data.ECTA.Gen.Sig (On (..), Sig (..), sigResult)
import Data.ECTA.Term (Symbol)
import Data.Ranked.Internal.Sampler
import Data.Ranked.Internal.Size (choiceIndex)

-- | Interpret a reified condition as one key projection per side.
withKeys ::
    On left right ->
    (forall key. (Ord key) => (left -> key) -> (right -> key) -> t) ->
    t
withKeys (leftKey :==: rightKey) continue = continue leftKey rightKey
withKeys (first :&&: second) continue =
    withKeys first $ \leftKey rightKey ->
        withKeys second $ \otherLeftKey otherRightKey ->
            continue
                (\left -> (leftKey left, otherLeftKey left))
                (\right -> (rightKey right, otherRightKey right))

-- | Lift one finite indexed source into transparent ECTA structure.
fromIndexed :: Indexed a -> ECTAGen gen a
fromIndexed indexed
    | indexedCardinality indexed <= 0 = Transparent $ Left EmptyGenerator
    | otherwise = Transparent $ Right $ indexedStatic indexed

-- | Embed an opaque backend generator.
fromBackend :: (Functor gen) => gen a -> ECTAGen gen a
fromBackend generated = Opaque $ Right <$> generated

{- | Read an ECTA as a generator of the terms it accepts.

The automaton is the support, unchanged, and members are counted by size —
the number of term nodes — so the generator draws uniformly from the terms
of at most a given size, recursive @Mu@ nodes included. Because the values
are the accepted terms, a bounded generator keeps full inspection: 'pmf',
'countBy', and 'groupBy' all work on it.

Equality constraints are not counted: they correlate an edge's children, so
its count is the size of an intersection rather than a product, and an
automaton carrying them is rejected with 'CannotCountConstrainedEdges'
rather than miscounted.

Ambiguity is not counted either. A node's count sums over its edges, which
counts accepting runs, so a node with two edges accepting a common term would
count that term twice and report it at two ranks. Such an automaton is
rejected with 'AmbiguousAutomaton'.
-}
fromECTA :: Node Symbol -> ECTAGen gen (Tree.Tree Symbol)
fromECTA supportNode =
    Cyclic $ do
        index <- automatonIndex supportNode
        pure $ Recursive supportNode index (uniformSampleIndex index) False False $ Just id

-- | Choose uniformly from a finite non-empty list.
elements :: [a] -> ECTAGen gen a
elements values =
    fromIndexed $
        Indexed
            (toInteger total)
            ((indexed Array.!) . fromInteger)
  where
    total = length values
    indexed = Array.listArray (0, total - 1) values

-- | Choose one generator with the supplied positive relative weight.
frequency ::
    (GenBackend gen) =>
    [(Integer, ECTAGen gen a)] ->
    ECTAGen gen a
frequency [] = Transparent $ Left EmptyGenerator
frequency alternatives
    | Just badWeight <- firstNonPositiveWeight alternatives =
        Transparent $ Left $ NonPositiveWeight badWeight
    | Just err <- firstError alternatives = Transparent $ Left err
    | Just staticAlternatives <- traverse getStatic alternatives =
        Transparent $ Right $ frequencyStatic staticAlternatives
    | any (isRecursive . snd) alternatives =
        Cyclic $ do
            views <- traverse (recursiveView . snd) alternatives
            if allWeightsEqual alternatives
                then
                    pure $
                        Recursive
                            ( Node
                                [ Edge (frequencySymbol index) [recursiveSupport view]
                                | (index, view) <- zip [0 ..] views
                                ]
                            )
                            (choiceIndex $ map recursiveIndex views)
                            ( choiceSampleIndex
                                [ (recursiveIndex view, recursiveSampling view)
                                | view <- views
                                ]
                            )
                            (any recursiveWeighted views)
                            (any recursiveOccurrence views)
                            Nothing
                else Left WeightedRecursiveAlternatives
    | otherwise =
        Opaque $
            frequencyGen
                [(weight, lower generator) | (weight, generator) <- alternatives]
  where
    firstError = go
      where
        go [] = Nothing
        go ((_, Transparent (Left err)) : _) = Just err
        go (_ : rest) = go rest

    getStatic (weight, Transparent (Right static)) = Just (weight, static)
    getStatic _ = Nothing

{- | Choose uniformly among generators.

Every alternative is equally likely, whatever the size of its language, as
in QuickCheck's own @oneof@. In a recursive definition this is the shape to
reach for: weights around a recursive occurrence are rejected, because such
a language uses structural counts for global size selection and rank offsets.
A finite choice closed with 'atomic' can still retain its own sampler mass
within the selected size.
-}
oneof :: (GenBackend gen) => [ECTAGen gen a] -> ECTAGen gen a
oneof alternatives = frequency [(1, alternative) | alternative <- alternatives]

{- | Choose among generators so that every member of the combined language is
equally likely.

Finite alternatives are combined in proportion to their cardinalities. An
alternative with no members is dropped, as is one whose construction failed
with 'EmptyGenerator'; any other failure is reported, including an opaque
alternative, which has no cardinality to weight by. A recursive alternative
makes this 'oneof': a recursive language has no cardinality either, and its
size-class sampler already draws every member of a size class equally.

An alternative that is itself weighted keeps its own distribution, so members
are equally likely exactly when each alternative is uniform.
-}
uniformly :: (GenBackend gen) => [ECTAGen gen a] -> ECTAGen gen a
uniformly alternatives
    | any isRecursive alternatives = oneof alternatives
    | otherwise = case traverse liveCardinality alternatives of
        Left err -> Transparent $ Left err
        Right counts ->
            frequency
                [ (count, alternative)
                | (Just count, alternative) <- zip counts alternatives
                ]
  where
    liveCardinality alternative = case cardinality alternative of
        Left EmptyGenerator -> Right Nothing
        Left err -> Left err
        Right count -> Right $ if count > 0 then Just count else Nothing

-- | Generate two values whose projected keys agree.
match ::
    (GenBackend gen) =>
    On left right ->
    ECTAGen gen left ->
    ECTAGen gen right ->
    ECTAGen gen (left, right)
match _ (Transparent (Left err)) _ = Transparent $ Left err
match _ _ (Transparent (Left err)) = Transparent $ Left err
match _ (Cyclic _) _ = Transparent $ Left UnboundedGenerator
match _ _ (Cyclic _) = Transparent $ Left UnboundedGenerator
match condition (Transparent (Right left)) (Transparent (Right right)) =
    withKeys condition $ \leftKey rightKey ->
        Transparent $ joinStatic leftKey rightKey left right
match condition left right =
    withKeys condition $ \leftKey rightKey ->
        let generatedPairs = liftA2 (liftA2 (,)) (lower left) (lower right)
            matches (Left _) = True
            matches (Right (leftValue, rightValue)) =
                leftKey leftValue == rightKey rightValue
         in Opaque $ filterGen matches generatedPairs

{- | Generate two values whose projected keys satisfy a relation.

For finite inspectable inputs, the relation is evaluated once per live key
pair. The accepted group products are counted and sampled directly without
rejection. The key types may differ, and the relation need not be symmetric.
The relation must be total for every live key pair. An opaque input uses
backend rejection filtering instead.
-}
relate ::
    (GenBackend gen, Ord leftKey, Ord rightKey) =>
    (left -> leftKey) ->
    (right -> rightKey) ->
    (leftKey -> rightKey -> Bool) ->
    ECTAGen gen left ->
    ECTAGen gen right ->
    ECTAGen gen (left, right)
relate _ _ _ (Transparent (Left err)) _ = Transparent $ Left err
relate _ _ _ _ (Transparent (Left err)) = Transparent $ Left err
relate _ _ _ (Cyclic _) _ = Transparent $ Left UnboundedGenerator
relate _ _ _ _ (Cyclic _) = Transparent $ Left UnboundedGenerator
relate leftKey rightKey relation (Transparent (Right left)) (Transparent (Right right)) =
    Transparent $ relateStatic leftKey rightKey relation left right
relate leftKey rightKey relation left right =
    let generatedPairs = liftA2 (liftA2 (,)) (lower left) (lower right)
        related (Left _) = True
        related (Right (leftValue, rightValue)) =
            relation (leftKey leftValue) (rightKey rightValue)
     in Opaque $ filterGen related generatedPairs
