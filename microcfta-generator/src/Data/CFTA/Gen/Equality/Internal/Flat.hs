{- | The flat layer: sources, imported automata, choices, and joins over one
generator at a time.

The grouped layer lives in "Data.CFTA.Gen.Equality.Internal.Grouped" and
recursion in "Data.CFTA.Gen.Equality.Internal.Recursion".
-}
module Data.CFTA.Gen.Equality.Internal.Flat (
    -- * Sources
    fromIndexed,
    fromGen,
    elements,
    namedElements,

    -- * Imported automata
    fromAutomaton,
    fromAutomatonUpToDepth,

    -- * Choices
    frequency,
    oneof,
    uniformly,

    -- * Joins
    match,
    relate,
    relateM,
) where

import qualified Data.Array as Array
import Data.CFTA.Constraint (Constraint (..), HasEqualities (..))
import Data.Hashable (Hashable)
import qualified Data.Text as Text
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)
import qualified Test.QuickCheck as QC

import Data.CFTA.Equality (Edge (Edge), Node (Node))
import Data.CFTA.Gen.Equality.Internal.Automaton (automatonIndex, finiteAutomaton)
import Data.CFTA.Gen.Equality.Internal.Grouped (groupBy, relateGroupsM, ungroup)
import Data.CFTA.Gen.Equality.Internal.Inspect (cardinality)
import Data.CFTA.Gen.Equality.Internal.Inspection
import Data.CFTA.Gen.Equality.Internal.Join
import Data.CFTA.Gen.Equality.Internal.Recursive
import Data.CFTA.Gen.Equality.Internal.Static
import Data.CFTA.Gen.Equality.Internal.Support (relabel)
import Data.CFTA.Gen.Equality.Internal.Types
import Data.CFTA.Gen.Equality.Sig (On (..))
import Data.CFTA.Gen.Error
import Data.CFTA.Gen.Label (Label (..))
import qualified Data.CFTA.Interned as Common
import Data.CFTA.Ranked.Internal (Indexed (..))
import Data.CFTA.Ranked.Internal.Sampler (GenBackend (frequencyGen), choiceSampleIndex, uniformSampleIndex)
import Data.CFTA.Ranked.Internal.Size (choiceIndex, mapIndex)
import Data.CFTA.Ranked.QuickCheck (QuickCheckBackend (..))

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
fromIndexed :: (Constraint constraint, Hashable symbol, Typeable symbol) => Indexed a -> Gen symbol constraint a
fromIndexed indexed
    | indexedCardinality indexed <= 0 = Transparent $ Left EmptyGenerator
    | otherwise = Transparent $ Right $ indexedStatic indexed

-- | Embed an ordinary QuickCheck generator as an opaque region.
fromGen :: QC.Gen a -> Gen symbol constraint a
fromGen generated = Opaque $ Right <$> generated

{- | Read an automaton as a generator of the terms it accepts.

An acyclic automaton gives a finite generator with one rank per distinct
term. Symbolic counts, used where alternatives overlap or an equality reaches
below direct children, order constructors by the key. A cyclic automaton
gives a recursive generator counted by size; it must be unambiguous and carry
no equality constraints, because its count sums over accepting runs.
-}
fromAutomaton ::
    (Constraint constraint, Ord symbol, Hashable symbol, Typeable symbol, Ord key) =>
    (symbol -> key) -> Node symbol constraint -> Gen symbol constraint (Tree.Tree symbol)
fromAutomaton order root = withRecipe (Imported Nothing root) $ readAutomaton order root

-- | Read the terms an automaton accepts up to a constructor-depth bound. A leaf has depth zero.
fromAutomatonUpToDepth ::
    (Constraint constraint, Ord symbol, Hashable symbol, Typeable symbol, Ord key) =>
    (symbol -> key) -> Int -> Node symbol constraint -> Gen symbol constraint (Tree.Tree symbol)
fromAutomatonUpToDepth order depth graph =
    withRecipe (Imported (Just depth) graph) $ readAutomaton order $ Common.boundDepth depth graph

-- | The language of an automaton: finite when acyclic, counted by size otherwise.
readAutomaton ::
    (Constraint constraint, Ord symbol, Hashable symbol, Typeable symbol, Ord key) =>
    (symbol -> key) -> Node symbol constraint -> Gen symbol constraint (Tree.Tree symbol)
readAutomaton order root
    | Common.numNestedMu root == 0 = Transparent $ finiteAutomaton order root
    | otherwise = Cyclic $ do
        index <- automatonIndex root
        pure $
            Recursive
                supportNode
                index
                (uniformSampleIndex index)
                False
                False
                (Just $ mapIndex (fmap Label) index)
                (plainInspection supportNode)
  where
    supportNode = relabel Label root

-- | Choose uniformly from a finite non-empty list.
elements :: (Constraint constraint, Hashable symbol, Typeable symbol) => [a] -> Gen symbol constraint a
elements values =
    fromIndexed $
        Indexed
            (toInteger total)
            ((indexed Array.!) . fromInteger)
  where
    total = length values
    indexed = Array.listArray (0, total - 1) values

-- | Choose uniformly from named source values.
namedElements ::
    (Constraint constraint, Hashable symbol, Typeable symbol) => [(Text.Text, a)] -> Gen symbol constraint a
namedElements values
    | total <= 0 = Transparent $ Left EmptyGenerator
    | otherwise =
        Transparent
            $ Right
            $ indexedStaticWithLabels
                (Just . fst . entry)
                (Indexed (toInteger total) (snd . entry))
  where
    total = length values
    indexed = Array.listArray (0, total - 1) values
    entry index = indexed Array.! fromInteger index

-- | Choose one generator with the supplied positive relative weight.
frequency ::
    (Constraint constraint, Hashable symbol, Typeable symbol) =>
    [(Integer, Gen symbol constraint a)] -> Gen symbol constraint a
frequency alternatives = withRecipe (Chosen alternatives) $ chooseLanguage alternatives

-- | The language of a weighted choice.
chooseLanguage ::
    (Constraint constraint, Hashable symbol, Typeable symbol) =>
    [(Integer, Gen symbol constraint a)] -> Gen symbol constraint a
chooseLanguage weighted
    | Just badWeight <- firstNonPositiveWeight weighted =
        Transparent $ Left $ NonPositiveWeight badWeight
    | Just err <- firstError weighted = Transparent $ Left err
    | null alternatives = Transparent $ Left EmptyGenerator
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
                                [ Edge (Choice index) [recursiveSupport view]
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
                            (choiceInspection $ map recursiveInspection views)
                else Left WeightedRecursiveAlternatives
    | otherwise =
        Opaque $ case frequencyGen [(weight, QuickCheckBackend $ lower generator) | (weight, generator) <- alternatives] of
            QuickCheckBackend generated -> generated
  where
    -- An empty alternative has no member to choose; it is not a failure.
    alternatives = filter (not . emptyAlternative . snd) weighted
    emptyAlternative (Transparent (Left EmptyGenerator)) = True
    emptyAlternative _ = False

    firstError = go
      where
        go [] = Nothing
        go ((_, Transparent (Left EmptyGenerator)) : rest) = go rest
        go ((_, Transparent (Left err)) : _) = Just err
        go (_ : rest) = go rest

    getStatic (weight, Transparent (Right static)) = Just (weight, static)
    getStatic _ = Nothing

-- | Choose uniformly among generators.
oneof ::
    (Constraint constraint, Hashable symbol, Typeable symbol) => [Gen symbol constraint a] -> Gen symbol constraint a
oneof alternatives = frequency [(1, alternative) | alternative <- alternatives]

-- | Choose among generators so that every member of the combined language is equally likely.
uniformly ::
    (Constraint constraint, Hashable symbol, Typeable symbol) => [Gen symbol constraint a] -> Gen symbol constraint a
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
    (HasEqualities constraint, Hashable symbol, Typeable symbol) =>
    On left right ->
    Gen symbol constraint left ->
    Gen symbol constraint right ->
    Gen symbol constraint (left, right)
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
         in Opaque $ generatedPairs `QC.suchThat` matches

-- | Generate two values whose projected keys satisfy a relation.
relate ::
    (HasEqualities constraint, Ord leftKey, Ord rightKey, Hashable symbol, Typeable symbol) =>
    (left -> leftKey) ->
    (right -> rightKey) ->
    (leftKey -> rightKey -> Bool) ->
    Gen symbol constraint left ->
    Gen symbol constraint right ->
    Gen symbol constraint (left, right)
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
     in Opaque $ generatedPairs `QC.suchThat` related

-- | Compile an effectful relation between two finite inspectable languages.
relateM ::
    (HasEqualities constraint, Ord leftKey, Ord rightKey, Hashable symbol, Typeable symbol) =>
    (left -> leftKey) ->
    (right -> rightKey) ->
    (leftKey -> rightKey -> IO (Either relationError Bool)) ->
    Gen symbol constraint left ->
    Gen symbol constraint right ->
    IO (Either relationError (Gen symbol constraint (left, right)))
relateM leftKey rightKey relation left right =
    fmap (fmap ungroup) $
        relateGroupsM
            relation
            (\_ _ -> ())
            (groupBy leftKey left)
            (groupBy rightKey right)
