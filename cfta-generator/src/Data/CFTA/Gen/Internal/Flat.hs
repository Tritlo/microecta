{- | The flat layer: sources, imported automata, choices, and joins over one
generator at a time.

The grouped layer lives in "Data.CFTA.Gen.Internal.Grouped" and
recursion in "Data.CFTA.Gen.Internal.Recur".
-}
module Data.CFTA.Gen.Internal.Flat (
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
import Data.Hashable (Hashable)
import qualified Data.Text as Text
import Data.Typeable (Typeable)
import qualified Test.QuickCheck as QC

import Data.CFTA.Equality (Node)
import Data.CFTA.Gen.Error
import Data.CFTA.Gen.Internal.Automaton (automatonIndex, automatonTermPosition, finiteAutomaton)
import Data.CFTA.Gen.Internal.Grouped (groupOn, relateGroupsM, ungroup)
import Data.CFTA.Gen.Internal.Inspection
import Data.CFTA.Gen.Internal.Join
import Data.CFTA.Gen.Internal.Query (cardinality)
import Data.CFTA.Gen.Internal.Recursive
import Data.CFTA.Gen.Internal.Static
import Data.CFTA.Gen.Internal.Support (relabel)
import Data.CFTA.Gen.Internal.Types
import Data.CFTA.Gen.Label (Label (..))
import Data.CFTA.Gen.Sig (On (..))
import Data.CFTA.Index (Depth, Weight, countWeight)
import qualified Data.CFTA.Interned as Common
import Data.CFTA.Ranked.Internal (Indexed (..))
import Data.CFTA.Ranked.Internal.Sampler (GenBackend (frequencyGen), choiceSampleIndex, uniformSampleIndex)
import Data.CFTA.Ranked.Internal.Size (mapIndex)
import Data.CFTA.Ranked.QuickCheck (QuickCheckBackend (..))
import Data.CFTA.Term (Term)

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
fromIndexed :: (Hashable symbol, Typeable symbol) => Indexed a -> Gen symbol a
fromIndexed indexed
    | indexedCardinality indexed <= 0 = Transparent $ Left EmptyGenerator
    | otherwise = Transparent $ Right $ indexedStatic indexed

-- | Embed an ordinary QuickCheck generator as an opaque region.
fromGen :: QC.Gen a -> Gen symbol a
fromGen generated = Opaque $ Right <$> generated

{- | Read an automaton as a generator of the terms it accepts.

An acyclic automaton gives a finite generator with one rank per distinct term.
Symbolic counts are used where alternatives overlap or an equality reaches
below direct children. Every path orders the constructors at a node by arity,
then by the key. Alternatives with the same symbol are then ordered by the
structure of their children. Other alternatives with the same arity and key
keep the order in which their edges were interned. 'Symbol' orders by text, so
with the symbol as the key, the ranks do not depend on the order in which the
process interned its symbols and edges. A cyclic automaton gives a recursive
generator counted by size; it must be unambiguous and carry no equality
constraints, because its count sums over accepting runs.
-}
fromAutomaton ::
    (Ord symbol, Hashable symbol, Typeable symbol, Ord key) =>
    (symbol -> key) -> Node symbol -> Gen symbol (Term symbol)
fromAutomaton order root = withRecipe (Imported Nothing order root) $ readAutomaton order root

-- | Read the terms an automaton accepts up to a constructor-depth bound. A leaf has depth zero.
fromAutomatonUpToDepth ::
    (Ord symbol, Hashable symbol, Typeable symbol, Ord key) =>
    (symbol -> key) -> Depth -> Node symbol -> Gen symbol (Term symbol)
fromAutomatonUpToDepth order depth graph =
    withRecipe (Imported (Just depth) order graph) $ readAutomaton order $ Common.boundDepth depth graph

-- | The language of an automaton: finite when acyclic, counted by size otherwise.
readAutomaton ::
    (Ord symbol, Hashable symbol, Typeable symbol, Ord key) =>
    (symbol -> key) -> Node symbol -> Gen symbol (Term symbol)
readAutomaton order root
    | Common.numNestedMu root == 0 = Transparent $ finiteAutomaton order root
    | otherwise = Cyclic $ do
        index <- automatonIndex order root
        pure $
            Recursive
                supportNode
                index
                (uniformSampleIndex index)
                False
                (Just $ RecursiveTerms (mapIndex (fmap Label) index) $ leafRanks positions)
                (plainInspection supportNode)
  where
    supportNode = relabel Label root
    -- The term of a member is the accepted user term under 'Label', and the
    -- automaton checks every symbol of it.
    position = automatonTermPosition order root
    positions term = maybe [] (either (const []) (\found -> [CheckedRank found True]) . position) $ userTerm term

-- | Choose uniformly from a finite non-empty list.
elements :: (Hashable symbol, Typeable symbol) => [a] -> Gen symbol a
elements values =
    fromIndexed $
        Indexed
            (toEnum total)
            ((indexed Array.!) . fromEnum)
  where
    total = length values
    indexed = Array.listArray (0, total - 1) values

-- | Choose uniformly from named source values.
namedElements ::
    (Hashable symbol, Typeable symbol) => [(Text.Text, a)] -> Gen symbol a
namedElements values
    | total <= 0 = Transparent $ Left EmptyGenerator
    | otherwise =
        Transparent
            $ Right
            $ indexedStaticWithLabels
                (Just . fst . entry)
                (Indexed (toEnum total) (snd . entry))
  where
    total = length values
    indexed = Array.listArray (0, total - 1) values
    entry index = indexed Array.! fromEnum index

-- | Choose one generator with the supplied positive relative weight.
frequency ::
    (Hashable symbol, Typeable symbol) =>
    [(Weight, Gen symbol a)] -> Gen symbol a
frequency alternatives = withRecipe (Chosen alternatives) $ chooseLanguage alternatives

-- | The language of a weighted choice.
chooseLanguage ::
    (Hashable symbol, Typeable symbol) =>
    [(Weight, Gen symbol a)] -> Gen symbol a
chooseLanguage weighted
    | Just badWeight <- firstNonPositiveWeight weighted =
        Transparent $ Left $ NonPositiveWeight badWeight
    | failed : _ <- [alternative | (_, alternative) <- weighted, failure alternative] = failed
    | null alternatives = Transparent $ Left EmptyGenerator
    | Just staticAlternatives <- traverse getStatic alternatives =
        Transparent $ Right $ frequencyStatic staticAlternatives
    | any (isRecursive . snd) alternatives =
        Cyclic $ do
            views <- traverse (recursiveView . snd) alternatives
            if allWeightsEqual alternatives
                then
                    pure $
                        choiceRecursive
                            (choiceSampleIndex [(recursiveIndex view, recursiveSampling view) | view <- views])
                            (any recursiveWeighted views)
                            views
                else Left WeightedRecursiveAlternatives
    | otherwise =
        Opaque $ case frequencyGen [(weight, QuickCheckBackend $ lower generator) | (weight, generator) <- alternatives] of
            QuickCheckBackend generated -> generated
  where
    -- An empty alternative has no member to choose; it is not a failure.
    alternatives = filter (not . emptyAlternative . snd) weighted
      where
        emptyAlternative (Transparent (Left EmptyGenerator)) = True
        emptyAlternative (Cyclic (Left EmptyGenerator)) = True
        emptyAlternative _ = False
    -- The first failed alternative, finite or recursive, gives the error and
    -- whether the failure is recursive. An empty alternative is no failure.
    failure (Transparent (Left err)) = err /= EmptyGenerator
    failure (Cyclic (Left err)) = err /= EmptyGenerator
    failure _ = False

    getStatic (weight, Transparent (Right static)) = Just (weight, static)
    getStatic _ = Nothing

-- | Choose uniformly among generators.
oneof ::
    (Hashable symbol, Typeable symbol) => [Gen symbol a] -> Gen symbol a
oneof alternatives = frequency [(1, alternative) | alternative <- alternatives]

{- | Choose among generators in proportion to their members. If all
alternatives are finite, each alternative is weighted by its cardinality, so
every member of the combined language is equally likely when every alternative
is uniform. An alternative with its own weights, such as a 'frequency', keeps
them inside its share. If any alternative is recursive, this is 'oneof', whose
recursive choice draws each alternative in proportion to its members at the
drawn size. A member of several alternatives counts once for each. When an
alternative waits for 'Data.CFTA.Gen.Refinement.compile', so does the choice,
and compile weighs the compiled alternatives in the same way.
-}
uniformly ::
    (Hashable symbol, Typeable symbol) => [Gen symbol a] -> Gen symbol a
uniformly alternatives
    | any isRecursive alternatives = oneof alternatives
    | otherwise = case traverse liveCardinality alternatives of
        -- The weights wait for compile, which counts the alternatives.
        Left SourceRequiresCompilation -> withRecipe (Uniform alternatives) $ Transparent $ Left SourceRequiresCompilation
        Left err -> Transparent $ Left err
        Right counts ->
            frequency
                [ (countWeight count, alternative)
                | (Just count, alternative) <- zip counts alternatives
                ]
  where
    liveCardinality alternative = case cardinality alternative of
        Left EmptyGenerator -> Right Nothing
        Left err -> Left err
        Right count -> Right $ if count > 0 then Just count else Nothing

-- | Generate two values whose projected keys agree.
match ::
    (Hashable symbol, Typeable symbol) =>
    On left right ->
    Gen symbol left ->
    Gen symbol right ->
    Gen symbol (left, right)
match condition left right = case joinSides left right of
    Left err -> Transparent $ Left err
    Right (Just (leftStatic, rightStatic)) ->
        withKeys condition $ \leftKey rightKey ->
            Transparent $ joinStatic leftKey rightKey leftStatic rightStatic
    Right Nothing ->
        withKeys condition $ \leftKey rightKey ->
            opaquePairs (\leftValue rightValue -> leftKey leftValue == rightKey rightValue) left right

-- | Generate two values whose projected keys satisfy a relation.
relate ::
    (Ord leftKey, Ord rightKey, Hashable symbol, Typeable symbol) =>
    (left -> leftKey) ->
    (right -> rightKey) ->
    (leftKey -> rightKey -> Bool) ->
    Gen symbol left ->
    Gen symbol right ->
    Gen symbol (left, right)
relate leftKey rightKey relation left right = case joinSides left right of
    Left err -> Transparent $ Left err
    Right (Just (leftStatic, rightStatic)) ->
        Transparent $ relateStatic leftKey rightKey relation leftStatic rightStatic
    Right Nothing ->
        opaquePairs (\leftValue rightValue -> relation (leftKey leftValue) (rightKey rightValue)) left right

{- | The two finite sides of a join, the error that empties it, or 'Nothing'
when a side is opaque. A failed side wins over an opaque one, and the left
side is checked first.
-}
joinSides :: Gen symbol left -> Gen symbol right -> Either GenError (Maybe (Static symbol left, Static symbol right))
joinSides left right
    | Transparent (Left err) <- left = Left err
    | Transparent (Left err) <- right = Left err
    | Cyclic (Left err) <- left = Left err
    | Cyclic (Left err) <- right = Left err
    | Cyclic _ <- left = Left UnboundedGenerator
    | Cyclic _ <- right = Left UnboundedGenerator
    | Transparent (Right leftStatic) <- left
    , Transparent (Right rightStatic) <- right =
        Right $ Just (leftStatic, rightStatic)
    | otherwise = Right Nothing

-- | The pairs of two generators with an opaque side, sampled until the pair passes the test.
opaquePairs :: (left -> right -> Bool) -> Gen symbol left -> Gen symbol right -> Gen symbol (left, right)
opaquePairs keep left right = Opaque $ liftA2 (liftA2 (,)) (lower left) (lower right) `QC.suchThat` kept
  where
    kept (Left _) = True
    kept (Right (leftValue, rightValue)) = keep leftValue rightValue

-- | Compile an effectful relation between two finite inspectable languages.
relateM ::
    (Ord leftKey, Ord rightKey, Hashable symbol, Typeable symbol) =>
    (left -> leftKey) ->
    (right -> rightKey) ->
    (leftKey -> rightKey -> IO (Either relationError Bool)) ->
    Gen symbol left ->
    Gen symbol right ->
    IO (Either relationError (Gen symbol (left, right)))
relateM leftKey rightKey relation left right =
    fmap (fmap ungroup) $
        relateGroupsM
            relation
            (\_ _ -> ())
            (groupOn leftKey left)
            (groupOn rightKey right)
