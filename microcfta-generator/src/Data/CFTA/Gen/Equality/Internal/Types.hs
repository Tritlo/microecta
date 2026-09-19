{- | The generator types and how they lower into QuickCheck.

A generator is inspectable ECTA structure, finite or recursive, or an opaque
QuickCheck generator. A grouped generator is the same thing per retained key. The
combinators over these types live in the other @Data.CFTA.Gen.Equality.Internal@
modules and in "Data.CFTA.Gen.Equality"; this module also holds the two weight checks
that the flat and the grouped choice combinators share.
-}
module Data.CFTA.Gen.Equality.Internal.Types (
    -- * Generators
    ECTAGen (..),
    isRecursive,
    isOpaque,
    recursiveView,

    -- * Grouped generators
    Grouped (..),
    isRecursiveGrouped,
    recursiveGroups,

    -- * Composing
    Args (..),
    NodeLayer (..),
    node,

    -- * Lowering
    lower,
    lowerWithRank,
    lowerUniform,
    lowerUniformWithRank,
    lowerVia,
    lowerWithRankVia,

    -- * Alternative weights
    firstNonPositiveWeight,
    allWeightsEqual,
) where

import Data.Kind (Type)
import qualified Data.Map.Strict as Map
import qualified Test.QuickCheck as QC

import Data.CFTA.Equality (Edge (Edge), Node (Node))
import Data.CFTA.Gen.Equality.Internal
import Data.CFTA.Gen.Equality.Internal.Inspection
import Data.CFTA.Ranked.Internal.Decoder (RankDecoder (..))
import Data.CFTA.Ranked.Internal.Sampler
import Data.CFTA.Ranked.Internal.Size (mapIndex, productIndex)
import Data.CFTA.Ranked.QuickCheck (QuickCheckBackend (..))
import Data.CFTA.Symbol (Symbol)

{- | A generator is inspectable ECTA structure — finite or recursive — or an
opaque QuickCheck generator.
-}
data ECTAGen a
    = Transparent !(Either GenError (Static a))
    | Cyclic !(Either GenError (Recursive a))
    | Opaque !(QC.Gen (Either GenError a))

-- | Whether a generator stands for a recursive language.
isRecursive :: ECTAGen a -> Bool
isRecursive (Cyclic _) = True
isRecursive _ = False

-- | Whether a generator is an opaque region, which cannot be inspected.
isOpaque :: ECTAGen a -> Bool
isOpaque (Opaque _) = True
isOpaque _ = False

{- | View any inspectable generator as a recursive one.

A finite generator is a recursive language that happens to stop: its plan
already counts by size, and its support is already its automaton.
-}
recursiveView :: ECTAGen a -> Either GenError (Recursive a)
recursiveView (Transparent result) = recursiveFromStatic <$> result
recursiveView (Cyclic result) = result
recursiveView (Opaque _) = Left CannotInspectOpaqueGenerator

{- | A transparent generator whose values are classified by a projected key.

The key is not part of the generated value. It classifies values into groups;
during a join, matching key values determine which groups receive equal internal
labels on constrained ECTA paths. Each key group retains compact ECTA support
and indexed selection without storing all outcomes.
-}
data Grouped key a
    = Grouped !(Either GenError (Map.Map key (KeyedBucket a)))
    | -- | A recursive family: one language per key, all sharing one @Mu@.
      CyclicGrouped !(Either GenError (Map.Map key (KeyedRecursive a)))

-- | Whether a grouped generator stands for a recursive family.
isRecursiveGrouped :: Grouped key a -> Bool
isRecursiveGrouped (CyclicGrouped _) = True
isRecursiveGrouped _ = False

{- | View a grouped generator as a recursive family, one language per key.

A finite family is a recursive one that happens to stop, so this is how the
recursive builders accept either.
-}
recursiveGroups ::
    Grouped key a ->
    Either GenError (Map.Map key (KeyedRecursive a))
recursiveGroups (CyclicGrouped result) = result
recursiveGroups (Grouped result) = keyedRecursiveFromBuckets <$> result

{- | Argument families for 'apply', one per signature component, in order.

Each link requires the family key type named by the corresponding signature
component and consumes the corresponding argument of the generated operation.
-}
data Args (argKeys :: [Type]) operation result where
    ANil :: Args '[] result result
    (:&) ::
        (Ord argKey) =>
        Grouped argKey arg ->
        Args argKeys operation result ->
        Args (argKey ': argKeys) (arg -> operation) result

infixr 5 :&

{- | A generated child layer that can be closed with one visible constructor
label.

Instances cover ordinary and grouped ECTA generators. The grouped instance
keeps its result key and equality constraints while replacing the generator's
private join symbol with the supplied domain symbol.
-}
class NodeLayer layer where
    -- | Replace an open layer's private root with a domain constructor.
    closeNode :: Symbol -> layer a -> layer a

-- | Close an applicative child description with one domain constructor.
node :: (NodeLayer layer) => Symbol -> layer a -> layer a
node = closeNode

instance NodeLayer ECTAGen where
    closeNode symbol (Transparent result) =
        Transparent $ fmap (labelStatic symbol) result
    closeNode symbol (Cyclic result) =
        Cyclic $ fmap (labelRecursive symbol) result
    closeNode _ opaque@(Opaque _) = opaque

instance NodeLayer (Grouped key) where
    closeNode symbol (Grouped result) =
        Grouped $ fmap (fmap labelBucket) result
      where
        labelBucket bucket =
            bucket
                { keyedBucketStatic =
                    labelStatic symbol $ keyedBucketStatic bucket
                }
    closeNode symbol (CyclicGrouped result) =
        CyclicGrouped $ fmap (fmap labelGroup) result
      where
        labelGroup group =
            group
                { keyedRecursiveLanguage =
                    labelRecursive symbol $ keyedRecursiveLanguage group
                }

instance Functor (Grouped key) where
    fmap transform (Grouped result) =
        Grouped $ fmap (fmap mapBucket) result
      where
        mapBucket bucket =
            KeyedBucket
                (keyedBucketMass bucket)
                (mapStatic transform $ keyedBucketStatic bucket)
    fmap transform (CyclicGrouped result) =
        CyclicGrouped $ fmap (fmap mapGroup) result
      where
        mapGroup group =
            KeyedRecursive
                ( Recursive
                    (recursiveSupport recursive)
                    (mapIndex transform $ recursiveIndex recursive)
                    (mapSampleIndex transform $ recursiveSampling recursive)
                    (recursiveWeighted recursive)
                    (recursiveOccurrence recursive)
                    Nothing
                    (recursiveInspection recursive)
                )
                (keyedRecursiveMasses group)
                (keyedRecursiveMassWeighted group)
          where
            recursive = keyedRecursiveLanguage group

instance Functor ECTAGen where
    fmap transform (Transparent result) = Transparent $ fmap (mapStatic transform) result
    fmap transform (Cyclic result) = Cyclic $ fmap mapRecursive result
      where
        mapRecursive recursive =
            Recursive
                (recursiveSupport recursive)
                (mapIndex transform $ recursiveIndex recursive)
                (mapSampleIndex transform $ recursiveSampling recursive)
                (recursiveWeighted recursive)
                (recursiveOccurrence recursive)
                Nothing
                (recursiveInspection recursive)
    fmap transform (Opaque generated) = Opaque $ fmap (fmap transform) generated

instance Applicative ECTAGen where
    pure value = Transparent $ Right $ pureStatic value

    Transparent (Left err) <*> _ = Transparent $ Left err
    _ <*> Transparent (Left err) = Transparent $ Left err
    Transparent (Right functions) <*> Transparent (Right values) =
        Transparent $ Right $ applyStatic functions values
    functions <*> values
        | isRecursive functions || isRecursive values =
            Cyclic $ do
                left <- recursiveView functions
                right <- recursiveView values
                pure $
                    Recursive
                        ( Node
                            [ Edge
                                applySymbol
                                [recursiveSupport left, recursiveSupport right]
                            ]
                        )
                        (productIndex (recursiveIndex left) (recursiveIndex right))
                        ( productSampleIndex
                            (recursiveIndex left)
                            (recursiveSampling left)
                            (recursiveIndex right)
                            (recursiveSampling right)
                        )
                        (recursiveWeighted left || recursiveWeighted right)
                        (recursiveOccurrence left || recursiveOccurrence right)
                        Nothing
                        ( Inspection Nothing $
                            Node
                                [ Edge (plainSymbol applySymbol) [inspectionGraph $ recursiveInspection left, inspectionGraph $ recursiveInspection right]
                                ]
                        )
    functions <*> values =
        Opaque $ liftA2 (<*>) (lower functions) (lower values)

-- | Lower to QuickCheck, preserving construction and decoding errors.
lower :: ECTAGen a -> QC.Gen (Either GenError a)
lower (Opaque generated) = generated
lower generator = quickCheck $ lowerVia generator

-- | Lower an inspectable generator while retaining the sampled rank.
lowerWithRank :: ECTAGen a -> QC.Gen (Either GenError (Integer, a))
lowerWithRank = quickCheck . lowerWithRankVia

{- | Lower an inspectable generator through any sampling backend.

The exact backend of "Data.CFTA.Ranked.Internal.Sampler" gives the sampling
distribution as a finite list. An opaque region is a QuickCheck generator and
cannot be interpreted, so it reports 'CannotInspectOpaqueGenerator'.
-}
lowerVia :: (GenBackend gen) => ECTAGen a -> gen (Either GenError a)
lowerVia (Transparent (Left err)) = pure $ Left err
lowerVia (Transparent (Right static)) = sampleStatic static
lowerVia (Cyclic _) = pure $ Left UnboundedGenerator
lowerVia (Opaque _) = pure $ Left CannotInspectOpaqueGenerator

-- | 'lowerVia' retaining the sampled replay rank.
lowerWithRankVia :: (GenBackend gen) => ECTAGen a -> gen (Either GenError (Integer, a))
lowerWithRankVia (Transparent (Left err)) = pure $ Left err
lowerWithRankVia (Transparent (Right static)) = sampleStaticWithRank static
lowerWithRankVia (Cyclic _) = pure $ Left UnboundedGenerator
lowerWithRankVia (Opaque _) = pure $ Left CannotInspectOpaqueGenerator

-- | Run the QuickCheck backend.
quickCheck :: QuickCheckBackend a -> QC.Gen a
quickCheck (QuickCheckBackend generated) = generated

{- | Lower a transparent uniform generator to a direct QuickCheck generator.

The generator carries no per-sample error wrapping; construction errors and
the non-uniform and opaque cases return 'Nothing' and must go through 'lower'.
-}
lowerUniform :: ECTAGen a -> Maybe (QC.Gen a)
lowerUniform (Transparent (Right static))
    | Just _ <- outcomeUniformMass outcomes =
        Just $ case compiledDecoder outcomes of
            SmallDecoder bound decode -> decode <$> QC.chooseInt (0, bound - 1)
            LargeDecoder bound decode -> decode <$> QC.chooseInteger (0, bound - 1)
  where
    outcomes = staticOutcomes static
lowerUniform _ = Nothing

-- | Like 'lowerUniform', retaining the sampled replay rank.
lowerUniformWithRank :: ECTAGen a -> Maybe (QC.Gen (Integer, a))
lowerUniformWithRank (Transparent (Right static))
    | Just _ <- outcomeUniformMass outcomes =
        Just $ case compiledDecoder outcomes of
            SmallDecoder bound decode ->
                (\index -> (toInteger index, decode index)) <$> QC.chooseInt (0, bound - 1)
            LargeDecoder bound decode ->
                (\index -> (index, decode index)) <$> QC.chooseInteger (0, bound - 1)
  where
    outcomes = staticOutcomes static
lowerUniformWithRank _ = Nothing

-- | Find the first invalid alternative weight.
firstNonPositiveWeight :: [(Integer, a)] -> Maybe Integer
firstNonPositiveWeight = go
  where
    go [] = Nothing
    go ((weight, _) : rest)
        | weight <= 0 = Just weight
        | otherwise = go rest

-- | Whether every alternative carries the same weight.
allWeightsEqual :: [(Integer, a)] -> Bool
allWeightsEqual [] = True
allWeightsEqual ((firstWeight, _) : rest) =
    all ((== firstWeight) . fst) rest
