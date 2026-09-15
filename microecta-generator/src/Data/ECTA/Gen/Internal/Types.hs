{- | The generator types and how they lower into a backend.

A generator is inspectable ECTA structure, finite or recursive, or an opaque
backend action. A grouped generator is the same thing per retained key. The
combinators over these types live in the other @Data.ECTA.Gen.Internal@
modules and in "Data.ECTA.Gen"; this module also holds the two weight checks
that the flat and the grouped choice combinators share.
-}
module Data.ECTA.Gen.Internal.Types (
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

    -- * Alternative weights
    firstNonPositiveWeight,
    allWeightsEqual,
) where

import Data.Kind (Type)
import qualified Data.Map.Strict as Map

import Data.ECTA (Edge (Edge), Node (Node))
import Data.ECTA.Gen.Internal
import Data.ECTA.Term (Symbol)
import Data.Tree.Gen.Internal.Decoder (RankDecoder (..))
import Data.Tree.Gen.Internal.Sampler
import Data.Tree.Gen.Internal.Size (mapIndex, productIndex)

{- | A generator is inspectable ECTA structure — finite or recursive — or an
opaque backend action.
-}
data ECTAGen gen a
    = Transparent !(Either ECTAGenError (Static a))
    | Cyclic !(Either ECTAGenError (Recursive a))
    | Opaque !(gen (Either ECTAGenError a))

-- | Whether a generator stands for a recursive language.
isRecursive :: ECTAGen gen a -> Bool
isRecursive (Cyclic _) = True
isRecursive _ = False

-- | Whether a generator is an opaque region, which cannot be inspected.
isOpaque :: ECTAGen gen a -> Bool
isOpaque (Opaque _) = True
isOpaque _ = False

{- | View any inspectable generator as a recursive one.

A finite generator is a recursive language that happens to stop: its plan
already counts by size, and its support is already its automaton.
-}
recursiveView :: ECTAGen gen a -> Either ECTAGenError (Recursive a)
recursiveView (Transparent result) = recursiveFromStatic <$> result
recursiveView (Cyclic result) = result
recursiveView (Opaque _) = Left CannotInspectOpaqueGenerator

{- | A transparent generator whose values are classified by a projected key.

The key is not part of the generated value. It classifies values into groups;
during a join, matching key values determine which groups receive equal internal
labels on constrained ECTA paths. Each key group retains compact ECTA support
and indexed selection without storing all outcomes.
-}
data Grouped (gen :: Type -> Type) key a
    = Grouped !(Either ECTAGenError (Map.Map key (KeyedBucket a)))
    | -- | A recursive family: one language per key, all sharing one @Mu@.
      CyclicGrouped !(Either ECTAGenError (Map.Map key (KeyedRecursive a)))

-- | Whether a grouped generator stands for a recursive family.
isRecursiveGrouped :: Grouped gen key a -> Bool
isRecursiveGrouped (CyclicGrouped _) = True
isRecursiveGrouped _ = False

{- | View a grouped generator as a recursive family, one language per key.

A finite family is a recursive one that happens to stop, so this is how the
recursive builders accept either.
-}
recursiveGroups ::
    Grouped gen key a ->
    Either ECTAGenError (Map.Map key (KeyedRecursive a))
recursiveGroups (CyclicGrouped result) = result
recursiveGroups (Grouped result) = keyedRecursiveFromBuckets <$> result

{- | Argument families for 'apply', one per signature component, in order.

Each link requires the family key type named by the corresponding signature
component and consumes the corresponding argument of the generated operation.
-}
data Args gen (argKeys :: [Type]) operation result where
    ANil :: Args gen '[] result result
    (:&) ::
        (Ord argKey) =>
        Grouped gen argKey arg ->
        Args gen argKeys operation result ->
        Args gen (argKey ': argKeys) (arg -> operation) result

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

instance NodeLayer (ECTAGen gen) where
    closeNode symbol (Transparent result) =
        Transparent $ fmap (labelStatic symbol) result
    closeNode symbol (Cyclic result) =
        Cyclic $ fmap (labelRecursive symbol) result
    closeNode _ opaque@(Opaque _) = opaque

instance NodeLayer (Grouped gen key) where
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

instance Functor (Grouped gen key) where
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
                )
                (keyedRecursiveMasses group)
                (keyedRecursiveMassWeighted group)
          where
            recursive = keyedRecursiveLanguage group

instance (Functor gen) => Functor (ECTAGen gen) where
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
    fmap transform (Opaque generated) = Opaque $ fmap (fmap transform) generated

instance (GenBackend gen) => Applicative (ECTAGen gen) where
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
    functions <*> values =
        Opaque $ liftA2 (<*>) (lower functions) (lower values)

-- | Lower to the backend, preserving construction and decoding errors.
lower :: (GenBackend gen) => ECTAGen gen a -> gen (Either ECTAGenError a)
lower (Transparent (Left err)) = pure $ Left err
lower (Transparent (Right static)) = sampleStatic static
lower (Cyclic _) = pure $ Left UnboundedGenerator
lower (Opaque generated) = generated

-- | Lower a transparent generator while retaining the sampled rank.
lowerWithRank ::
    (GenBackend gen) =>
    ECTAGen gen a ->
    gen (Either ECTAGenError (Integer, a))
lowerWithRank (Transparent (Left err)) = pure $ Left err
lowerWithRank (Transparent (Right static)) = sampleStaticWithRank static
lowerWithRank (Cyclic _) = pure $ Left UnboundedGenerator
lowerWithRank (Opaque _) = pure $ Left CannotInspectOpaqueGenerator

{- | Lower a transparent uniform generator to a direct backend action.

The action carries no per-sample error wrapping; construction errors and the
non-uniform and opaque cases return 'Nothing' and must go through 'lower'.
-}
lowerUniform :: (GenBackend gen) => ECTAGen gen a -> Maybe (gen a)
lowerUniform (Transparent (Right static))
    | Just _ <- outcomeUniformMass outcomes =
        Just $ case compiledDecoder outcomes of
            SmallDecoder bound decode -> decode <$> selectInt bound
            LargeDecoder bound decode -> decode <$> selectInteger bound
  where
    outcomes = staticOutcomes static
lowerUniform _ = Nothing

-- | Like 'lowerUniform', retaining the sampled replay rank.
lowerUniformWithRank :: (GenBackend gen) => ECTAGen gen a -> Maybe (gen (Integer, a))
lowerUniformWithRank (Transparent (Right static))
    | Just _ <- outcomeUniformMass outcomes =
        Just $ case compiledDecoder outcomes of
            SmallDecoder bound decode ->
                (\index -> (toInteger index, decode index)) <$> selectInt bound
            LargeDecoder bound decode ->
                (\index -> (index, decode index)) <$> selectInteger bound
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
