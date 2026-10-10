{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}

{- | The generator types and how they lower into QuickCheck.

A generator is the language it denotes and a recipe of how it was built.
The language is inspectable ECTA structure, finite or recursive, or an
opaque QuickCheck generator. A grouped generator is the same thing per
retained key. The combinators over these types live in the other
@Data.CFTA.Gen.Internal@ modules and in "Data.CFTA.Gen"; this
module also holds the two weight checks that the flat and the grouped choice
combinators share.
-}
module Data.CFTA.Gen.Internal.Types (
    -- * Generators
    Gen (..),
    Language (..),
    pattern Transparent,
    pattern Cyclic,
    pattern Opaque,
    Recipe (..),
    withRecipe,
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
    pay,
    payGrouped,
    nodeWithKey,

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

import Data.CFTA.Constraint (
    Constraint (..),
    noConstraint,
 )
import Data.Hashable (Hashable)
import Data.Kind (Type)
import qualified Data.Map.Strict as Map
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)
import qualified Test.QuickCheck as QC

import Data.CFTA.Equality (Edge (Edge), Node (Node))
import Data.CFTA.Gen.Error
import Data.CFTA.Gen.Internal.Bucket
import Data.CFTA.Gen.Internal.Inspection
import Data.CFTA.Gen.Internal.Recursive
import Data.CFTA.Gen.Internal.Static
import Data.CFTA.Gen.Label (Label (..))
import Data.CFTA.Index (Cardinality (..), Depth, Rank (..), Weight)
import Data.CFTA.Ranked.Internal.Decoder (RankDecoder (..), RankedValue (..))
import Data.CFTA.Ranked.Internal.Sampler
import Data.CFTA.Ranked.Internal.Size (MinimumSize, SizeIndex (minimumMemberSize), productIndex)
import Data.CFTA.Ranked.QuickCheck (QuickCheckBackend (..))

{- | A generator: the language it denotes and how it was built.

The language is inspectable ECTA structure, finite or recursive, or an
opaque QuickCheck generator. Its support is an automaton over 'Label': the
user's symbols, closed with @node@ or read from an imported automaton, and
the private labels of the engine. The recipe records the constructors,
choices, applications, and imports the generator was built from, so that a
theory whose constraints need a solver can fold it once the solver is at
hand; a language that the engine could build at construction is 'Built'.
-}
data Gen symbol a = Gen
    { genRecipe :: Recipe symbol a
    , genLanguage :: !(Language symbol a)
    }

-- | Inspectable ECTA structure, finite or recursive, or an opaque generator.
data Language symbol a
    = TransparentLanguage !(Either GenError (Static symbol a))
    | CyclicLanguage !(Either GenError (Recursive symbol a))
    | OpaqueLanguage !(QC.Gen (Either GenError a))

-- | A finite language, or the error that left it empty.
pattern Transparent :: Either GenError (Static symbol a) -> Gen symbol a
pattern Transparent result <- Gen _ (TransparentLanguage result)
  where
    Transparent result = Gen Built (TransparentLanguage result)

-- | A recursive language, or the error that left it empty.
pattern Cyclic :: Either GenError (Recursive symbol a) -> Gen symbol a
pattern Cyclic result <- Gen _ (CyclicLanguage result)
  where
    Cyclic result = Gen Built (CyclicLanguage result)

-- | An opaque QuickCheck generator.
pattern Opaque :: QC.Gen (Either GenError a) -> Gen symbol a
pattern Opaque generated <- Gen _ (OpaqueLanguage generated)
  where
    Opaque generated = Gen Built (OpaqueLanguage generated)

{-# COMPLETE Transparent, Cyclic, Opaque #-}

{- | How a generator was built.

Every combinator that a solver-backed compile step folds records itself
here: a lifted value, a map, an application, a constructor closed over a
child description with the constraint its edge carries, a weighted choice,
a uniform choice, an automaton import with its depth bound, and a leaf of
integers that a constraint narrows. Everything else, sources and joins and
recursion among them, is 'Built'. Its language is final, unless an input is
deferred. Then the generator is 'Transparent' with a
'SourceRequiresCompilation' error, and compile returns that error.
-}
data Recipe symbol a where
    Built :: Recipe symbol a
    Lifted :: a -> Recipe symbol a
    Mapped :: (a -> b) -> Gen symbol a -> Recipe symbol b
    Applied :: Gen symbol (a -> b) -> Gen symbol a -> Recipe symbol b
    Closed :: symbol -> Constraint -> Gen symbol a -> Recipe symbol a
    -- | A @pay@: the members of the generator, each one larger.
    Paid :: Gen symbol a -> Recipe symbol a
    -- | A constructor whose symbol is computed from the root symbols of its children, or an error.
    ClosedBy :: ([symbol] -> Either GenError symbol) -> Constraint -> Gen symbol a -> Recipe symbol a
    Chosen :: [(Weight, Gen symbol a)] -> Recipe symbol a
    -- | A choice weighted by the members of its alternatives, as 'uniformly' builds it, before compile counts them.
    Uniform :: [Gen symbol a] -> Recipe symbol a
    -- | An imported automaton, its depth bound, and the key that orders its constructors.
    Imported ::
        (Ord key) => Maybe Depth -> (symbol -> key) -> Node symbol -> Recipe symbol (Tree.Tree symbol)
    -- | A leaf of the integers that its constraint admits. The theory of the constraint counts them.
    Integers :: Constraint -> Recipe symbol Integer

-- | Record how a generator was built.
withRecipe :: Recipe symbol a -> Gen symbol a -> Gen symbol a
withRecipe recipe generator = generator{genRecipe = recipe}

-- | Whether a generator stands for a recursive language.
isRecursive :: Gen symbol a -> Bool
isRecursive (Cyclic _) = True
isRecursive _ = False

-- | Whether a generator is an opaque region, which cannot be inspected.
isOpaque :: Gen symbol a -> Bool
isOpaque (Opaque _) = True
isOpaque _ = False

{- | View any inspectable generator as a recursive one.

A finite generator is a recursive language that ends: its plan
already counts by size, and its support is already its automaton.
-}
recursiveView :: Gen symbol a -> Either GenError (Recursive symbol a)
recursiveView (Transparent result) = recursiveFromStatic <$> result
recursiveView (Cyclic result) = result
recursiveView (Opaque _) = Left CannotInspectOpaqueGenerator

-- | A generator whose values are classified by a projected key: one language per key.
data Grouped symbol key a
    = Grouped !(Either GenError (Map.Map key (KeyedBucket symbol a)))
    | -- | A recursive family: one language per key, all sharing one @Mu@.
      CyclicGrouped !(Either GenError (Map.Map key (KeyedRecursive symbol a)))

-- | Whether a grouped generator stands for a recursive family.
isRecursiveGrouped :: Grouped symbol key a -> Bool
isRecursiveGrouped (CyclicGrouped _) = True
isRecursiveGrouped _ = False

{- | View a grouped generator as a recursive family, one language per key.

A finite family is a recursive one that ends, so this is how the
recursive builders accept either.
-}
recursiveGroups ::
    Grouped symbol key a ->
    Either GenError (Map.Map key (KeyedRecursive symbol a))
recursiveGroups (CyclicGrouped result) = result
recursiveGroups (Grouped result) = keyedRecursiveFromBuckets <$> result

{- | Argument families for 'apply', one per signature component, in order.

Each link requires the family key type named by the corresponding signature
component and consumes the corresponding argument of the generated operation.
-}
data Args symbol (argKeys :: [Type]) operation result where
    ANil :: Args symbol '[] result result
    (:&) ::
        (Ord argKey) =>
        Grouped symbol argKey arg ->
        Args symbol argKeys operation result ->
        Args symbol (argKey ': argKeys) (arg -> operation) result

infixr 5 :&

-- | A generated child layer that can be closed with one visible constructor label.
class NodeLayer symbol layer | layer -> symbol where
    -- | Replace an open layer's private root with a domain constructor.
    closeNode :: symbol -> layer a -> layer a

{- | Close an applicative child description with one domain constructor.

The constructor pays, as in 'pay': every member is one larger.
-}
node :: (NodeLayer symbol layer) => symbol -> layer a -> layer a
node = closeNode

{- | Add one to the size of every member: the @pay@ of FEAT (Duregård, Jansson,
and Wang, "Feat: Functional Enumeration of Algebraic Types", Haskell
Symposium 2012).

Sizes count pays. 'pure' has size zero, '<*>' adds the sizes of its sides, and
'fmap' and the choices keep sizes. An atom ('elements', 'fromIndexed') has
size one, and a constructor ('node', 'leaf') pays one. So the 'Functor' and
'Applicative' laws hold for sizes. A recursion must reach its occurrence
through a pay, or through a product whose other side has no member of size
zero. A pay changes no term, rank, or value.
-}
pay :: Gen symbol a -> Gen symbol a
pay generator =
    withRecipe (Paid generator) $ case generator of
        Transparent result -> Transparent $ fmap payStatic result
        Cyclic result -> Cyclic $ fmap payRecursive result
        Opaque generated -> Opaque generated

instance (Hashable symbol, Typeable symbol) => NodeLayer symbol (Gen symbol) where
    closeNode symbol generator =
        withRecipe (Closed symbol noConstraint generator) $ case generator of
            Transparent result -> Transparent $ fmap (labelStatic symbol) result
            Cyclic result -> Cyclic $ fmap (labelRecursive symbol) result
            Opaque generated -> Opaque generated

instance (Hashable symbol, Typeable symbol) => NodeLayer symbol (Grouped symbol key) where
    closeNode symbol = nodeWithKey (const symbol)

-- | Close every group with a constructor computed from its key.
nodeWithKey ::
    (Hashable symbol, Typeable symbol) =>
    (key -> symbol) -> Grouped symbol key a -> Grouped symbol key a
nodeWithKey symbolOf (Grouped result) =
    Grouped $ fmap (Map.mapWithKey labelBucket) result
  where
    labelBucket key bucket =
        bucket
            { keyedBucketStatic =
                labelStatic (symbolOf key) $ keyedBucketStatic bucket
            }
nodeWithKey symbolOf (CyclicGrouped result) =
    CyclicGrouped $ fmap (Map.mapWithKey labelGroup) result
  where
    labelGroup key group =
        group
            { keyedRecursiveLanguage =
                labelRecursive (symbolOf key) $ keyedRecursiveLanguage group
            , keyedRecursiveMasses = payMassIndex (groupMinimum group) $ keyedRecursiveMasses group
            }

-- | 'pay' for every group of a grouped generator: every member is one larger.
payGrouped :: Grouped symbol key a -> Grouped symbol key a
payGrouped (Grouped result) =
    Grouped $ fmap (fmap $ \bucket -> bucket{keyedBucketStatic = payStatic $ keyedBucketStatic bucket}) result
payGrouped (CyclicGrouped result) =
    CyclicGrouped $ fmap (fmap payGroup) result
  where
    payGroup group =
        group
            { keyedRecursiveLanguage = payRecursive $ keyedRecursiveLanguage group
            , keyedRecursiveMasses = payMassIndex (groupMinimum group) $ keyedRecursiveMasses group
            }

-- | The minimum size of the language of one recursive group.
groupMinimum :: KeyedRecursive symbol a -> MinimumSize
groupMinimum = minimumMemberSize . recursiveIndex . keyedRecursiveLanguage

instance Functor (Grouped symbol key) where
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
        mapGroup group = group{keyedRecursiveLanguage = mapRecursive transform $ keyedRecursiveLanguage group}

instance Functor (Gen symbol) where
    fmap transform generator =
        withRecipe (Mapped transform generator) $ case generator of
            Transparent result -> Transparent $ fmap (mapStatic transform) result
            Cyclic result -> Cyclic $ fmap (mapRecursive transform) result
            Opaque generated -> Opaque $ fmap (fmap transform) generated

instance (Hashable symbol, Typeable symbol) => Applicative (Gen symbol) where
    pure value = withRecipe (Lifted value) $ Transparent $ Right $ pureStatic value

    functions <*> values = withRecipe (Applied functions values) $ applyLanguages functions values

-- | The applicative product of two languages.
applyLanguages ::
    (Hashable symbol, Typeable symbol) =>
    Gen symbol (a -> b) -> Gen symbol a -> Gen symbol b
applyLanguages functions values = case (functions, values) of
    (Transparent (Left err), _) -> Transparent $ Left err
    (_, Transparent (Left err)) -> Transparent $ Left err
    (Transparent (Right functionStatic), Transparent (Right valueStatic)) ->
        Transparent $ Right $ applyStatic functionStatic valueStatic
    _
        | isRecursive functions || isRecursive values ->
            Cyclic $ do
                left <- recursiveView functions
                right <- recursiveView values
                pure $
                    Recursive
                        ( Node
                            [ Edge
                                Apply
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
                        (productTerms (recursiveIndex left) (recursiveIndex right) <$> recursiveTerm left <*> recursiveTerm right)
                        ( Inspection Nothing $
                            Node
                                [ Edge (plainSymbol Apply) [inspectionGraph $ recursiveInspection left, inspectionGraph $ recursiveInspection right]
                                ]
                        )
        | otherwise ->
            Opaque $ liftA2 (<*>) (lower functions) (lower values)

-- | Lower to QuickCheck, preserving construction and decoding errors.
lower :: Gen symbol a -> QC.Gen (Either GenError a)
lower (Opaque generated) = generated
lower generator = runQuickCheckBackend $ lowerVia generator

-- | Lower an inspectable generator while retaining the sampled rank.
lowerWithRank :: Gen symbol a -> QC.Gen (Either GenError (RankedValue a))
lowerWithRank = runQuickCheckBackend . lowerWithRankVia

-- | Lower an inspectable generator through any sampling backend.
lowerVia :: (GenBackend gen) => Gen symbol a -> gen (Either GenError a)
lowerVia (Transparent (Left err)) = pure $ Left err
lowerVia (Transparent (Right static)) = sampleStatic static
lowerVia (Cyclic (Left err)) = pure $ Left err
lowerVia (Cyclic _) = pure $ Left UnboundedGenerator
lowerVia (Opaque _) = pure $ Left CannotInspectOpaqueGenerator

-- | 'lowerVia' retaining the sampled replay rank.
lowerWithRankVia :: (GenBackend gen) => Gen symbol a -> gen (Either GenError (RankedValue a))
lowerWithRankVia (Transparent (Left err)) = pure $ Left err
lowerWithRankVia (Transparent (Right static)) = sampleStaticWithRank static
lowerWithRankVia (Cyclic (Left err)) = pure $ Left err
lowerWithRankVia (Cyclic _) = pure $ Left UnboundedGenerator
lowerWithRankVia (Opaque _) = pure $ Left CannotInspectOpaqueGenerator

-- | Run the QuickCheck backend.
runQuickCheckBackend :: QuickCheckBackend a -> QC.Gen a
runQuickCheckBackend (QuickCheckBackend generated) = generated

-- | Lower a transparent uniform generator to a direct QuickCheck generator.
lowerUniform :: Gen symbol a -> Maybe (QC.Gen a)
lowerUniform (Transparent (Right static))
    | Just _ <- outcomeUniformMass outcomes =
        Just $ case outcomeDecoder outcomes of
            SmallDecoder bound decode -> decode <$> QC.chooseInt (0, bound - 1)
            LargeDecoder (Cardinality bound) decode -> decode . Rank <$> QC.chooseInteger (0, bound - 1)
  where
    outcomes = staticOutcomes static
lowerUniform _ = Nothing

-- | Like 'lowerUniform', retaining the sampled replay rank.
lowerUniformWithRank :: Gen symbol a -> Maybe (QC.Gen (RankedValue a))
lowerUniformWithRank (Transparent (Right static))
    | Just _ <- outcomeUniformMass outcomes =
        Just $ case outcomeDecoder outcomes of
            SmallDecoder bound decode ->
                (\index -> RankedValue (Rank $ toInteger index) (decode index)) <$> QC.chooseInt (0, bound - 1)
            LargeDecoder (Cardinality bound) decode ->
                (\index -> RankedValue (Rank index) (decode $ Rank index)) <$> QC.chooseInteger (0, bound - 1)
  where
    outcomes = staticOutcomes static
lowerUniformWithRank _ = Nothing

-- | Find the first invalid alternative weight.
firstNonPositiveWeight :: [(Weight, a)] -> Maybe Weight
firstNonPositiveWeight = go
  where
    go [] = Nothing
    go ((weight, _) : rest)
        | weight <= 0 = Just weight
        | otherwise = go rest

-- | Whether every alternative carries the same weight.
allWeightsEqual :: [(Weight, a)] -> Bool
allWeightsEqual [] = True
allWeightsEqual ((firstWeight, _) : rest) =
    all ((== firstWeight) . fst) rest
