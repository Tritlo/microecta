{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE KindSignatures #-}

{- | Derive a regular tree grammar and term codecs from an algebraic datatype.

Derive 'Generic', then declare an empty 'HasFTA' instance. Recursive fields
refer to the same type state. Atomic fields need an explicit finite domain.
The grammar describes constructor structure. Constraint layers add invariants.

Atomic types have no constructors in the grammar; their values are literals.
'Int', 'Integer', 'Char', and 'Text' are atomic. Make another type atomic
with @deriving via@, or with 'atomic' and handwritten codecs:

@
deriving via (Atomic Double) instance HasFTA Double
@
-}
module Data.Tree.FTA.Generic (
    HasFTA (..),
    Description,
    atomic,
    Atomic (..),
    TypedFTA,
    datatypeFTA,
    datatypeDecode,
    decodeLabelledTerm,
    annotateDatatype,
    deriveFTA,
    deriveFTAWith,
    Domains,
    domain,
    DeriveError (..),
    Constructor (..),
    Field (..),
    fieldNamed,
    constructorLabel,
) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, (<=<))
import Data.Bifunctor (first)
import Data.Containers.ListUtils (nubOrd)
import Data.Kind (Type)
import Data.List (find)
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (Proxy))
import Data.Text (Text)
import qualified Data.Tree as Tree
import Data.Typeable (TypeRep, Typeable, splitTyConApp, tyConModule, tyConName, tyConPackage, typeRep)
import GHC.Generics hiding (Constructor)
import qualified GHC.Generics as Generic
import Text.Read (readMaybe)

import qualified Data.Tree.FTA as FTA

-- | One constructor field, including its zero-based child position.
data Field = Field
    { fieldPosition :: !Int
    , fieldName :: !(Maybe String)
    , fieldType :: !TypeRep
    }
    deriving (Eq, Ord, Show)

-- | A constructor in one fully applied datatype, or one primitive literal.
data Constructor = Constructor
    { constructorType :: !TypeRep
    , constructorName :: !String
    , constructorFields :: ![Field]
    }
    deriving (Eq, Ord, Show)

-- | Find a named record field. Positional fields have no selector name.
fieldNamed :: String -> Constructor -> Maybe Field
fieldNamed name = find ((== Just name) . fieldName) . constructorFields

{- | A label that distinguishes constructor types and primitive values.

Type constructors include package, module, and type names, so the label is
unique within one build. The package component is the unit identifier, which
can change between builds; do not persist labels across builds. Length
prefixes keep names and type arguments distinct without depending on a
delimiter convention.
-}
constructorLabel :: Constructor -> String
constructorLabel constructor = encodeName (typeLabel $ constructorType constructor) <> encodeName (constructorName constructor)
  where
    encodeName name = show (length name) <> ":" <> name
    typeLabel typ =
        let (con, arguments) = splitTyConApp typ
         in concatMap encodeName [tyConPackage con, tyConModule con, tyConName con]
                <> show (length arguments)
                <> ":"
                <> concatMap (encodeName . typeLabel) arguments

-- | A checked datatype grammar with the matching typed decoder.
data TypedFTA guard a = TypedFTA
    { datatypeFTA :: !(FTA.FTA TypeRep Constructor guard)
    -- ^ The finite grammar, including any caller-supplied annotations.
    , datatypeDecode :: Tree.Tree Constructor -> Maybe a
    -- ^ Decode a value. The codec does not interpret transition annotations.
    }

-- | Annotate constructors while retaining the grammar and its typed codecs.
annotateDatatype :: (Constructor -> guard) -> TypedFTA old a -> TypedFTA guard a
annotateDatatype annotate datatype =
    datatype{datatypeFTA = FTA.annotate (\_ -> annotate . FTA.transitionSymbol) $ datatypeFTA datatype}

{- | Decode labels produced by 'constructorLabel'. Reject unknown labels.

Constraint layers can use their own interned string alphabet. The lookup table
is shared by all calls through one partially applied decoder.
-}
decodeLabelledTerm :: TypedFTA guard a -> Tree.Tree String -> Maybe a
decodeLabelledTerm datatype = datatypeDecode datatype <=< restore
  where
    constructors =
        Map.fromList
            [ (constructorLabel constructor, constructor)
            | transitions <- Map.elems $ FTA.transitionTable $ datatypeFTA datatype
            , transition <- transitions
            , let constructor = FTA.transitionSymbol transition
            ]
    restore = traverse (`Map.lookup` constructors)

-- | Finite literal alternatives for primitive field types.
newtype Domains = Domains (Map.Map TypeRep [Constructor])

instance Semigroup Domains where
    Domains left <> Domains right = Domains $ Map.union right left

instance Monoid Domains where
    mempty = Domains Map.empty

{- | Supply a finite domain for an atomic field type.

Built-in atomic types are 'Int', 'Integer', 'Char', and 'Text'. Repeated values
are removed in their first-occurrence order. An empty domain accepts nothing.
When domains are combined, the rightmost domain for a type takes precedence.
-}
domain :: forall a. (Typeable a, Show a) => [a] -> Domains
domain values = Domains $ Map.singleton typ $ nubOrd [Constructor typ (show value) [] | value <- values]
  where
    typ = typeRep (Proxy @a)

-- | Failure while deriving a finite grammar.
data DeriveError
    = -- | An atomic field type has no domain.
      MissingDomain !TypeRep
    | -- | A domain was supplied for a type that has constructors.
      NonAtomicDomain !TypeRep
    | -- | Recursion grows a type argument, so the state set is not finite.
      NonRegularRecursion !TypeRep !TypeRep
    | -- | The derived transition table is not a valid ranked grammar.
      InvalidDerivedFTA !(FTA.FTAError TypeRep Constructor)
    deriving (Eq, Show)

-- | Structural alternatives for one type. Child descriptions remain lazy.
data Description
    = AtomicType TypeRep
    | AlgebraicType TypeRep [(Constructor, [Description])]

-- | Describe a type whose values are literals from a finite domain.
atomic :: forall a. (Typeable a) => Proxy a -> Description
atomic = AtomicType . typeRep

{- | Make a type atomic through @deriving via@.

Literals are written with 'Show' and read back with 'Read'. The grammar and
the codecs use the type inside the wrapper, so the wrapper does not appear in
labels or domains.
-}
newtype Atomic a = Atomic a

instance (Typeable a, Show a, Read a) => HasFTA (Atomic a) where
    describeType _ = atomic (Proxy @a)
    encodeTerm (Atomic value) = encodeAtomic value
    decodeTerm = fmap Atomic . decodeAtomic

{- | Datatypes whose finite constructor structure has a regular tree grammar.

The default methods use 'Generic'. Declare an empty instance for each user
datatype in a recursive family. Codecs use the complete datatype; a finite
primitive domain restricts the derived grammar, not the codec itself.

A handwritten codec must keep 'decodeTerm' total on the terms of the derived
grammar, which are the terms 'encodeTerm' produces. The generators decode
generated terms without a fallback.
-}
class (Typeable a) => HasFTA a where
    -- | Describe the type as atomic, or as its constructors and their fields.
    describeType :: Proxy a -> Description
    default describeType :: (GConstructors (Rep a)) => Proxy a -> Description
    describeType proxy = AlgebraicType (typeRep proxy) $ gConstructors (typeRep proxy) (Proxy @(Rep a))

    -- | Encode a datatype value as a constructor term.
    encodeTerm :: a -> Tree.Tree Constructor
    default encodeTerm :: (Generic a, GConstructors (Rep a)) => a -> Tree.Tree Constructor
    encodeTerm = gEncode (typeRep $ Proxy @a) . from

    -- | Decode a constructor term. Reject wrong types, labels, and arities.
    decodeTerm :: Tree.Tree Constructor -> Maybe a
    default decodeTerm :: (Generic a, GConstructors (Rep a)) => Tree.Tree Constructor -> Maybe a
    decodeTerm = fmap to . gDecode (typeRep $ Proxy @a)

-- | Derive a grammar whose fields need no explicit atomic domains.
deriveFTA :: forall a. (HasFTA a) => Either DeriveError (TypedFTA () a)
deriveFTA = deriveFTAWith mempty

{- | Derive the reachable grammar without enumerating datatype values.

States are fully applied types. A repeated type reuses its row. Recursion that
grows a type argument is rejected before it can create an infinite state set.
The check is syntactic: a type constructor applied to a larger argument than
an ancestor on the same path is rejected, even when that growth would stop.
-}
deriveFTAWith :: forall a. (HasFTA a) => Domains -> Either DeriveError (TypedFTA () a)
deriveFTAWith (Domains domains) = do
    rows <- visit [] Map.empty (describeType $ Proxy @a)
    graph <- first InvalidDerivedFTA $ FTA.mkFTA (typeRep $ Proxy @a) (Map.toList rows)
    pure $ TypedFTA graph decodeTerm
  where
    visit ancestors rows description
        | Map.member typ rows = Right rows
        | Just prior <- find (growsInto typ) ancestors = Left $ NonRegularRecursion prior typ
        | otherwise = case description of
            AtomicType _ -> case Map.lookup typ domains of
                Nothing -> Left $ MissingDomain typ
                Just constructors -> Right $ Map.insert typ [FTA.Transition constructor [] () | constructor <- constructors] rows
            AlgebraicType _ constructors
                | Map.member typ domains -> Left $ NonAtomicDomain typ
                | otherwise ->
                    let transitions = [FTA.Transition constructor (map descriptionType children) () | (constructor, children) <- constructors]
                        allocated = Map.insert typ transitions rows
                     in foldM (visit $ typ : ancestors) allocated (concatMap snd constructors)
      where
        typ = descriptionType description
    growsInto typ ancestor =
        fst (splitTyConApp typ) == fst (splitTyConApp ancestor) && typeSize typ > typeSize ancestor
    typeSize typ = 1 + sum (map typeSize $ snd $ splitTyConApp typ) :: Integer

-- | Read the type identity without inspecting a recursive description.
descriptionType :: Description -> TypeRep
descriptionType (AtomicType typ) = typ
descriptionType (AlgebraicType typ _) = typ

-- | Generic sums retain constructor alternatives and their codecs.
class GConstructors (f :: Type -> Type) where
    gConstructors :: TypeRep -> Proxy f -> [(Constructor, [Description])]
    gEncode :: TypeRep -> f p -> Tree.Tree Constructor
    gDecode :: TypeRep -> Tree.Tree Constructor -> Maybe (f p)

instance (GConstructors f) => GConstructors (M1 D metadata f) where
    gConstructors typ _ = gConstructors typ (Proxy @f)
    gEncode typ (M1 value) = gEncode typ value
    gDecode typ = fmap M1 . gDecode typ

instance (GConstructors left, GConstructors right) => GConstructors (left :+: right) where
    gConstructors typ _ = gConstructors typ (Proxy @left) <> gConstructors typ (Proxy @right)
    gEncode typ (L1 value) = gEncode typ value
    gEncode typ (R1 value) = gEncode typ value
    gDecode typ term = (L1 <$> gDecode typ term) <|> (R1 <$> gDecode typ term)

instance (Generic.Constructor metadata, GFields fields) => GConstructors (M1 C metadata fields) where
    gConstructors typ _ = [(genericConstructor @metadata @fields typ, map snd $ gFields $ Proxy @fields)]
    gEncode typ (M1 fields) = Tree.Node (genericConstructor @metadata @fields typ) (gEncodeFields fields)
    gDecode typ (Tree.Node constructor children)
        | constructor == genericConstructor @metadata @fields typ = do
            (fields, rest) <- gDecodeFields children
            if null rest then Just $ M1 fields else Nothing
        | otherwise = Nothing

instance GConstructors V1 where
    gConstructors _ _ = []
    gEncode _ value = case value of {}
    gDecode _ _ = Nothing

-- | Construct metadata without evaluating any field value.
genericConstructor ::
    forall (metadata :: Meta) fields. (Generic.Constructor metadata, GFields fields) => TypeRep -> Constructor
genericConstructor typ =
    Constructor typ (conName (undefined :: M1 C metadata fields ())) $
        zipWith (\index (name, description) -> Field index name (descriptionType description)) [0 ..] (gFields $ Proxy @fields)

-- | Generic products retain field order and consume one term per field.
class GFields (f :: Type -> Type) where
    gFields :: Proxy f -> [(Maybe String, Description)]
    gEncodeFields :: f p -> [Tree.Tree Constructor]
    gDecodeFields :: [Tree.Tree Constructor] -> Maybe (f p, [Tree.Tree Constructor])

instance GFields U1 where
    gFields _ = []
    gEncodeFields U1 = []
    gDecodeFields terms = Just (U1, terms)

instance (HasFTA a) => GFields (K1 index a) where
    gFields _ = [(Nothing, describeType $ Proxy @a)]
    gEncodeFields (K1 value) = [encodeTerm value]
    gDecodeFields [] = Nothing
    gDecodeFields (term : rest) = (\value -> (K1 value, rest)) <$> decodeTerm term

instance (Selector metadata, GFields fields) => GFields (M1 S metadata fields) where
    gFields _ = [(name, description) | (_, description) <- gFields (Proxy @fields)]
      where
        name = case selName (undefined :: M1 S metadata fields ()) of
            "" -> Nothing
            selector -> Just selector
    gEncodeFields (M1 fields) = gEncodeFields fields
    gDecodeFields terms = do
        (fields, rest) <- gDecodeFields terms
        pure (M1 fields, rest)

instance (GFields left, GFields right) => GFields (left :*: right) where
    gFields _ = gFields (Proxy @left) <> gFields (Proxy @right)
    gEncodeFields (left :*: right) = gEncodeFields left <> gEncodeFields right
    gDecodeFields terms = do
        (left, remaining) <- gDecodeFields terms
        (right, rest) <- gDecodeFields remaining
        pure (left :*: right, rest)

-- | Encode one atomic value. Atomic constructor labels contain its literal.
encodeAtomic :: forall a. (Typeable a, Show a) => a -> Tree.Tree Constructor
encodeAtomic value = Tree.Node (Constructor (typeRep $ Proxy @a) (show value) []) []

-- | Decode a literal only when its type and nullary shape match.
decodeAtomic :: forall a. (Typeable a, Read a) => Tree.Tree Constructor -> Maybe a
decodeAtomic (Tree.Node (Constructor typ literal []) [])
    | typ == typeRep (Proxy @a) = readMaybe literal
decodeAtomic _ = Nothing

deriving via (Atomic Int) instance HasFTA Int
deriving via (Atomic Integer) instance HasFTA Integer
deriving via (Atomic Char) instance HasFTA Char
deriving via (Atomic Text) instance HasFTA Text

instance HasFTA Bool
instance HasFTA ()
instance (HasFTA a) => HasFTA [a]
instance (HasFTA a) => HasFTA (Maybe a)
instance (HasFTA a, HasFTA b) => HasFTA (Either a b)
instance (HasFTA a, HasFTA b) => HasFTA (a, b)
instance (HasFTA a, HasFTA b, HasFTA c) => HasFTA (a, b, c)
