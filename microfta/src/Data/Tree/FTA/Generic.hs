{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{- | Derive a regular tree grammar and term codecs from an algebraic datatype.

Derive 'Generic', then declare an empty 'HasFTA' instance. Recursive fields
refer to the same type state. Primitive fields need an explicit finite domain.
The grammar describes constructor structure. Constraint layers add invariants.
-}
module Data.Tree.FTA.Generic (
    HasFTA (encodeTerm, decodeTerm),
    TypedFTA,
    datatypeFTA,
    datatypeEncode,
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
import Control.Monad (foldM)
import Data.Hashable (Hashable (hashWithSalt))
import Data.Kind (Type)
import Data.List (find)
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (Proxy))
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Typeable (TypeRep, Typeable, splitTyConApp, tyConModule, tyConName, tyConPackage, typeRep)
import GHC.Generics hiding (Constructor)
import qualified GHC.Generics as Generic
import Text.Read (readMaybe)

import qualified Data.Tree.FTA as FTA
import Data.Tree.Term (Term (Term))

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

instance Hashable Constructor where
    hashWithSalt salt constructor =
        salt
            `hashWithSalt` constructorLabel constructor
            `hashWithSalt` [(fieldPosition field, fieldName field, show $ fieldType field) | field <- constructorFields constructor]

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
    , datatypeEncode :: a -> Term Constructor
    -- ^ Encode a value. The codec does not restrict the configured domains.
    , datatypeDecode :: Term Constructor -> Maybe a
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
decodeLabelledTerm :: TypedFTA guard a -> Term String -> Maybe a
decodeLabelledTerm datatype = (>>= datatypeDecode datatype) . restore
  where
    constructors =
        Map.fromList
            [(constructorLabel constructor, constructor) | transitions <- Map.elems $ FTA.transitionTable $ datatypeFTA datatype, transition <- transitions, let constructor = FTA.transitionSymbol transition]
    restore (Term label children) = Term <$> Map.lookup label constructors <*> traverse restore children

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
domain values = Domains $ Map.singleton typ $ unique Set.empty [Constructor typ (show value) [] | value <- values]
  where
    typ = typeRep (Proxy @a)
    unique _ [] = []
    unique seen (value : rest)
        | Set.member value seen = unique seen rest
        | otherwise = value : unique (Set.insert value seen) rest

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
    = Atomic TypeRep
    | Algebraic TypeRep [(Constructor, [Description])]

{- | Datatypes whose finite constructor structure has a regular tree grammar.

The default methods use 'Generic'. Declare an empty instance for each user
datatype in a recursive family. Codecs use the complete datatype; a finite
primitive domain restricts the derived grammar, not the codec itself.

A handwritten codec must keep 'decodeTerm' total on the terms of the derived
grammar, which are the terms 'encodeTerm' produces. The generators decode
generated terms without a fallback.
-}
class (Typeable a) => HasFTA a where
    describeType :: Proxy a -> Description
    default describeType :: (GConstructors (Rep a)) => Proxy a -> Description
    describeType proxy = Algebraic (typeRep proxy) $ gConstructors (typeRep proxy) (Proxy @(Rep a))

    -- | Encode a datatype value as a constructor term.
    encodeTerm :: a -> Term Constructor
    default encodeTerm :: (Generic a, GConstructors (Rep a)) => a -> Term Constructor
    encodeTerm = gEncode (typeRep $ Proxy @a) . from

    -- | Decode a constructor term. Reject wrong types, labels, and arities.
    decodeTerm :: Term Constructor -> Maybe a
    default decodeTerm :: (Generic a, GConstructors (Rep a)) => Term Constructor -> Maybe a
    decodeTerm = fmap to . gDecode (typeRep $ Proxy @a)

-- | Derive a grammar whose fields need no explicit atomic domains.
deriveFTA :: forall a. (HasFTA a) => Either DeriveError (TypedFTA () a)
deriveFTA = deriveFTAWith mempty

{- | Derive the reachable grammar without enumerating datatype values.

States are fully applied types. A repeated type reuses its row. Recursion that
grows a type argument is rejected before it can create an infinite state set.
-}
deriveFTAWith :: forall a. (HasFTA a) => Domains -> Either DeriveError (TypedFTA () a)
deriveFTAWith (Domains domains) = do
    rows <- visit [] Map.empty (describeType $ Proxy @a)
    graph <- either (Left . InvalidDerivedFTA) Right $ FTA.mkFTA (typeRep $ Proxy @a) (Map.toList rows)
    pure $ TypedFTA graph encodeTerm decodeTerm
  where
    visit ancestors rows description
        | Map.member typ rows = Right rows
        | Just prior <- find (growsInto typ) ancestors = Left $ NonRegularRecursion prior typ
        | otherwise = case description of
            Atomic _ -> case Map.lookup typ domains of
                Nothing -> Left $ MissingDomain typ
                Just constructors -> Right $ Map.insert typ [FTA.Transition constructor [] () | constructor <- constructors] rows
            Algebraic _ constructors
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
descriptionType (Atomic typ) = typ
descriptionType (Algebraic typ _) = typ

-- | Generic sums retain constructor alternatives and their codecs.
class GConstructors (f :: Type -> Type) where
    gConstructors :: TypeRep -> Proxy f -> [(Constructor, [Description])]
    gEncode :: TypeRep -> f p -> Term Constructor
    gDecode :: TypeRep -> Term Constructor -> Maybe (f p)

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
    gEncode typ (M1 fields) = Term (genericConstructor @metadata @fields typ) (gEncodeFields fields)
    gDecode typ (Term constructor children)
        | constructor == genericConstructor @metadata @fields typ = do
            (fields, rest) <- gDecodeFields children
            if null rest then Just $ M1 fields else Nothing
        | otherwise = Nothing

instance GConstructors V1 where
    gConstructors _ _ = []
    gEncode _ value = case value of {}
    gDecode _ _ = Nothing

-- | Construct metadata without evaluating any field value.
genericConstructor :: forall (metadata :: Meta) fields. (Generic.Constructor metadata, GFields fields) => TypeRep -> Constructor
genericConstructor typ =
    Constructor typ (conName (undefined :: M1 C metadata fields ())) $
        zipWith (\index (name, description) -> Field index name (descriptionType description)) [0 ..] (gFields $ Proxy @fields)

-- | Generic products retain field order and consume one term per field.
class GFields (f :: Type -> Type) where
    gFields :: Proxy f -> [(Maybe String, Description)]
    gEncodeFields :: f p -> [Term Constructor]
    gDecodeFields :: [Term Constructor] -> Maybe (f p, [Term Constructor])

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
encodeAtomic :: forall a. (Typeable a, Show a) => a -> Term Constructor
encodeAtomic value = Term (Constructor (typeRep $ Proxy @a) (show value) []) []

-- | Decode a literal only when its type and nullary shape match.
decodeAtomic :: forall a. (Typeable a, Read a) => Term Constructor -> Maybe a
decodeAtomic (Term (Constructor typ literal []) [])
    | typ == typeRep (Proxy @a) = readMaybe literal
decodeAtomic _ = Nothing

instance HasFTA Int where
    describeType = Atomic . typeRep
    encodeTerm = encodeAtomic
    decodeTerm = decodeAtomic

instance HasFTA Integer where
    describeType = Atomic . typeRep
    encodeTerm = encodeAtomic
    decodeTerm = decodeAtomic

instance HasFTA Char where
    describeType = Atomic . typeRep
    encodeTerm = encodeAtomic
    decodeTerm = decodeAtomic

instance HasFTA Text where
    describeType = Atomic . typeRep
    encodeTerm = encodeAtomic
    decodeTerm = decodeAtomic

instance HasFTA Bool
instance HasFTA ()
instance (HasFTA a) => HasFTA [a]
instance (HasFTA a) => HasFTA (Maybe a)
instance (HasFTA a, HasFTA b) => HasFTA (Either a b)
instance (HasFTA a, HasFTA b) => HasFTA (a, b)
instance (HasFTA a, HasFTA b, HasFTA c) => HasFTA (a, b, c)
