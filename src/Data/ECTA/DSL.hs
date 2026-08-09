{-# LANGUAGE OverloadedStrings #-}

{- | A symbolic generator DSL for equality-constrained tree automata.

`choose` allocates one future value. Reusing that value records sharing, which
the elaborator turns into ECTA equality constraints. Applicative fields retain
concrete decoders. Typed and named constraint sources can add relationships
that come from independent code. Elaboration returns an ordinary raw ECTA.
`compileGenerator` reduces and compiles a finite generator for repeated decoded
sampling.
-}
module Data.ECTA.DSL (
    -- * Names
    Name,
    name,
    Selector,
    selector,
    renderSelector,

    -- * Generator construction
    Pool,
    pool,
    elements,
    Value,
    Gen,
    Fields,
    Generator,
    generator,
    choose,
    constant,
    construct,
    field,
    reference,
    elaborateGenerator,
    decodeGenerated,
    availableGeneratorSelectors,
    CompiledGenerator,
    GeneratorCompileError (..),
    GeneratorSampleError (..),
    compileGenerator,
    sampleGenerator,

    -- * Low-level schema construction
    Ref,
    Domain,
    Schema,
    Build,
    Children,
    schema,
    alternative,
    child,
    choice,
    empty,
    scope,
    recursive,
    embedRaw,

    -- * Constraint sources
    Constraints,
    Source,
    NamedEquality,
    source,
    namedSource,
    same,
    sameNamed,

    -- * Elaboration
    DslError (..),
    elaborate,
    availableSelectors,
) where

import Control.Monad.State.Strict (State, StateT, gets, modify', runState, runStateT)
import Control.Monad.Trans.Class (lift)
import qualified Data.IntMap.Strict as IntMap
import Data.Kind (Type)
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.String (IsString (..))
import Data.Text (Text)
import qualified Data.Text as Text

import Data.ECTA.Internal.ECTA.Generation (
    GenerationPlan,
    GenerationPlanError,
    compileGenerationPlan,
    sampleGenerationPlan,
 )
import Data.ECTA.Internal.ECTA.Operations (reducePartially, union)
import Data.ECTA.Internal.ECTA.Type (Node (EmptyNode, Node), createMu, mkEdge)
import Data.ECTA.Internal.Term (Symbol, Term (Term))
import Data.ECTA.Paths (Path, mkEqConstraints, path)

-- | One local field name or constraint-source name.
newtype Name = Name Text
    deriving (Eq, Ord)

instance IsString Name where
    fromString = Name . Text.pack

instance Show Name where
    show (Name value) = show value

-- | Construct a name from text.
name :: Text -> Name
name = Name

-- | A qualified field name, from the schema root to one child.
newtype Selector = Selector [Name]
    deriving (Eq, Ord)

instance Show Selector where
    show = show . renderSelector

-- | Construct a selector from its path segments.
selector :: [Name] -> Selector
selector = Selector

-- | Render a selector with dot separators.
renderSelector :: Selector -> Text
renderSelector (Selector parts) = Text.intercalate "." [part | Name part <- parts]

-- | Internal identity of one named child occurrence.
newtype AnchorId = AnchorId Int
    deriving (Eq, Ord, Show)

-- | Internal identity of one declared edge.
newtype EdgeId = EdgeId Int
    deriving (Eq, Ord, Show)

-- | Internal identity of one recursive binder.
newtype RecId = RecId Int
    deriving (Eq, Ord, Show)

-- | Internal identity of one symbolic generator value.
newtype ValueId = ValueId Int
    deriving (Eq, Ord, Show)

-- | A generator expression before it is elaborated to a raw ECTA.
data GenExpr
    = GenChoice Node
    | GenConstruct EdgeId Symbol [GenField]

-- | One named field and its symbolic value.
data GenField = GenField Name ValueId GenExpr

-- | A raw ECTA domain and its concrete-value decoder.
data Pool a = Pool Node (Term -> Either String a)

-- | A symbolic value produced by one generator construction.
data Value s a = Value ValueId GenExpr (Term -> Either String a)

-- | Pure state for allocating symbolic generator values.
newtype Gen s a = Gen (State BuildState a)
    deriving (Functor, Applicative, Monad)

-- | Applicative fields for one generated constructor.
data Fields s a = Fields [GenField] ([Term] -> Either String (a, [Term]))

-- | A closed generator, its public references, and its result decoder.
data Generator root (refs :: Type -> Type) where
    Generator :: GenExpr -> refs s -> (Term -> Either String root) -> Generator root refs

-- | A finite generation plan with its concrete-value decoder.
data CompiledGenerator root = CompiledGenerator GenerationPlan (Term -> Either String root)

-- | An error found while elaborating or compiling one generator.
data GeneratorCompileError
    = GeneratorDslError [DslError]
    | GeneratorPlanError GenerationPlanError
    deriving (Eq, Show)

-- | An error found while sampling or decoding one compiled generator.
data GeneratorSampleError
    = GeneratorSamplingError GenerationPlanError
    | GeneratorDecodeError String
    deriving (Eq, Show)

-- | Unelaborated node structure with stable declaration identities.
data DslNode
    = DslAlternatives [DslEdge]
    | DslChoice [DslNode]
    | DslEmpty
    | DslScope Name DslNode
    | DslRecursive RecId DslNode
    | DslRec RecId
    | DslRaw Node

-- | One unelaborated ECTA edge.
data DslEdge = DslEdge EdgeId Symbol [DslChild]

-- | One named edge child and its stable reference anchor.
data DslChild = DslChild Name AnchorId DslNode

-- | Internal target of one typed equality reference.
data RefTarget
    = AnchorTarget AnchorId
    | ValueTarget ValueId

-- | A reference to one symbolic value in schema @s@ with semantic sort @a@.
newtype Ref s a = Ref RefTarget

-- | A set of terms with semantic sort @a@ under schema scope @s@.
newtype Domain s a = Domain DslNode

-- | Identity supply for one closed schema construction.
data BuildState = BuildState
    { nextAnchor :: !Int
    , nextEdge :: !Int
    , nextRec :: !Int
    , nextValue :: !Int
    }

initialBuildState :: BuildState
initialBuildState = BuildState 0 0 0 0

instance Functor (Fields s) where
    fmap apply (Fields fields decodeFields) =
        Fields fields $ \terms -> do
            (value, remaining) <- decodeFields terms
            return (apply value, remaining)

instance Applicative (Fields s) where
    pure value = Fields [] $ \terms -> Right (value, terms)
    Fields functionFields decodeFunction <*> Fields valueFields decodeValue =
        Fields (functionFields <> valueFields) $ \terms -> do
            (function, afterFunction) <- decodeFunction terms
            (value, remaining) <- decodeValue afterFunction
            return (function value, remaining)

-- | Construct a typed pool from one raw ECTA and its decoder.
pool :: Node -> (Term -> Either String a) -> Pool a
pool = Pool

-- | Construct a finite pool from decoded leaf symbols.
elements :: [(Symbol, a)] -> Pool a
elements alternatives = Pool node decodeLeaf
  where
    node = Node [mkEdge symbol [] (mkEqConstraints []) | (symbol, _) <- alternatives]

    decodeLeaf (Term symbol []) =
        case lookup symbol alternatives of
            Just value -> Right value
            Nothing -> Left $ "unknown generated symbol: " <> show symbol
    decodeLeaf term = Left $ "expected a generated leaf: " <> show term

-- | Allocate one symbolic choice from a typed pool.
choose :: Pool a -> Gen s (Value s a)
choose (Pool node decodeValue) = Gen $ do
    valueId <- freshValueState
    return $ Value valueId (GenChoice node) decodeValue

-- | Allocate one decoded constant leaf.
constant :: Symbol -> a -> Gen s (Value s a)
constant symbol value = choose $ elements [(symbol, value)]

-- | Add one named symbolic value to an applicative constructor.
field :: Name -> Value s a -> Fields s a
field fieldName (Value valueId expression decodeValue) =
    Fields [GenField fieldName valueId expression] decodeField
  where
    decodeField (term : terms) = do
        value <- decodeValue term
        return (value, terms)
    decodeField [] = Left $ "missing generated field: " <> show fieldName

-- | Construct one symbolic term and its decoded value.
construct :: Symbol -> Fields s a -> Gen s (Value s a)
construct symbol (Fields fields decodeFields) = Gen $ do
    edgeId <- freshEdgeState
    valueId <- freshValueState
    return $ Value valueId (GenConstruct edgeId symbol fields) decodeValue
  where
    decodeValue term@(Term actual children)
        | actual /= symbol =
            Left $
                "expected generated constructor "
                    <> show symbol
                    <> ", got "
                    <> show term
        | otherwise = do
            (value, remaining) <- decodeFields children
            case remaining of
                [] -> Right value
                _ -> Left $ "too many fields in generated constructor: " <> show term

-- | Close one symbolic generator and retain its result decoder.
generator ::
    (forall s. Gen s (Value s root, refs s)) ->
    Generator root refs
generator build =
    case runState (runGen build) initialBuildState of
        ((Value _ expression decodeRoot, refs), _) ->
            Generator expression refs decodeRoot

-- | Convert one symbolic generator value to a typed equality reference.
reference :: Value s a -> Ref s a
reference (Value valueId _ _) = Ref $ ValueTarget valueId

-- | Decode one complete term produced by a generator.
decodeGenerated :: Generator root refs -> Term -> Either String root
decodeGenerated (Generator _ _ decodeRoot) = decodeRoot

{- | Compile one constrained finite generator.

Static reduction intersects the languages of equal values before plan
compilation. This permits independently authored generators to expose different
languages for one joined value.
-}
compileGenerator ::
    Generator root refs ->
    [Source refs] ->
    Either GeneratorCompileError (CompiledGenerator root)
compileGenerator generated@(Generator _ _ decodeRoot) sources = do
    node <- either (Left . GeneratorDslError) Right $ elaborateGenerator generated sources
    plan <- either (Left . GeneratorPlanError) Right $ compileGenerationPlan $ reducePartially node
    return $ CompiledGenerator plan decodeRoot

-- | Sample and decode one value from a compiled finite generator.
sampleGenerator ::
    (Int -> g -> (Int, g)) ->
    g ->
    CompiledGenerator root ->
    Either GeneratorSampleError (root, g)
sampleGenerator select initialState (CompiledGenerator plan decodeRoot) = do
    (term, finalState) <-
        either (Left . GeneratorSamplingError) Right $
            sampleGenerationPlan select initialState plan
    value <- either (Left . GeneratorDecodeError) Right $ decodeRoot term
    return (value, finalState)

-- | Unwrap one generator construction action.
runGen :: Gen s a -> State BuildState a
runGen (Gen action) = action

-- | Pure schema-construction state.
newtype Build s a = Build (State BuildState a)
    deriving (Functor, Applicative, Monad)

-- | Ordered child construction for one ECTA edge.
newtype Children s a = Children (StateT [DslChild] (Build s) a)
    deriving (Functor, Applicative, Monad)

-- | A closed schema and its public reference record.
data Schema root (refs :: Type -> Type) where
    Schema :: DslNode -> refs s -> Schema root refs

-- | Equality classes contributed by one typed source.
newtype Constraints s = Constraints [[RefTarget]]

instance Semigroup (Constraints s) where
    Constraints left <> Constraints right = Constraints (left <> right)

instance Monoid (Constraints s) where
    mempty = Constraints []

-- | One equality class written with qualified names.
newtype NamedEquality = NamedEquality [Selector]

-- | An independently authored typed or named constraint source.
data Source (refs :: Type -> Type) where
    TypedSource :: Name -> (forall s. refs s -> Constraints s) -> Source refs
    NamedSource :: Name -> [NamedEquality] -> Source refs

-- | An error found while references are resolved or constraints are placed.
data DslError
    = UnknownSelector Name Selector
    | AmbiguousSelector Name Selector
    | UnreachableReference Name Int
    | UnreachableValue Name Int
    | RepeatedReference Name [Selector]
    | ConstraintAcrossAlternatives Name [Selector]
    deriving (Eq, Show)

-- | Close one polymorphic schema construction.
schema :: (forall s. Build s (Domain s root, refs s)) -> Schema root refs
schema build =
    case runState (runBuild build) initialBuildState of
        ((Domain root, refs), _) -> Schema root refs

-- | Construct one ECTA edge and return its child references.
alternative :: Symbol -> Children s refs -> Build s (Domain s result, refs)
alternative symbol fields = do
    edgeId <- freshEdge
    (refs, reversedChildren) <- runChildren fields
    return
        ( Domain $ DslAlternatives [DslEdge edgeId symbol (reverse reversedChildren)]
        , refs
        )

-- | Add one named child and return its typed reference.
child :: Name -> Domain s value -> Children s (Ref s value)
child fieldName (Domain node) = Children $ do
    anchorId <- lift freshAnchor
    modify' (DslChild fieldName anchorId node :)
    return $ Ref $ AnchorTarget anchorId

-- | Combine domains as alternatives of one ECTA node.
choice :: [Domain s value] -> Domain s value
choice domains = Domain $ DslChoice [node | Domain node <- domains]

-- | The empty ECTA language.
empty :: Domain s value
empty = Domain DslEmpty

-- | Add a name prefix without changing the represented ECTA language.
scope :: Name -> Domain s value -> Domain s value
scope prefix (Domain node) = Domain $ DslScope prefix node

{- | Construct a recursive domain and return references from its body.

The callback receives the recursive domain. The DSL reifies the callback once
and later elaborates it with 'createMu'.
-}
recursive ::
    (Domain s value -> Build s (Domain s value, refs)) ->
    Build s (Domain s value, refs)
recursive buildBody = do
    recId <- freshRec
    (Domain body, refs) <- buildBody (Domain $ DslRec recId)
    return (Domain $ DslRecursive recId body, refs)

-- | Embed an existing raw ECTA as an opaque domain.
embedRaw :: Node -> Domain s value
embedRaw = Domain . DslRaw

-- | Construct one typed constraint source.
source :: Name -> (forall s. refs s -> Constraints s) -> Source refs
source = TypedSource

-- | Construct one name-resolved constraint source.
namedSource :: Name -> [NamedEquality] -> Source refs
namedSource = NamedSource

-- | Require all supplied typed references to denote equal subterms.
same :: [Ref s value] -> Constraints s
same refs = Constraints [[target | Ref target <- refs]]

-- | Require all supplied selectors to denote equal subterms.
sameNamed :: [Selector] -> NamedEquality
sameNamed = NamedEquality

-- | List every selector available to the named frontend.
availableSelectors :: Schema root refs -> [Selector]
availableSelectors (Schema root _) = Map.keys $ metadataSelectors $ collectMetadata root

-- | List every selector available in one symbolic generator.
availableGeneratorSelectors :: Generator root refs -> [Selector]
availableGeneratorSelectors (Generator root _ _) =
    Map.keys $ metadataSelectors $ collectGeneratorMetadata root

-- | Elaborate a schema and its constraint sources to a raw ECTA.
elaborate :: Schema root refs -> [Source refs] -> Either [DslError] Node
elaborate (Schema root refs) sources =
    case resolveSources metadata refs sources of
        (errors@(_ : _), _) -> Left errors
        ([], resolved) ->
            case placeConstraints resolved of
                Left errors -> Left errors
                Right placements -> Right $ elaborateNode placements IntMap.empty root
  where
    metadata = collectMetadata root

-- | Elaborate one symbolic generator and its independent constraints.
elaborateGenerator ::
    Generator root refs ->
    [Source refs] ->
    Either [DslError] Node
elaborateGenerator (Generator root refs _) sources =
    case resolveSources metadata refs sources of
        (errors@(_ : _), _) -> Left errors
        ([], resolved) ->
            case placeConstraints (sharingConstraints metadata <> resolved) of
                Left errors -> Left errors
                Right placements -> Right $ elaborateGeneratorNode placements root
  where
    metadata = collectGeneratorMetadata root

-- | Unwrap one schema construction action.
runBuild :: Build s a -> State BuildState a
runBuild (Build action) = action

-- | Run one ordered child declaration.
runChildren :: Children s a -> Build s (a, [DslChild])
runChildren (Children action) = runStateT action []

-- | Allocate one reference anchor.
freshAnchor :: Build s AnchorId
freshAnchor = Build $ do
    current <- gets nextAnchor
    modify' $ \state -> state{nextAnchor = current + 1}
    return $ AnchorId current

-- | Allocate one declared edge identity.
freshEdge :: Build s EdgeId
freshEdge = Build freshEdgeState

-- | Allocate one declared edge identity in the shared state.
freshEdgeState :: State BuildState EdgeId
freshEdgeState = do
    current <- gets nextEdge
    modify' $ \state -> state{nextEdge = current + 1}
    return $ EdgeId current

-- | Allocate one recursive binder identity.
freshRec :: Build s RecId
freshRec = Build $ do
    current <- gets nextRec
    modify' $ \state -> state{nextRec = current + 1}
    return $ RecId current

-- | Allocate one symbolic generator value identity.
freshValueState :: State BuildState ValueId
freshValueState = do
    current <- gets nextValue
    modify' $ \state -> state{nextValue = current + 1}
    return $ ValueId current

-- | One edge and child index on a reference route.
data RouteStep = RouteStep !EdgeId !Int
    deriving (Eq, Show)

-- | A route from the schema root to one reference anchor.
type Route = [RouteStep]

-- | One selector and its resolved route.
data Located = Located !Selector !Route

-- | Reference and selector indexes collected from a schema.
data Metadata = Metadata
    { metadataAnchors :: !(IntMap.IntMap [Located])
    , metadataValues :: !(IntMap.IntMap [Located])
    , metadataSelectors :: !(Map.Map Selector [Route])
    }

-- | An empty schema metadata index.
emptyMetadata :: Metadata
emptyMetadata = Metadata IntMap.empty IntMap.empty Map.empty

-- | Index all reachable anchors and qualified selectors.
collectMetadata :: DslNode -> Metadata
collectMetadata = collect [] [] emptyMetadata
  where
    collect route names metadata (DslAlternatives edges) =
        List.foldl' (collectEdge route names) metadata edges
    collect route names metadata (DslChoice nodes) =
        List.foldl' (collect route names) metadata nodes
    collect _ _ metadata DslEmpty = metadata
    collect route names metadata (DslScope prefix node) =
        collect route (names <> [prefix]) metadata node
    collect route names metadata (DslRecursive _ body) =
        collect route names metadata body
    collect _ _ metadata (DslRec _) = metadata
    collect _ _ metadata (DslRaw _) = metadata

    collectEdge route names metadata (DslEdge edgeId _ children) =
        List.foldl' collectChild metadata (zip [0 ..] children)
      where
        collectChild current (index, DslChild childName (AnchorId anchorId) node) =
            let childRoute = route <> [RouteStep edgeId index]
                childSelector = Selector $ names <> [childName]
                located = Located childSelector childRoute
                withAnchor =
                    current
                        { metadataAnchors =
                            IntMap.insertWith (<>) anchorId [located] (metadataAnchors current)
                        , metadataSelectors =
                            Map.insertWith (<>) childSelector [childRoute] (metadataSelectors current)
                        }
             in collect childRoute (names <> [childName]) withAnchor node

-- | Index every reachable value occurrence and qualified generator field.
collectGeneratorMetadata :: GenExpr -> Metadata
collectGeneratorMetadata = collect [] [] emptyMetadata
  where
    collect _ _ metadata (GenChoice _) = metadata
    collect route names metadata (GenConstruct edgeId _ fields) =
        List.foldl' collectField metadata (zip [0 ..] fields)
      where
        collectField current (index, GenField fieldName (ValueId valueId) expression) =
            let fieldRoute = route <> [RouteStep edgeId index]
                fieldSelector = Selector $ names <> [fieldName]
                located = Located fieldSelector fieldRoute
                withValue =
                    current
                        { metadataValues =
                            IntMap.insertWith (<>) valueId [located] (metadataValues current)
                        , metadataSelectors =
                            Map.insertWith (<>) fieldSelector [fieldRoute] (metadataSelectors current)
                        }
             in collect fieldRoute (names <> [fieldName]) withValue expression

-- | Turn repeated symbolic values into implicit equality constraints.
sharingConstraints :: Metadata -> [ResolvedConstraint]
sharingConstraints metadata =
    [ ResolvedConstraint "generator-sharing" locations
    | locations <- IntMap.elems $ metadataValues metadata
    , length locations > 1
    ]

-- | One equality class after typed or named reference resolution.
data ResolvedConstraint = ResolvedConstraint !Name ![Located]

-- | Resolve all typed and named constraint sources.
resolveSources ::
    Metadata ->
    refs s ->
    [Source refs] ->
    ([DslError], [ResolvedConstraint])
resolveSources metadata refs = foldMap resolveSource
  where
    resolveSource (TypedSource sourceName buildConstraints) =
        let Constraints classes = buildConstraints refs
         in foldMap (resolveTyped sourceName) classes
    resolveSource (NamedSource sourceName equalities) =
        foldMap (resolveNamed sourceName) equalities

    resolveTyped sourceName targets =
        case partitionEithers $ map (resolveTarget sourceName) targets of
            ([], locations) ->
                ([], [ResolvedConstraint sourceName (concat locations)])
            (errors, _) -> (errors, [])
    resolveNamed sourceName (NamedEquality selectors) =
        collectResolved sourceName $ map (resolveSelector sourceName) selectors

    resolveTarget sourceName (AnchorTarget (AnchorId anchorId)) =
        case IntMap.findWithDefault [] anchorId (metadataAnchors metadata) of
            [] -> Left $ UnreachableReference sourceName anchorId
            [located] -> Right [located]
            located ->
                Left $ RepeatedReference sourceName [selected | Located selected _ <- located]
    resolveTarget sourceName (ValueTarget (ValueId valueId)) =
        case IntMap.findWithDefault [] valueId (metadataValues metadata) of
            [] -> Left $ UnreachableValue sourceName valueId
            locations -> Right locations

    resolveSelector sourceName selected =
        case Map.findWithDefault [] selected (metadataSelectors metadata) of
            [] -> Left $ UnknownSelector sourceName selected
            [route] -> Right $ Located selected route
            _ -> Left $ AmbiguousSelector sourceName selected

    collectResolved sourceName results =
        case partitionEithers results of
            ([], located) -> ([], [ResolvedConstraint sourceName located])
            (errors, _) -> (errors, [])

-- | Partition errors and successful values without an extra dependency.
partitionEithers :: [Either a b] -> ([a], [b])
partitionEithers = foldr collect ([], [])
  where
    collect (Left left) (lefts, rights) = (left : lefts, rights)
    collect (Right right) (lefts, rights) = (lefts, right : rights)

-- | Place each equality class on its deepest common edge.
placeConstraints ::
    [ResolvedConstraint] ->
    Either [DslError] (Map.Map EdgeId [[Path]])
placeConstraints constraints =
    case partitionEithers $ map place constraints of
        ([], placed) ->
            Right $ Map.fromListWith (<>) [placement | placement@(_, _ : _) <- placed]
        (errors, _) -> Left errors
  where
    place (ResolvedConstraint _ []) = Right (EdgeId (-1), [])
    place (ResolvedConstraint _ [_]) = Right (EdgeId (-1), [])
    place (ResolvedConstraint sourceName located) =
        case deepestCommonEdge [route | Located _ route <- located] of
            Nothing ->
                Left $
                    ConstraintAcrossAlternatives
                        sourceName
                        [selected | Located selected _ <- located]
            Just (edgeId, paths) -> Right (edgeId, [paths])

-- | Find the deepest edge shared by every reference route.
deepestCommonEdge :: [Route] -> Maybe (EdgeId, [Path])
deepestCommonEdge routes = go routes
  where
    go current = do
        firstSteps <- traverse unconsStep current
        case firstSteps of
            [] -> Nothing
            (RouteStep firstEdge firstIndex, _) : otherSteps
                | all (sameEdge firstEdge) otherSteps ->
                    let here =
                            ( firstEdge
                            , [path [index | RouteStep _ index <- route] | route <- current]
                            )
                        remaining = [rest | (_, rest) <- firstSteps]
                     in if all (sameIndex firstIndex) otherSteps
                            && all (not . null) remaining
                            then go remaining
                            else Just here
                | otherwise -> Nothing

    unconsStep [] = Nothing
    unconsStep (value : values) = Just (value, values)

    sameEdge expected (RouteStep actual _, _) = expected == actual
    sameIndex expected (RouteStep _ actual, _) = expected == actual

-- | Convert the declarative tree and placed constraints to raw ECTA nodes.
elaborateNode :: Map.Map EdgeId [[Path]] -> IntMap.IntMap Node -> DslNode -> Node
elaborateNode placements recs = go
  where
    go (DslAlternatives edges) = Node $ map elaborateEdge edges
    go (DslChoice nodes) = union $ map go nodes
    go DslEmpty = EmptyNode
    go (DslScope _ node) = go node
    go (DslRecursive (RecId recId) body) =
        createMu $ \self -> elaborateNode placements (IntMap.insert recId self recs) body
    go (DslRec (RecId recId)) =
        case IntMap.lookup recId recs of
            Just node -> node
            Nothing -> error "Data.ECTA.DSL.elaborateNode: unbound recursive reference"
    go (DslRaw node) = node

    elaborateEdge (DslEdge edgeId symbol children) =
        mkEdge
            symbol
            [go childNode | DslChild _ _ childNode <- children]
            (mkEqConstraints $ Map.findWithDefault [] edgeId placements)

-- | Convert one symbolic generator expression to a raw ECTA node.
elaborateGeneratorNode :: Map.Map EdgeId [[Path]] -> GenExpr -> Node
elaborateGeneratorNode _ (GenChoice node) = node
elaborateGeneratorNode placements (GenConstruct edgeId symbol fields) =
    Node
        [ mkEdge
            symbol
            [elaborateGeneratorNode placements expression | GenField _ _ expression <- fields]
            (mkEqConstraints $ Map.findWithDefault [] edgeId placements)
        ]
