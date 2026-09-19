{-# LANGUAGE TupleSections #-}

{- | Ordinary finite-language generators over plain automata.

The interned node remains the inspectable support. This module adds exact
cardinality, stable replay ranks, backend-independent sampling, and
structural shrinking. Ranks identify accepting derivations; an ambiguous
automaton may therefore produce the same concrete term at more than one rank.
A construction failure stays inside the generator; 'cardinality' and
'Data.CFTA.Gen.QuickCheck.toGen' report it.
-}
module Data.CFTA.Gen (
    FTAGen,
    Children,
    NodeLayer,
    GenError (..),
    explain,
    leaf,
    node,
    frequency,
    oneof,
    children,
    applyChildren,
    toRanked,
    cardinality,
    unrank,
    termAt,
    shrinkRank,
    smallerMembers,
    support,
    fromAutomaton,
    fromAutomatonUpToSize,
    fromAutomatonUpToDepth,
    fromDatatypeUpToDepth,
    fromDatatypeUpToSize,
) where

import Data.Bifunctor (first)
import Data.Hashable (Hashable)
import qualified Data.Map.Lazy as Map
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import qualified Data.CFTA as FTA
import Data.CFTA.Gen.Error (GenError (..), explain, fromRankedError)
import qualified Data.CFTA.Gen.Internal.Automaton as Automaton
import Data.CFTA.Generic (Constructor, TypedFTA, datatypeDecode, datatypeFTA)
import Data.CFTA.Interned (
    Edge (Edge),
    Node (EmptyNode, Node),
    PlainNode,
    boundDepth,
    freeVars,
    nodeIdentity,
    numNestedMu,
    union,
 )
import Data.CFTA.Ranked (Ranked)
import qualified Data.CFTA.Ranked as Ranked
import qualified Data.CFTA.Ranked.Internal as Internal
import Data.CFTA.Ranked.Internal.Size (SizeIndex)
import Data.CFTA.Refinement (AutomatonError (OpenAutomaton))

-- | A finite ranked language whose members retain their terms, or the failure that left it empty.
newtype FTAGen symbol a = FTAGen (Either GenError (Ranked (Generated symbol a)))

-- | One generated value paired with its tree witness.
data Generated symbol a = Generated
    { generatedValue :: a
    , generatedWitness :: !(Tree.Tree symbol)
    }

-- | Applicatively assembled child positions awaiting one constructor label.
newtype Children symbol a = Children (Either GenError (Ranked (Forest symbol a)))

-- | An applicative result and its direct constructor-child witnesses.
data Forest symbol a = Forest
    { forestValue :: a
    , forestWitnesses :: ![Tree.Tree symbol]
    }

-- | A child language or forest that one constructor can contain.
class NodeLayer layer where
    -- | Read the direct children of one constructor.
    asChildren :: layer symbol a -> Children symbol a

instance NodeLayer FTAGen where
    asChildren = children

instance NodeLayer Children where
    asChildren = id

instance Functor (FTAGen symbol) where
    fmap transform (FTAGen ranked) =
        FTAGen $ fmap (mapGenerated transform) <$> ranked
      where
        mapGenerated function generated =
            generated{generatedValue = function $ generatedValue generated}

instance Functor (Children symbol) where
    fmap transform (Children ranked) =
        Children $ fmap (mapForest transform) <$> ranked
      where
        mapForest function forest =
            forest{forestValue = function $ forestValue forest}

instance Applicative (Children symbol) where
    pure value = Children $ Right $ pure $ Forest value []

    Children functions <*> Children arguments =
        Children $ (\fs as -> applyForest <$> fs <*> as) <$> functions <*> arguments
      where
        applyForest function argument =
            Forest
                (forestValue function $ forestValue argument)
                (forestWitnesses function <> forestWitnesses argument)

-- | A generator that failed to construct.
failed :: GenError -> FTAGen symbol a
failed = FTAGen . Left

-- | Build one nullary constructor.
leaf :: a -> symbol -> FTAGen symbol a
leaf value symbol =
    FTAGen $ Right $ pure $ Generated value (Tree.Node symbol [])

{- | Close an applicative child forest with one constructor label.

With @QualifiedDo@ and @ApplicativeDo@:

@node "pair" $ FTA.do ...@
-}
node :: (NodeLayer layer) => symbol -> layer symbol a -> FTAGen symbol a
node symbol layer =
    FTAGen $ fmap close <$> ranked
  where
    Children ranked = asChildren layer

    close forest =
        Generated
            (forestValue forest)
            (Tree.Node symbol $ forestWitnesses forest)

{- | Choose among languages with positive relative weights.

The weights decide sampling only; ranks list the alternatives in order. A
failed alternative or a non-positive weight fails the choice.
-}
frequency :: [(Integer, FTAGen symbol a)] -> FTAGen symbol a
frequency alternatives = FTAGen $ do
    weighted <- traverse (\(weight, FTAGen ranked) -> (,) weight <$> ranked) alternatives
    first fromRankedError $ Ranked.frequency weighted

-- | Choose equally among languages.
oneof :: [FTAGen symbol a] -> FTAGen symbol a
oneof = frequency . map (1,)

-- | Treat one language as one child position.
children :: FTAGen symbol a -> Children symbol a
children (FTAGen ranked) =
    Children $ fmap toForest <$> ranked
  where
    toForest generated =
        Forest (generatedValue generated) [generatedWitness generated]

-- | Apply one child-forest function to another child forest.
applyChildren :: Children symbol (a -> b) -> Children symbol a -> Children symbol b
applyChildren = (<*>)

-- | Forget retained witness terms and expose the ranked value language.
toRanked :: FTAGen symbol a -> Either GenError (Ranked a)
toRanked (FTAGen ranked) = fmap generatedValue <$> ranked

-- | Number of stable ranks in a finite generator.
cardinality :: FTAGen symbol a -> Either GenError Integer
cardinality = fmap Ranked.cardinality . toRanked

-- | Replay one generated value by rank.
unrank :: FTAGen symbol a -> Integer -> Either GenError a
unrank generator rank = do
    ranked <- toRanked generator
    first fromRankedError $ Ranked.unrank ranked rank

-- | Inspect the concrete witness retained at one rank.
termAt :: FTAGen symbol a -> Integer -> Either GenError (Tree.Tree symbol)
termAt (FTAGen ranked) rank = do
    language <- ranked
    generatedWitness <$> first fromRankedError (Ranked.unrank language rank)

-- | Structurally smaller ranks of a rank, as 'Ranked.shrinkRank' orders them. A failed generator has none.
shrinkRank :: FTAGen symbol a -> Integer -> [Integer]
shrinkRank generator rank = either (const []) (`Ranked.shrinkRank` rank) (toRanked generator)

-- | Every structurally smaller member of a rank, with its rank.
smallerMembers :: FTAGen symbol a -> Integer -> [(Integer, a)]
smallerMembers generator rank = either (const []) (`Ranked.smallerMembers` rank) (toRanked generator)

{- | Build the exact support of a finite generator as an interned automaton.

Equal subterms share one node. This decodes every rank, so use it on small
languages only.
-}
support :: (Hashable symbol, Typeable symbol) => FTAGen symbol a -> Either GenError (PlainNode symbol)
support generator = do
    total <- cardinality generator
    terms <- traverse (termAt generator) [0 .. total - 1]
    pure $ union $ map termNode terms
  where
    termNode (Tree.Node symbol subterms) = Node [Edge symbol $ map termNode subterms]

{- | Compile an acyclic automaton into its finite accepting derivations.

Each node shares its compiled decoder across all incoming edges. Ranks and
structural shrinking retain the alternative and child order. A recursive
automaton fails with 'UnboundedGenerator'; bound it with
'fromAutomatonUpToDepth' or 'fromAutomatonUpToSize'.
-}
fromAutomaton :: (Hashable symbol, Typeable symbol) => PlainNode symbol -> FTAGen symbol (Tree.Tree symbol)
fromAutomaton EmptyNode = failed EmptyGenerator
fromAutomaton root
    | not $ Set.null $ freeVars root = failed $ InvalidSupport OpenAutomaton
    | numNestedMu root > 0 = failed UnboundedGenerator
    | otherwise = fromTable (nodeIdentity root) (Automaton.rowsOf root)

{- | Compile all accepting runs with at most the given number of tree nodes.

Cycles are valid. Ranks use size-major order, including for acyclic automata.
Ambiguous terms retain one rank per accepting run. A non-positive bound or an
empty bounded language gives 'EmptyGenerator'.
-}
fromAutomatonUpToSize ::
    (Hashable symbol, Typeable symbol) => Int -> PlainNode symbol -> FTAGen symbol (Tree.Tree symbol)
fromAutomatonUpToSize _ EmptyNode = failed EmptyGenerator
fromAutomatonUpToSize bound root
    | not $ Set.null $ freeVars root = failed $ InvalidSupport OpenAutomaton
    | otherwise = fromSizeIndex bound $ Automaton.tableIndex (nodeIdentity root) (Automaton.rowsOf root)

{- | Compile every accepting run up to the given constructor depth.

A leaf has depth zero. Ranks retain alternative and child order in the bounded
graph. This is a depth bound, whereas 'fromAutomatonUpToSize' bounds all tree
nodes. The only possible failure is 'EmptyGenerator'.
-}
fromAutomatonUpToDepth ::
    (Hashable symbol, Typeable symbol) => Int -> PlainNode symbol -> FTAGen symbol (Tree.Tree symbol)
fromAutomatonUpToDepth bound = fromAutomaton . boundDepth bound

{- | Generate datatype values from the derived grammar up to constructor depth.

The value and its original constructor term share one rank. Codecs are applied
only when a selected value is demanded. A leaf has depth zero.
-}
fromDatatypeUpToDepth :: Int -> TypedFTA () a -> FTAGen Constructor a
fromDatatypeUpToDepth bound datatype =
    fromDatatypeTerms datatype $ fromTable (FTA.initialState bounded) (FTA.transitionTable bounded)
  where
    bounded = FTA.boundDepth bound $ datatypeFTA datatype

-- | Generate datatype values in size-major order with uniform rank sampling.
fromDatatypeUpToSize :: Int -> TypedFTA () a -> FTAGen Constructor a
fromDatatypeUpToSize bound datatype =
    fromDatatypeTerms datatype $ fromSizeIndex bound $ Automaton.automatonIndex $ datatypeFTA datatype

-- | Retain the witness while decoding a term from its own datatype grammar.
fromDatatypeTerms :: TypedFTA () a -> FTAGen Constructor (Tree.Tree Constructor) -> FTAGen Constructor a
fromDatatypeTerms datatype (FTAGen ranked) = FTAGen $ fmap generated <$> ranked
  where
    generated term = Generated (decode $ generatedWitness term) (generatedWitness term)
    decode term = case datatypeDecode datatype term of
        Just value -> value
        Nothing ->
            error
                "microcfta-generator bug in Data.CFTA.Gen.fromDatatypeTerms: \
                \the derived codec rejected a term of its own grammar"

-- | A size-major language, or 'EmptyGenerator' when the bound admits no term.
fromSizeIndex :: Int -> SizeIndex (Tree.Tree symbol) -> FTAGen symbol (Tree.Tree symbol)
fromSizeIndex bound index =
    FTAGen $ first (const EmptyGenerator) $ fmap witness <$> Internal.fromSizeIndex bound index

-- | Compile the accepting derivations of an acyclic table from its initial state.
fromTable :: (Ord state) => state -> Map.Map state [FTA.Transition state symbol ()] -> FTAGen symbol (Tree.Tree symbol)
fromTable initial rows =
    FTAGen $ maybe (Left EmptyGenerator) (Right . fmap witness) (compileState initial)
  where
    -- The lazy table permits references to states compiled from the same table.
    compiled = Map.map compileTransitions rows

    compileState state = Map.findWithDefault Nothing state compiled

    compileTransitions = fmap Internal.share . combine . mapMaybe compileTransition

    compileTransition transition = do
        childLanguages <- traverse compileState (FTA.transitionChildren transition)
        pure $ buildTerm (FTA.transitionSymbol transition) childLanguages

    combine [] = Nothing
    combine alternatives = either (const Nothing) Just $ Ranked.oneof alternatives

-- | A term as its own witness.
witness :: Tree.Tree symbol -> Generated symbol (Tree.Tree symbol)
witness term = Generated term term

-- | Apply a constructor to its independently ranked children.
buildTerm :: symbol -> [Ranked (Tree.Tree symbol)] -> Ranked (Tree.Tree symbol)
buildTerm symbol childLanguages =
    ($ [])
        <$> foldl'
            applyChild
            (pure $ Tree.Node symbol)
            childLanguages
  where
    applyChild partial child =
        (\finish value rest -> finish (value : rest)) <$> partial <*> child
