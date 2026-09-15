{- | Compile ordinary finite-language FTAs into ranked generators.

The FTA remains the inspectable support. This module adds exact cardinality,
stable replay ranks, backend-independent sampling, and structural shrinking.
Ranks identify accepting derivations; an ambiguous FTA may therefore produce
the same concrete term at more than one rank.
-}
module Data.Tree.FTA.Gen (
    FTAGen,
    Children,
    NodeLayer,
    CompileError (..),
    leaf,
    node,
    frequency,
    oneof,
    children,
    applyChildren,
    toRanked,
    cardinality,
    unrank,
    generatedTerm,
    support,
    fromFTA,
    fromFTAUpToSize,
    fromFTAUpToDepth,
    fromDatatypeUpToDepth,
    fromDatatypeUpToSize,
) where

import qualified Data.Map.Lazy as Map
import Data.Maybe (mapMaybe)

import qualified Data.Tree.FTA as FTA
import qualified Data.Tree.FTA.Gen.Internal.Automaton as Automaton
import Data.Tree.FTA.Generic (Constructor, TypedFTA, datatypeDecode, datatypeFTA)
import Data.Tree.Gen (Ranked, RankedError)
import qualified Data.Tree.Gen as Ranked
import qualified Data.Tree.Gen.Internal as Internal
import Data.Tree.Term (Term (Term))
import Data.Typeable (TypeRep)

-- | A finite ranked language whose members retain their ordinary FTA terms.
newtype FTAGen symbol a = FTAGen (Ranked (Generated symbol a))

-- | One generated value paired with its ordinary tree witness.
data Generated symbol a = Generated
    { generatedValue :: a
    , generatedWitness :: !(Term symbol)
    }

-- | Applicatively assembled child positions awaiting one constructor label.
newtype Children symbol a = Children (Ranked (Forest symbol a))

-- | An applicative result and its direct constructor-child witnesses.
data Forest symbol a = Forest
    { forestValue :: a
    , forestWitnesses :: ![Term symbol]
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
        FTAGen $ mapGenerated transform <$> ranked
      where
        mapGenerated function generated =
            generated{generatedValue = function $ generatedValue generated}

instance Functor (Children symbol) where
    fmap transform (Children ranked) =
        Children $ mapForest transform <$> ranked
      where
        mapForest function forest =
            forest{forestValue = function $ forestValue forest}

instance Applicative (Children symbol) where
    pure value = Children $ pure $ Forest value []

    Children functions <*> Children arguments =
        Children $ applyForest <$> functions <*> arguments
      where
        applyForest function argument =
            Forest
                (forestValue function $ forestValue argument)
                (forestWitnesses function <> forestWitnesses argument)

-- | Build one nullary constructor.
leaf :: symbol -> a -> FTAGen symbol a
leaf symbol value =
    FTAGen $ pure $ Generated value (Term symbol [])

{- | Close an applicative child forest with one constructor label.

With @QualifiedDo@ and @ApplicativeDo@:

@node "pair" $ FTA.do ...@
-}
node :: (NodeLayer layer) => symbol -> layer symbol a -> FTAGen symbol a
node symbol layer =
    FTAGen $ close <$> ranked
  where
    Children ranked = asChildren layer

    close forest =
        Generated
            (forestValue forest)
            (Term symbol $ forestWitnesses forest)

-- | Choose among non-empty FTA languages with positive relative weights.
frequency :: [(Integer, FTAGen symbol a)] -> Either RankedError (FTAGen symbol a)
frequency alternatives =
    FTAGen <$> Ranked.frequency [(weight, ranked) | (weight, FTAGen ranked) <- alternatives]

-- | Choose equally among non-empty FTA languages.
oneof :: [FTAGen symbol a] -> Either RankedError (FTAGen symbol a)
oneof alternatives =
    FTAGen <$> Ranked.oneof [ranked | FTAGen ranked <- alternatives]

-- | Treat one FTA language as one child position.
children :: FTAGen symbol a -> Children symbol a
children (FTAGen ranked) =
    Children $ toForest <$> ranked
  where
    toForest generated =
        Forest (generatedValue generated) [generatedWitness generated]

-- | Apply one child-forest function to another child forest.
applyChildren :: Children symbol (a -> b) -> Children symbol a -> Children symbol b
applyChildren = (<*>)

-- | Forget retained witness terms and expose the ranked value language.
toRanked :: FTAGen symbol a -> Ranked a
toRanked (FTAGen ranked) = generatedValue <$> ranked

-- | Number of stable ranks in a finite FTA generator.
cardinality :: FTAGen symbol a -> Integer
cardinality = Ranked.cardinality . toRanked

-- | Replay one generated value by rank.
unrank :: FTAGen symbol a -> Integer -> Either RankedError a
unrank generator = Ranked.unrank (toRanked generator)

-- | Inspect the concrete FTA witness retained at one rank.
generatedTerm :: FTAGen symbol a -> Integer -> Either RankedError (Term symbol)
generatedTerm (FTAGen ranked) rank =
    generatedWitness <$> Ranked.unrank ranked rank

{- | Build the exact ordinary FTA support of a finite generator.

States are concrete subterms. The distinguished @Nothing@ state contains all
complete generated terms; sharing equal subterms keeps the support compact.
This decodes every rank, so use it on small languages only.
-}
support ::
    (Ord symbol) =>
    FTAGen symbol a ->
    Either (FTA.FTAError (Maybe (Term symbol)) symbol) (FTA.PlainFTA (Maybe (Term symbol)) symbol)
support generator =
    FTA.fromTerms
        [ term
        | rank <- [0 .. cardinality generator - 1]
        , Right term <- [generatedTerm generator rank]
        ]

-- | Failure while compiling an FTA into a finite ranked language.
data CompileError state
    = -- | A cyclic FTA needs an explicit size bound before it is finite.
      RecursiveFTA !state
    | -- | The initial state accepts no terms.
      EmptyFTALanguage
    deriving (Eq, Show)

{- | Compile an acyclic ordinary FTA into its finite accepting derivations.

Each state shares its compiled decoder across all incoming transitions.
Ranks and structural shrinking retain the transition and child order.
-}
fromFTA ::
    (Ord state) =>
    FTA.PlainFTA state symbol ->
    Either (CompileError state) (Ranked (Term symbol))
fromFTA automaton = case FTA.cycleState automaton of
    Just state -> Left (RecursiveFTA state)
    Nothing -> maybe (Left EmptyFTALanguage) Right (compileState $ FTA.initialState automaton)
  where
    -- The lazy table permits references to states compiled from the same table.
    compiled = Map.map compileTransitions $ FTA.transitionTable automaton

    compileState state = Map.findWithDefault Nothing state compiled

    compileTransitions = fmap Internal.share . combine . mapMaybe compileTransition

    compileTransition transition = do
        childLanguages <- traverse compileState (FTA.transitionChildren transition)
        pure $ buildTerm (FTA.transitionSymbol transition) childLanguages

    combine [] = Nothing
    combine alternatives =
        case Ranked.oneof alternatives of
            Left _ -> Nothing
            Right ranked -> Just ranked

{- | Compile all accepting runs with at most the given number of tree nodes.

Cycles are valid. Ranks use size-major order, including for acyclic automata.
Ambiguous terms retain one rank per accepting run. A non-positive bound or an
empty bounded language gives 'EmptyFTALanguage'.
-}
fromFTAUpToSize ::
    (Ord state) => Int -> FTA.PlainFTA state symbol -> Either (CompileError state) (Ranked (Term symbol))
fromFTAUpToSize bound automaton =
    case Internal.fromSizeIndex bound $ Automaton.automatonIndex automaton of
        Left _ -> Left EmptyFTALanguage
        Right ranked -> Right ranked

{- | Compile every accepting run up to the given constructor depth.

A leaf has depth zero. Ranks retain transition and child order in the bounded
graph. This is a depth bound, whereas 'fromFTAUpToSize' bounds all tree nodes.
The only possible failure is 'EmptyFTALanguage'.
-}
fromFTAUpToDepth ::
    (Ord state) => Int -> FTA.PlainFTA state symbol -> Either (CompileError state) (Ranked (Term symbol))
fromFTAUpToDepth bound automaton =
    case fromFTA $ FTA.boundDepth bound automaton of
        Right ranked -> Right ranked
        Left EmptyFTALanguage -> Left EmptyFTALanguage
        Left (RecursiveFTA _) ->
            error
                "microfta-generator bug in Data.Tree.FTA.Gen.fromFTAUpToDepth: \
                \a depth-bounded automaton is cyclic"

{- | Generate datatype values from the derived grammar up to constructor depth.

The value and its original constructor term share one rank. Codecs are applied
only when a selected value is demanded. A leaf has depth zero.
-}
fromDatatypeUpToDepth :: Int -> TypedFTA () a -> Either (CompileError TypeRep) (FTAGen Constructor a)
fromDatatypeUpToDepth bound datatype =
    fromDatatypeTerms datatype <$> fromFTAUpToDepth bound (datatypeFTA datatype)

-- | Generate datatype values in size-major order with uniform rank sampling.
fromDatatypeUpToSize :: Int -> TypedFTA () a -> Either (CompileError TypeRep) (FTAGen Constructor a)
fromDatatypeUpToSize bound datatype =
    fromDatatypeTerms datatype <$> fromFTAUpToSize bound (datatypeFTA datatype)

-- | Retain the witness while decoding a term from its own datatype grammar.
fromDatatypeTerms :: TypedFTA () a -> Ranked (Term Constructor) -> FTAGen Constructor a
fromDatatypeTerms datatype ranked = FTAGen $ generated <$> ranked
  where
    generated term = Generated (decode term) term
    decode term = case datatypeDecode datatype term of
        Just value -> value
        Nothing ->
            error
                "microfta-generator bug in Data.Tree.FTA.Gen.fromDatatypeTerms: \
                \the derived codec rejected a term of its own grammar"

-- | Apply a constructor to its independently ranked children.
buildTerm :: symbol -> [Ranked (Term symbol)] -> Ranked (Term symbol)
buildTerm symbol childLanguages =
    ($ [])
        <$> foldl'
            applyChild
            (pure $ Term symbol)
            childLanguages
  where
    applyChild partial child =
        (\finish value rest -> finish (value : rest)) <$> partial <*> child
