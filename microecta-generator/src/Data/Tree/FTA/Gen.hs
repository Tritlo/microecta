{-# LANGUAGE BangPatterns #-}

{- | Compile ordinary finite-language FTAs into ranked generators.

The FTA remains the inspectable support. This module adds exact cardinality,
stable replay ranks, backend-independent sampling, and structural shrinking.
Ranks identify accepting derivations; an ambiguous FTA may therefore produce
the same concrete term at more than one rank.
-}
module Data.Tree.FTA.Gen (
    FTAGen,
    Children,
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
) where

import Data.Maybe (mapMaybe)
import qualified Data.Set as Set

import qualified Data.Tree.FTA as FTA
import Data.Tree.Gen (Ranked, RankedError)
import qualified Data.Tree.Gen as Ranked
import Data.Tree.Term (Term (Term))

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
node :: symbol -> Children symbol a -> FTAGen symbol a
node symbol (Children ranked) =
    FTAGen $ close <$> ranked
  where
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
-}
support ::
    (Ord symbol) =>
    FTAGen symbol a ->
    Either (FTA.FTAError (Maybe (Term symbol)) symbol) (FTA.PlainFTA (Maybe (Term symbol)) symbol)
support generator =
    FTA.mkFTA Nothing $
        (Nothing, map transition terms)
            : [ (Just term, [transition term])
              | term <- Set.toList $ Set.fromList $ concatMap subterms terms
              ]
  where
    terms = Set.toList $ Set.fromList generatedTerms

    generatedTerms =
        [ term
        | rank <- [0 .. cardinality generator - 1]
        , Right term <- [generatedTerm generator rank]
        ]

    transition (Term symbol children_) =
        FTA.Transition symbol (map Just children_) ()

    subterms term@(Term _ children_) =
        term : concatMap subterms children_

-- | Failure while compiling an FTA into a finite ranked language.
data CompileError state
    = -- | A cyclic FTA needs an explicit size bound before it is finite.
      RecursiveFTA !state
    | -- | The initial state accepts no terms.
      EmptyFTALanguage
    deriving (Eq, Show)

-- | Compile an acyclic ordinary FTA into its finite accepting derivations.
fromFTA ::
    (Ord state) =>
    FTA.PlainFTA state symbol ->
    Either (CompileError state) (Ranked (Term symbol))
fromFTA automaton = case FTA.cycleState automaton of
    Just state -> Left (RecursiveFTA state)
    Nothing -> maybe (Left EmptyFTALanguage) Right (compileState $ FTA.initialState automaton)
  where
    compileState state =
        combine $ mapMaybe compileTransition $ FTA.transitionsFrom automaton state

    compileTransition transition = do
        childLanguages <- traverse compileState (FTA.transitionChildren transition)
        pure $ buildTerm (FTA.transitionSymbol transition) childLanguages

    combine [] = Nothing
    combine alternatives =
        case Ranked.oneof alternatives of
            Left _ -> Nothing
            Right ranked -> Just ranked

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
