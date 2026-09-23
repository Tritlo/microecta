{-# LANGUAGE TupleSections #-}

{- | The paper's similarity inference and M-Trans minimization.

'similarity' asks a 'Subtyping' oracle to order transitions. 'minimize' then
applies one deterministic schedule of M-Trans on the explicit view of the
graph, keeps the original automaton whenever a step would lose a finite
derivation, and interns the result again.
-}
module Data.CFTA.Refinement.Minimize (
    TransitionId (..),
    Subtyping (..),
    refinementSubtypingBy,
    Similarity,
    SimilarityError (..),
    similarity,
    similarityPairs,
    MinimizeError (..),
    minimize,
) where

import Data.Bifunctor (first)
import Data.List (elemIndex, nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Data.CFTA as FTA
import Data.CFTA.Interned (InternedState (..), fromFTA, nodeIdentity)

import Data.CFTA.Refinement.Automaton (
    Automaton,
    AutomatonError (CyclicGuardReference),
    Transition,
    explicitView,
    fromViewError,
    located,
    transitionRefinement,
    validate,
 )
import Data.CFTA.Refinement.Constraint (LiquidConstraint)
import Data.CFTA.Refinement.Types (LiquidSymbol)
import Data.CFTA.Refinement.Verdict (Entailment, Verdict (..), entails)

{- | The address of a transition in one automaton snapshot.

The target is the node whose alternatives include the transition. The paper
writes the same target on the right of a bottom-up transition arrow.
-}
data TransitionId = TransitionId
    { transitionTarget :: !Automaton
    , transitionValue :: !Transition
    }
    deriving (Eq, Ord, Show)

{- | Source-language subtyping used by the paper's @Similarity@ procedure.

The callback receives the current automaton and compares the type sub-automata
associated with two program transitions. 'refinementSubtypingBy' is a compact
adapter for encodings that store the complete type refinement on the program
transition itself.
-}
newtype Subtyping = Subtyping
    { isTransitionSubtypeOf :: Automaton -> Transition -> Transition -> IO Verdict
    }

{- | Compare transition refinements after a structural type classification.

The projection supplies the non-liquid part of the type shape. Two transitions
are comparable only when both project to the same class; 'Nothing' excludes a
transition from similarity inference. This corresponds to the syntactic part
of the paper's @SubType@ relation, while implication checks its refinement.
-}
refinementSubtypingBy ::
    (Eq key) =>
    Entailment ->
    (Transition -> Maybe key) ->
    Subtyping
refinementSubtypingBy entailment classify =
    Subtyping $ \_ subtype supertype ->
        case (classify subtype, classify supertype) of
            (Just subtypeClass, Just supertypeClass)
                | subtypeClass == supertypeClass ->
                    entails
                        entailment
                        (transitionRefinement subtype)
                        (transitionRefinement supertype)
            _ -> pure No

-- | Directed transition pairs and the automaton for which they were inferred.
data Similarity = Similarity !Automaton ![(TransitionId, TransitionId)]
    deriving (Eq, Show)

-- | A similarity query that could not be answered.
data SimilarityError
    = -- | A source-language subtyping query could not be decided.
      SimilarityUnknown !TransitionId !TransitionId
    | -- | The automaton is not a valid LTA.
      InvalidSimilarityAutomaton !AutomatonError
    deriving (Eq, Show)

{- | Infer directed @(subtype, supertype)@ transition pairs.

Every unordered transition pair is considered once. If both directions hold,
the earlier transition is the representative, making equivalence deterministic
without introducing a cycle into the similarity set. A known direction is
usable even if its converse is unknown; an unresolved possible direction is
reported rather than treated as false.
-}
similarity :: Subtyping -> Automaton -> IO (Either SimilarityError Similarity)
similarity subtyping automaton = case validate automaton of
    Left err -> pure $ Left $ InvalidSimilarityAutomaton err
    Right () -> go [] $ unorderedPairs $ locatedTransitions automaton
  where
    go related [] = pure $ Right $ Similarity automaton $ reverse related
    go related (((leftId, left), (rightId, right)) : rest) = do
        leftToRight <- isTransitionSubtypeOf subtyping automaton left right
        case leftToRight of
            Yes -> go ((leftId, rightId) : related) rest
            No -> do
                rightToLeft <- isTransitionSubtypeOf subtyping automaton right left
                case rightToLeft of
                    Yes -> go ((rightId, leftId) : related) rest
                    No -> go related rest
                    Unknown -> pure $ Left $ SimilarityUnknown rightId leftId
            Unknown -> do
                rightToLeft <- isTransitionSubtypeOf subtyping automaton right left
                case rightToLeft of
                    Yes -> go ((rightId, leftId) : related) rest
                    No -> pure $ Left $ SimilarityUnknown leftId rightId
                    Unknown -> pure $ Left $ SimilarityUnknown leftId rightId

-- | Inspect the inferred @(subtype, supertype)@ transition pairs.
similarityPairs :: Similarity -> [(TransitionId, TransitionId)]
similarityPairs (Similarity _ related) = related

-- | Every transition paired with its address, in node identity order.
locatedTransitions :: Automaton -> [(TransitionId, Transition)]
locatedTransitions automaton =
    [(TransitionId node edge, edge) | (node, edges) <- located automaton, edge <- edges]

-- | Structural failure while applying the paper's @Minimize@ procedure.
data MinimizeError
    = -- | The similarity set was inferred for a different automaton snapshot.
      StaleSimilarity
    | -- | The inferred relation contains a directed cycle, which a non-transitive 'Subtyping' can produce.
      CyclicSimilarity ![TransitionId]
    | -- | Minimization exposed an invalid automaton structure.
      InvalidMinimizedAutomaton !AutomatonError
    deriving (Eq, Show)

-- | A transition of the explicit view, and its address as a state and ordinal.
type ViewTransition = FTA.Transition InternedState LiquidSymbol LiquidConstraint

type Address = (InternedState, Int)

{- | Apply a finite deterministic schedule of the paper's M-Trans rule.

Each selected supertype transition is considered once. A step keeps existing
incoming alternatives, adds copies with all occurrences of the removed target
replaced together, then removes only the selected original transition. Later
steps can copy alternatives added by earlier steps. Equal transitions are
deduplicated. The root stays the root.

The first inferred dominator selects the representative when several subtypes
are incomparable. Transitive representatives are resolved before the schedule.
This does not promise a globally minimal automaton or an equal term language.

The original automaton is retained if dependencies become unsafe, a
representative loses its finite structural derivations, the last finite root
derivation is lost, or a guard would inspect a recursive node. Unproductive
transitions are removed after a successful schedule.
-}
minimize :: Automaton -> Similarity -> Either MinimizeError Automaton
minimize automaton (Similarity original related) = do
    if automaton == original then Right () else Left StaleSimilarity
    view <- first InvalidMinimizedAutomaton $ explicitView automaton
    addressed <- traverse (\(subtype, supertype) -> (,) <$> address subtype <*> address supertype) related
    let table = FTA.transitionTable view
        initial = FTA.initialState view
        current :: Map.Map Address ViewTransition
        current =
            Map.fromList
                [ ((state, ordinal), transition)
                | (state, transitions) <- Map.toAscList table
                , (ordinal, transition) <- zip [0 ..] transitions
                ]
        names = Map.fromList $ zip (concatMap both addressed) (concatMap both related)
        dominators = foldl' rememberDominator Map.empty addressed
        rememberDominator known (subtype, supertype) = Map.insertWith keepEarlier supertype subtype known
        keepEarlier _ earlier = earlier
        resolve visited identifier
            | Set.member identifier visited =
                Left $ CyclicSimilarity $ map (names Map.!) $ Set.toAscList $ Set.insert identifier visited
            | otherwise = case Map.lookup identifier dominators of
                Nothing -> Right identifier
                Just representative -> resolve (Set.insert identifier visited) representative
    resolved <- traverse (\supertype -> (supertype,) <$> resolve Set.empty supertype) (Map.keys dominators)
    let redirectFor (supertype, representative) = (fst supertype, fst representative)
        redirects = Map.fromListWith (<>) [(source, [destination]) | pair <- resolved, let (source, destination) = redirectFor pair]
        applyStep (table', steps) pair@(supertype, representative)
            | source == destination && removed == retained = (Map.adjust nub source table', steps)
            | removed `notElem` Map.findWithDefault [] source table' = (table', steps)
            | retained `notElem` Map.findWithDefault [] destination table' = (table', steps)
            | otherwise =
                ( Map.adjust (filter (/= removed)) source $ fmap (copyAlternatives redirect) table'
                , redirect : steps
                )
          where
            redirect@(source, destination) = redirectFor pair
            removed = current Map.! supertype
            retained = current Map.! representative
        copyAlternatives (source, destination) transitions =
            nub $ transitions <> map (redirectTransition $ Map.singleton source destination) transitions
        (rewritten, applied) = foldl' applyStep (table, []) resolved
        productive = productiveStates rewritten
        finiteTransition = all (`Set.member` productive) . FTA.transitionChildren
        hasFiniteDerivation representative =
            any
                ( \transition ->
                    transition `elem` Map.findWithDefault [] (fst representative) rewritten && finiteTransition transition
                )
                (foldl' (flip copyAlternatives) [current Map.! representative] $ reverse applied)
        representatives = Set.toAscList $ Set.fromList $ map snd resolved
        losesFinal = Set.member initial (productiveStates table) && Set.notMember initial productive
        dependsOnRemovedTarget (supertype, representative) =
            reaches Set.empty $ FTA.transitionChildren $ current Map.! representative
          where
            target = fst supertype
            reaches _ [] = False
            reaches visited (state : rest)
                | state == target = True
                | Set.member state visited = reaches visited rest
                | otherwise =
                    reaches
                        (Set.insert state visited)
                        ( Map.findWithDefault [] state redirects
                            <> concatMap FTA.transitionChildren (Map.findWithDefault [] state table)
                            <> rest
                        )
    if any dependsOnRemovedTarget resolved || not (all hasFiniteDerivation representatives) || losesFinal
        then Right automaton
        else case FTA.mkFTA initial (Map.toList $ fmap (filter finiteTransition) rewritten) of
            Left err -> Left $ InvalidMinimizedAutomaton $ fromViewError err
            Right minimizedView ->
                let minimized = fromFTA minimizedView
                 in case validate minimized of
                        Left (CyclicGuardReference _ _) -> Right automaton
                        Left err -> Left $ InvalidMinimizedAutomaton err
                        Right () -> Right minimized
  where
    alternativesOf = located automaton

    address (TransitionId node edge) = case lookup node alternativesOf >>= elemIndex edge of
        Just ordinal -> Right (InternedState (nodeIdentity node), ordinal)
        Nothing -> Left StaleSimilarity

    both (left, right) = [left, right]

-- | States that derive at least one finite term.
productiveStates :: Map.Map InternedState [ViewTransition] -> Set.Set InternedState
productiveStates rows = grow Set.empty
  where
    grow known =
        let next = Map.keysSet $ Map.filter (any $ all (`Set.member` known) . FTA.transitionChildren) rows
         in if next == known then known else grow next

-- | Rewrite every child that targeted a removed supertype state.
redirectTransition :: Map.Map InternedState InternedState -> ViewTransition -> ViewTransition
redirectTransition redirects transition =
    transition{FTA.transitionChildren = map redirect $ FTA.transitionChildren transition}
  where
    redirect state = Map.findWithDefault state state redirects

-- | Every unordered pair of distinct list elements, preserving first-seen order.
unorderedPairs :: [a] -> [(a, a)]
unorderedPairs [] = []
unorderedPairs (value : rest) = [(value, other) | other <- rest] <> unorderedPairs rest
