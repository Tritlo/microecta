{- | The paper's similarity inference and M-Trans minimization.

'similarity' asks a 'Subtyping' oracle to order transitions. 'minimize' then
applies one deterministic schedule of M-Trans, keeping the original automaton
whenever a step would lose a finite derivation.
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

import Data.List (nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.CFTA.Refinement.Automaton (
    Automaton,
    AutomatonError (CyclicGuardReference),
    Transition,
    automatonInitial,
    automatonTransitions,
    mkAutomaton,
    replaceTransitionChildren,
    transitionChildren,
    transitionRefinement,
 )
import Data.CFTA.Refinement.Types (State)
import Data.CFTA.Refinement.Verdict (Entailment, Verdict (..), entails)

{- | Stable address of a transition in one automaton snapshot.

The state is the transition's target state; the ordinal is its zero-based
position in that state's transition row. The paper writes the same target on
the right of a bottom-up transition arrow.
-}
data TransitionId = TransitionId
    { transitionTargetState :: !State
    , transitionOrdinal :: !Int
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

-- | A source-language subtyping query that could not be decided.
data SimilarityError
    = SimilarityUnknown !TransitionId !TransitionId
    deriving (Eq, Show)

{- | Infer directed @(subtype, supertype)@ transition pairs.

Every unordered transition pair is considered once. If both directions hold,
the earlier transition is the representative, making equivalence deterministic
without introducing a cycle into the similarity set. A known direction is
usable even if its converse is unknown; an unresolved possible direction is
reported rather than treated as false.
-}
similarity :: Subtyping -> Automaton -> IO (Either SimilarityError Similarity)
similarity subtyping automaton = go [] $ unorderedPairs $ locatedTransitions automaton
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

-- | Structural failure while applying the paper's @Minimize@ procedure.
data MinimizeError
    = -- | The similarity set was inferred for a different automaton snapshot.
      StaleSimilarity
    | -- | The inferred relation contains a directed cycle, which a non-transitive 'Subtyping' can produce.
      CyclicSimilarity ![TransitionId]
    | -- | Minimization exposed an invalid automaton structure.
      InvalidMinimizedAutomaton !AutomatonError
    deriving (Eq, Show)

{- | Apply a finite deterministic schedule of the paper's M-Trans rule.

Each selected supertype transition is considered once. A step keeps existing
incoming alternatives, adds copies with all occurrences of the removed target
replaced together, then removes only the selected original transition. Later
steps can copy alternatives added by earlier steps. Equal transitions are
deduplicated. The state set and normalized final state remain unchanged.

The first inferred dominator selects the representative when several subtypes
are incomparable. Transitive representatives are resolved before the schedule.
This does not promise a globally minimal automaton or an equal term language.

The original batch is retained if dependencies become unsafe, a representative
loses its finite structural derivations, the last finite final derivation is
lost, or a guard would inspect a cyclic state. Unproductive transitions are
removed after a successful schedule.
-}
minimize :: Automaton -> Similarity -> Either MinimizeError Automaton
minimize automaton (Similarity original related) = do
    if automaton == original then Right () else Left StaleSimilarity
    resolved <- traverse resolveSupertype $ Map.keys dominators
    let redirects = Map.fromListWith (<>) [(source, [destination]) | pair <- resolved, let (source, destination) = redirectFor pair]
        (rewritten, applied) = foldl' applyStep (table, []) resolved
        productive = productiveStates rewritten
        finiteTransition = all (`Set.member` productive) . transitionChildren
        hasFiniteDerivation representative =
            any
                ( \transition ->
                    transition `elem` Map.findWithDefault [] (transitionTargetState representative) rewritten && finiteTransition transition
                )
                (foldl' (flip copyAlternatives) [current Map.! representative] $ reverse applied)
        representatives = Set.toAscList $ Set.fromList $ map snd resolved
        initial = automatonInitial automaton
        losesFinal = Set.member initial (productiveStates table) && Set.notMember initial productive
    if any (dependsOnRemovedTarget redirects) resolved || not (all hasFiniteDerivation representatives) || losesFinal
        then Right automaton
        else case mkAutomaton initial (Map.toList $ fmap (filter finiteTransition) rewritten) of
            Left (CyclicGuardReference _ _) -> Right automaton
            Left err -> Left $ InvalidMinimizedAutomaton err
            Right minimized -> Right minimized
  where
    table = automatonTransitions automaton
    current = Map.fromList $ locatedTransitions automaton
    dominators = foldl' rememberDominator Map.empty related

    rememberDominator known (subtype, supertype) =
        Map.insertWith keepEarlier supertype subtype known

    keepEarlier _ earlier = earlier

    resolveSupertype supertype = do
        representative <- resolve Set.empty supertype
        pure (supertype, representative)

    resolve visited identifier
        | Set.member identifier visited =
            Left $ CyclicSimilarity $ Set.toAscList $ Set.insert identifier visited
        | otherwise =
            case Map.lookup identifier dominators of
                Nothing -> Right identifier
                Just representative ->
                    resolve (Set.insert identifier visited) representative

    redirectFor (supertype, representative) =
        (transitionTargetState supertype, transitionTargetState representative)

    applyStep (rows, applied) pair@(supertype, representative)
        | source == destination && removed == retained = (Map.adjust nub source rows, applied)
        | removed `notElem` Map.findWithDefault [] source rows = (rows, applied)
        | retained `notElem` Map.findWithDefault [] destination rows = (rows, applied)
        | otherwise =
            ( Map.adjust (filter (/= removed)) source $ fmap (copyAlternatives redirect) rows
            , redirect : applied
            )
      where
        redirect@(source, destination) = redirectFor pair
        removed = current Map.! supertype
        retained = current Map.! representative

    copyAlternatives (source, destination) transitions =
        nub $ transitions <> map (redirectTransition $ Map.singleton source destination) transitions

    dependsOnRemovedTarget redirects (supertype, representative) =
        reaches Set.empty $ transitionChildren $ current Map.! representative
      where
        target = transitionTargetState supertype

        reaches _ [] = False
        reaches visited (state : rest)
            | state == target = True
            | Set.member state visited = reaches visited rest
            | otherwise =
                reaches
                    (Set.insert state visited)
                    ( Map.findWithDefault [] state redirects
                        <> concatMap transitionChildren (Map.findWithDefault [] state table)
                        <> rest
                    )

    productiveStates rewritten = grow Set.empty
      where
        grow known =
            let next =
                    Map.keysSet $
                        Map.filter
                            (any $ all (`Set.member` known) . transitionChildren)
                            rewritten
             in if next == known then known else grow next

-- | Rewrite every incoming edge that targeted a removed supertype state.
redirectTransition :: Map.Map State State -> Transition -> Transition
redirectTransition redirects transition =
    replaceTransitionChildren
        (map redirect $ transitionChildren transition)
        transition
  where
    redirect state = Map.findWithDefault state state redirects

-- | Every transition paired with its stable address, in table order.
locatedTransitions :: Automaton -> [(TransitionId, Transition)]
locatedTransitions automaton =
    [ (TransitionId state ordinal, transition)
    | (state, transitions) <- Map.toAscList $ automatonTransitions automaton
    , (ordinal, transition) <- zip [0 ..] transitions
    ]

-- | Every unordered pair of distinct list elements, preserving first-seen order.
unorderedPairs :: [a] -> [(a, a)]
unorderedPairs [] = []
unorderedPairs (value : rest) = [(value, other) | other <- rest] <> unorderedPairs rest
