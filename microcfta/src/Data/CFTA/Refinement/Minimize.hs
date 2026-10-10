{- | The paper's similarity inference and M-Trans minimization.

'similarity' asks a 'Subtyping' oracle to order transitions. 'minimize' then
applies one deterministic schedule of M-Trans on the explicit view of the
graph, skips a step that could change the answer of a guard, keeps the
original automaton whenever a step would lose a finite derivation, and interns
the result again.
-}
module Data.CFTA.Refinement.Minimize (
    TransitionId (..),
    Subtyping (..),
    refinementSubtypingOn,
    Similarity,
    SimilarityPair (..),
    SimilarityError (..),
    similarity,
    similarityPairs,
    MinimizeError (..),
    minimize,
) where

import Data.Bifunctor (first)
import Data.Foldable (toList)
import qualified Data.Graph as Graph
import qualified Data.IntMap.Strict as IntMap
import Data.List (elemIndex, nub, sortOn, (!?))
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq (..))
import qualified Data.Set as Set

import qualified Data.CFTA as FTA
import Data.CFTA.Index (ChildIndex (..), TransitionIndex (..))
import Data.CFTA.Interned (InternedState (..), NodeId (..), fromFTA, nodeIdentity)
import Data.CFTA.Path (Path, unPath)

import Data.CFTA.Constraint (Constraint (..), Guard (..), constraintPaths, guardPaths, noConstraint)
import Data.CFTA.Refinement.Automaton (
    Automaton,
    AutomatonError (CyclicGuardReference),
    Transition,
    explicitView,
    fromViewError,
    located,
    transitionRefinement,
    transitionSymbol,
    validate,
 )
import Data.CFTA.Refinement.Verdict (Entailment, Verdict (..), entails)
import Data.CFTA.Symbol (Symbol)

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
associated with two program transitions. 'refinementSubtypingOn' is a compact
adapter for encodings that store the complete type refinement on the program
transition itself.
-}
newtype Subtyping = Subtyping
    { isTransitionSubtypeOf :: Automaton -> Transition -> Transition -> IO Verdict
    }

{- | Compare transition refinements after a structural type classification.

The projection supplies the non-liquid part of the type shape. Two transitions
are comparable only when both project to the same class. 'Nothing' excludes a
transition from similarity inference. This corresponds to the syntactic part
of the paper's @SubType@ relation, while implication checks its refinement.
-}
refinementSubtypingOn ::
    (Eq key) =>
    Entailment ->
    (Transition -> Maybe key) ->
    Subtyping
refinementSubtypingOn entailment classify =
    Subtyping $ \_ low high ->
        case (classify low, classify high) of
            (Just lowClass, Just highClass)
                | lowClass == highClass ->
                    entails
                        entailment
                        (transitionRefinement low)
                        (transitionRefinement high)
            _ -> pure No

{- | A directed similarity pair @subtype ≲ supertype@ of the LTA paper. The
type parameter is the kind of name that identifies a transition.
-}
data SimilarityPair a = SimilarityPair
    { subtype :: !a
    , supertype :: !a
    }
    deriving (Eq, Ord, Show)

-- | Directed transition pairs and the automaton for which they were inferred.
data Similarity = Similarity !Automaton ![SimilarityPair TransitionId]
    deriving (Eq, Show)

-- | A similarity query that could not be answered.
data SimilarityError
    = -- | A source-language subtyping query could not be decided.
      SimilarityUnknown !TransitionId !TransitionId
    | -- | The automaton is not a valid LTA.
      InvalidSimilarityAutomaton !AutomatonError
    deriving (Eq, Show)

{- | Infer directed 'SimilarityPair' values over transitions.

Every unordered transition pair is considered once. If the first direction
holds, the second is not queried, so only one direction of a pair is recorded.
This removes two-cycles, and equivalence is deterministic. A non-transitive
'Subtyping' can still give a longer directed cycle. A known direction is
usable even if its converse is unknown. The result reports an unresolved
possible direction and does not treat it as false.
-}
similarity :: Subtyping -> Automaton -> IO (Either SimilarityError Similarity)
similarity subtyping automaton = case validate automaton of
    Left err -> pure $ Left $ InvalidSimilarityAutomaton err
    Right () -> go Empty $ unorderedPairs $ locatedTransitions automaton
  where
    go related [] = pure $ Right $ Similarity automaton $ toList related
    go related (((leftId, left), (rightId, right)) : rest) = do
        leftToRight <- isTransitionSubtypeOf subtyping automaton left right
        case leftToRight of
            Yes -> go (related :|> SimilarityPair leftId rightId) rest
            No -> do
                rightToLeft <- isTransitionSubtypeOf subtyping automaton right left
                case rightToLeft of
                    Yes -> go (related :|> SimilarityPair rightId leftId) rest
                    No -> go related rest
                    Unknown -> pure $ Left $ SimilarityUnknown rightId leftId
            Unknown -> do
                rightToLeft <- isTransitionSubtypeOf subtyping automaton right left
                case rightToLeft of
                    Yes -> go (related :|> SimilarityPair rightId leftId) rest
                    No -> pure $ Left $ SimilarityUnknown leftId rightId
                    Unknown -> pure $ Left $ SimilarityUnknown leftId rightId

-- | Inspect the inferred 'SimilarityPair' values.
similarityPairs :: Similarity -> [SimilarityPair TransitionId]
similarityPairs (Similarity _ related) = related

{- | Every transition paired with its address, in node identity order. Within
a node, the transitions are in symbol and refinement order, which does not
depend on the order in which the process interned them.
-}
locatedTransitions :: Automaton -> [(TransitionId, Transition)]
locatedTransitions automaton =
    [(TransitionId node edge, edge) | (node, edges) <- located automaton, edge <- sortOn label edges]
  where
    label edge = (transitionSymbol edge, transitionRefinement edge)

-- | Structural failure while applying the paper's @Minimize@ procedure.
data MinimizeError
    = -- | The similarity set was inferred for a different automaton snapshot.
      StaleSimilarity
    | -- | The inferred relation contains a directed cycle, which a non-transitive 'Subtyping' can produce.
      CyclicSimilarity ![TransitionId]
    | -- | Minimization exposed an invalid automaton structure.
      InvalidMinimizedAutomaton !AutomatonError
    deriving (Eq, Show)

-- | A transition of the explicit view, and its address as a state and transition index.
type ViewTransition = FTA.Transition InternedState Symbol Constraint

-- | A supertype transition and the representative that replaces it in the schedule. This is not a similarity pair.
data Replacement = Replacement
    { replacedSupertype :: !Address
    , chosenRepresentative :: !Address
    }

-- | The state of a transition in the explicit view, and the index of the transition in that state.
data Address = Address
    { addressNode :: !InternedState
    , addressIndex :: !TransitionIndex
    }
    deriving (Eq, Ord)

{- | Apply a finite deterministic schedule of the paper's M-Trans rule.

Each selected supertype transition is considered once. A step keeps existing
incoming alternatives, adds copies with all occurrences of the removed target
replaced together, then removes only the selected original transition. Later
steps can copy alternatives added by earlier steps. Equal transitions are
deduplicated. The root stays the root.

A copy replaces the node of the supertype by the node of the representative,
so it reaches every alternative of that node. The similarity pair relates
only the representative. Thus a step between two nodes applies only when the
representative is the only alternative of its node in the input. The schedule
skips the other steps between two nodes. A step within one node only removes
the supertype. If the similarity relates only equal transitions, each term of
the result is a term of the input.

The first inferred dominator selects the representative when several subtypes
are incomparable. Transitive representatives are resolved before the schedule.
This does not promise a globally minimal automaton or an equal term language.
The term language can change by design: a step replaces a supertype
transition by the representative that the similarity set selects. So a check
that the language stays equal does not apply. A globally minimal automaton
would need the exact similarity relation, and the solver can answer
@Unknown@.

A step changes the terms of the supertype's node in every place where that
node occurs, so a guard that reads such a place must keep its answer. The
representative has the stronger refinement when the oracle orders
refinements, as 'refinementSubtypingOn' does. So the schedule skips a step
unless each guard reads the node only at the end of a path, in 'Satisfies',
'Holds', or the antecedent of an 'Entails' that is not negated. A 'Same', the
consequent of an 'Entails', a negated 'Entails', a substitution, or an
equality class that reads the node or a term that contains it would change
its answer.

A step also needs a representative with an accepted term. A structural
derivation is an accepted term only when no constraint at or below the
representative can reject it, and 'minimize' has no solver to decide a
constraint. So the schedule skips a step whose representative has a
constraint at or below it. 'Data.CFTA.Refinement.Prune.prune' removes the
semantic part of each guard that it decides, so after pruning this skips the
representatives with an undecided guard, a 'Same', or an equality class at or
below them.

The original automaton is retained if dependencies become unsafe, a
representative loses its finite structural derivations, the last finite root
derivation is lost, or a guard would inspect a recursive node. Unproductive
transitions are removed after a successful schedule.
-}
minimize :: Automaton -> Similarity -> Either MinimizeError Automaton
minimize automaton (Similarity original related) = do
    if automaton == original then Right () else Left StaleSimilarity
    view <- first InvalidMinimizedAutomaton $ explicitView automaton
    addressed <- traverse (\(SimilarityPair low high) -> SimilarityPair <$> address low <*> address high) related
    let table = FTA.transitionTable view
        initial = FTA.initialState view
        current :: Map.Map Address ViewTransition
        current =
            Map.fromList
                [ (Address state ordinal, transition)
                | (state, transitions) <- Map.toAscList table
                , (ordinal, transition) <- zip [0 ..] transitions
                ]
        names = Map.fromList $ zip (concatMap both addressed) (concatMap both related)
        dominators = foldl' rememberDominator Map.empty addressed
        rememberDominator known (SimilarityPair low high) = Map.insertWith keepEarlier high low known
        keepEarlier _ earlier = earlier
        resolve visited identifier
            | Set.member identifier visited =
                Left $ CyclicSimilarity $ map (names Map.!) $ Set.toAscList $ Set.insert identifier visited
            | otherwise = case Map.lookup identifier dominators of
                Nothing -> Right identifier
                Just representative -> resolve (Set.insert identifier visited) representative
    resolved <- traverse (\replaced -> Replacement replaced <$> resolve Set.empty replaced) (Map.keys dominators)
    let redirectFor pair = (addressNode $ replacedSupertype pair, addressNode $ chosenRepresentative pair)
        redirects = Map.fromListWith (<>) [(source, [destination]) | pair <- resolved, let (source, destination) = redirectFor pair]
        applyStep (table', steps) pair
            | source == destination && removed == retained = (Map.adjust nub source table', steps)
            -- A copy reaches every alternative of the destination, and only the
            -- representative is similar to the removed transition.
            | source /= destination && Map.findWithDefault [] destination table /= [retained] = (table', steps)
            | removed `notElem` Map.findWithDefault [] source table' = (table', steps)
            | retained `notElem` Map.findWithDefault [] destination table' = (table', steps)
            -- The step changes the terms of the source in every context, so
            -- each guard that reads the source must keep its answer.
            | not $ keepsGuards table' source = (table', steps)
            -- Without a solver, a representative has an accepted term only when
            -- no constraint at or below it can reject its structural terms.
            | not $ unconstrainedBelow table' retained = (table', steps)
            | otherwise =
                ( Map.adjust (filter (/= removed)) source $ fmap (copyAlternatives redirect) table'
                , steps :|> redirect
                )
          where
            redirect@(source, destination) = redirectFor pair
            removed = current Map.! replacedSupertype pair
            retained = current Map.! chosenRepresentative pair
        copyAlternatives (source, destination) transitions =
            nub $ transitions <> map (redirectTransition $ Map.singleton source destination) transitions
        (rewritten, applied) = foldl' applyStep (table, Empty) resolved
        productive = productiveStates rewritten
        finiteTransition = all (`Set.member` productive) . FTA.transitionChildren
        hasFiniteDerivation chosen =
            any
                ( \transition ->
                    transition `elem` Map.findWithDefault [] (addressNode chosen) rewritten && finiteTransition transition
                )
                (foldl' (flip copyAlternatives) [current Map.! chosen] applied)
        representatives = Set.toAscList $ Set.fromList $ map chosenRepresentative resolved
        losesFinal = Set.member initial (productiveStates table) && Set.notMember initial productive
        -- A state depends on the states of its redirects and of its transitions' children.
        (dependencies, _, vertexOf) =
            Graph.graphFromEdges
                [ ((), state, Map.findWithDefault [] state redirects <> concatMap FTA.transitionChildren transitions)
                | (state, transitions) <- Map.toList table
                ]
        -- TODO: Graph.dfs makes a visited array for the whole table on each call,
        -- so each pair costs time in the size of the table. The hand-written
        -- search that it replaced cost time in the states that it reached, and it
        -- stopped at the target. On the benchmark cells (2026-10-09) the two
        -- searches differ by less than 0.01% of instructions. Go back to the
        -- hand-written search if minimization of large tables gets slow.
        dependsOnRemovedTarget pair =
            case vertexOf $ addressNode $ replacedSupertype pair of
                Nothing -> False
                Just target ->
                    any (elem target) $
                        Graph.dfs
                            dependencies
                            [start | child <- FTA.transitionChildren $ current Map.! chosenRepresentative pair, Just start <- [vertexOf child]]
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
    alternativesOf = IntMap.fromList [(ident, edges) | (node, edges) <- located automaton, let NodeId ident = nodeIdentity node]

    address (TransitionId node edge) = case IntMap.lookup ident alternativesOf >>= elemIndex edge of
        Just ordinal -> Right Address{addressNode = InternedState (nodeIdentity node), addressIndex = TransitionIndex ordinal}
        Nothing -> Left StaleSimilarity
      where
        NodeId ident = nodeIdentity node

    both (SimilarityPair low high) = [low, high]

    -- States that derive at least one finite term.
    productiveStates :: Map.Map InternedState [ViewTransition] -> Set.Set InternedState
    productiveStates rows = grow Set.empty
      where
        grow known =
            let next = Map.keysSet $ Map.filter (any $ all (`Set.member` known) . FTA.transitionChildren) rows
             in if next == known then known else grow next

    -- Rewrite every child that targeted a removed supertype state.
    redirectTransition :: Map.Map InternedState InternedState -> ViewTransition -> ViewTransition
    redirectTransition redirects transition =
        transition{FTA.transitionChildren = map redirect $ FTA.transitionChildren transition}
      where
        redirect state = Map.findWithDefault state state redirects

    -- Whether a transition and every transition below it have no constraint.
    unconstrainedBelow :: Map.Map InternedState [ViewTransition] -> ViewTransition -> Bool
    unconstrainedBelow rows transition =
        all ((== noConstraint) . FTA.transitionConstraint) $
            transition : concat [Map.findWithDefault [] state rows | state <- Set.toList below]
      where
        below = grow $ Set.fromList $ FTA.transitionChildren transition
        grow known =
            let next =
                    known
                        <> Set.fromList
                            [child | state <- Set.toList known, edge <- Map.findWithDefault [] state rows, child <- FTA.transitionChildren edge]
             in if next == known then known else grow next

    -- Whether each guard keeps its answer when the terms of the state change
    -- to terms of a representative with a stronger refinement. A guard can read
    -- the state only at the end of a path, and only where 'guardReads' calls
    -- the read monotone. A structural read must not contain the state.
    keepsGuards :: Map.Map InternedState [ViewTransition] -> InternedState -> Bool
    keepsGuards rows state = all (all keeps) $ Map.elems rows
      where
        -- The states whose terms can contain a term of the state.
        containing = grow $ Set.singleton state
          where
            grow known =
                let next = known <> Map.keysSet (Map.filter (any $ any (`Set.member` known) . FTA.transitionChildren) rows)
                 in if next == known then known else grow next
        keeps transition = all readable $ Set.toList $ constraintPaths constraint
          where
            constraint = FTA.transitionConstraint transition
            GuardReads{monotoneReads, sensitiveReads, structuralReads} = guardReads $ constraintGuard constraint
            structural = structuralReads <> constraintPaths constraint{constraintGuard = Top}
            readable target =
                let levels = statesAlong transition target
                    end = if null levels then Set.empty else last levels
                    subterm = if null levels then Set.fromList (FTA.transitionChildren transition) else end
                 in Set.notMember state (Set.unions $ drop 1 $ reverse levels)
                        && ( Set.notMember state end
                                || ( Set.member target monotoneReads
                                        && Set.notMember target sensitiveReads
                                        && Set.notMember target structural
                                   )
                           )
                        && (Set.notMember target structural || Set.disjoint subterm containing)
        -- The states at each nonempty prefix of a path below a transition.
        statesAlong transition target = case unPath target of
            [] -> []
            ChildIndex index : rest -> scanl descend (Set.fromList $ toList $ FTA.transitionChildren transition !? index) rest
        descend states (ChildIndex index) =
            Set.fromList
                [ child
                | known <- Set.toList states
                , edge <- Map.findWithDefault [] known rows
                , Just child <- [FTA.transitionChildren edge !? index]
                ]

{- | The paths of a guard by how a stronger refinement of the term at a path
changes the answer.

'Satisfies' and 'Holds' assume the refinements of their terms, and their
negations ask the refinements to refute the formula, so a stronger refinement
keeps both answers: these reads are monotone. The antecedent of a positive
'Entails' is monotone too. Its consequent is a conclusion, and a negated
'Entails' negates the answer, so these reads are sensitive. 'Same' compares
whole terms, and a substitution renames the terms below it, so their reads
are structural.
-}
guardReads :: Guard -> GuardReads
guardReads = go True
  where
    go positive guard = case guard of
        Satisfies target _ -> mempty{monotoneReads = Set.singleton target}
        Holds targets _ -> mempty{monotoneReads = Set.fromList targets}
        Entails antecedent consequent
            | positive -> mempty{monotoneReads = Set.singleton antecedent, sensitiveReads = Set.singleton consequent}
            | otherwise -> mempty{sensitiveReads = Set.fromList [antecedent, consequent]}
        Not nested -> go (not positive) nested
        And guards -> foldMap (go positive) guards
        Or guards -> foldMap (go positive) guards
        _ -> mempty{structuralReads = guardPaths guard}

-- | The paths of a guard by the kind of read, as 'guardReads' gives them.
data GuardReads = GuardReads
    { monotoneReads :: Set.Set Path
    , sensitiveReads :: Set.Set Path
    , structuralReads :: Set.Set Path
    }

instance Semigroup GuardReads where
    GuardReads monotone sensitive structural <> GuardReads monotone' sensitive' structural' =
        GuardReads (monotone <> monotone') (sensitive <> sensitive') (structural <> structural')

instance Monoid GuardReads where
    mempty = GuardReads Set.empty Set.empty Set.empty

-- | Every unordered pair of distinct list elements, preserving first-seen order.
unorderedPairs :: [a] -> [(a, a)]
unorderedPairs [] = []
unorderedPairs (value : rest) = [(value, other) | other <- rest] <> unorderedPairs rest
