{-# LANGUAGE PatternSynonyms #-}

{- | Transitions, automata, and the structural validation of an LTA.

'mkAutomaton' is the only construction path. It checks that each ranked symbol
keeps one arity and that no guard inspects a position whose state is recursive.
-}
module Data.LTA.Automaton (
    Transition,
    pattern Transition,
    transitionSymbol,
    transitionRefinement,
    transitionChildren,
    transitionConstraint,
    transitionEqualities,
    transitionLiquidSymbol,
    replaceTransitionChildren,
    Automaton,
    StateView (..),
    toTree,
    EqualityAutomaton,
    AutomatonError (..),
    InternedAutomatonError (..),
    fromInterned,
    annotateFTA,
    mkAutomaton,
    mkAutomatonWithFinals,
    fromFTAError,
    automatonInitial,
    automatonStates,
    automatonAlphabet,
    automatonTransitions,
    transitionsAt,
    statesBelow,
    unusedStates,
    reserveState,
    atIndex,
) where

import Data.Bifunctor (first)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Tree (Tree)

import Data.ECTA.Paths (EqConstraints, Path, unPath)
import Data.ECTA.Term (Symbol)
import Data.Tree.FTA (StateView (..))
import qualified Data.Tree.FTA as FTA
import qualified Data.Tree.FTA.Interned as Interned

import Data.LTA.Constraint (
    LiquidConstraint (constraintEqualities),
    constraintPaths,
 )
import Data.LTA.Types (LiquidSymbol (LiquidSymbol), Refinement, State (State))

-- | One refinement-labelled, constrained alternative from an LTA state.
type Transition = FTA.Transition State LiquidSymbol LiquidConstraint

-- | Construct or match an LTA transition.
pattern Transition :: Symbol -> Refinement -> [State] -> LiquidConstraint -> Transition
pattern Transition symbol refinement children constraint =
    FTA.Transition (LiquidSymbol symbol refinement) children constraint

{-# COMPLETE Transition #-}

-- | Symbol at the root of a transition.
transitionSymbol :: FTA.Transition State LiquidSymbol constraint -> Symbol
transitionSymbol (FTA.Transition (LiquidSymbol symbol _) _ _) = symbol

-- | Refinement formula at the root of a transition.
transitionRefinement :: FTA.Transition State LiquidSymbol constraint -> Refinement
transitionRefinement (FTA.Transition (LiquidSymbol _ refinement) _ _) = refinement

-- | Child states of a transition, from left to right.
transitionChildren :: FTA.Transition State LiquidSymbol constraint -> [State]
transitionChildren = FTA.transitionChildren

-- | Complete equality and semantic constraint attached to a transition.
transitionConstraint :: Transition -> LiquidConstraint
transitionConstraint = FTA.transitionGuard

-- | ECTA equality classes attached to a transition.
transitionEqualities :: Transition -> EqConstraints
transitionEqualities = constraintEqualities . transitionConstraint

-- | Liquid symbol carried by a transition.
transitionLiquidSymbol :: Transition -> LiquidSymbol
transitionLiquidSymbol (FTA.Transition symbol _ _) = symbol

-- | Replace only the child states of one transition.
replaceTransitionChildren :: [State] -> Transition -> Transition
replaceTransitionChildren children transition =
    Transition
        (transitionSymbol transition)
        (transitionRefinement transition)
        children
        (transitionConstraint transition)

-- | A validated LTA, possibly with recursive states.
type Automaton = FTA.FTA State LiquidSymbol LiquidConstraint

{- | Expose the reachable LTA graph as typed state and transition labels.

Transitions retain their refinements and constraints. 'Recursive' and 'Shared'
state labels identify references. Map the labels to strings before using
@drawTree@. This operation does not enumerate terms or call a solver.
-}
toTree :: Automaton -> Tree (Either (StateView State) Transition)
toTree = FTA.toTree

-- | The ECTA-shaped result of discharging every semantic guard in an LTA.
type EqualityAutomaton = FTA.FTA State LiquidSymbol EqConstraints

-- | A structural error found while constructing an automaton.
data AutomatonError
    = MissingInitialState !State
    | -- | A declared accepting state has no transition row.
      MissingFinalState !State
    | DanglingState !State
    | {- | A guard position reaches a recursive state, which would produce an
      unbounded logical obligation during semantic operations.
      -}
      CyclicGuardReference !State !Path
    | InconsistentArity !Symbol !Int !Int
    | -- | Named guard arguments do not match the constructor's child count.
      GuardArityMismatch !Symbol !Int !Int
    deriving (Eq, Show)

-- | Failure while validating an interned graph as an LTA.
data InternedAutomatonError
    = InvalidInternedGraph !(Interned.FTAViewError LiquidSymbol)
    | InvalidLiquidAutomaton !AutomatonError
    deriving (Eq, Show)

{- | Validate a common interned automaton with liquid constraints.

This operation retains refinements and guards. It assigns consecutive state
names and applies the same path and recursion checks as 'mkAutomaton'. It does
not enumerate terms or call a solver.
-}
fromInterned ::
    Interned.Node LiquidSymbol LiquidConstraint ->
    Either InternedAutomatonError Automaton
fromInterned root = do
    graph <- first InvalidInternedGraph (Interned.toFTA root)
    first InvalidLiquidAutomaton $ annotateFTA annotate graph
  where
    annotate _ transition =
        let LiquidSymbol symbol refinement = FTA.transitionSymbol transition
         in (symbol, refinement, FTA.transitionGuard transition)

{- | Add liquid labels and constraints to an existing FTA.

The callback receives the source state and transition. It supplies the result
symbol, refinement, and constraint. Constructor children retain their order.
The result uses consecutive state names and normal LTA validation.
-}
annotateFTA ::
    (Ord state) =>
    (state -> FTA.Transition state symbol guard -> (Symbol, Refinement, LiquidConstraint)) ->
    FTA.FTA state symbol guard ->
    Either AutomatonError Automaton
annotateFTA annotate graph =
    mkAutomaton
        (rename $ FTA.initialState graph)
        [(rename state, map (transition state) outgoing) | (state, outgoing) <- Map.toList $ FTA.transitionTable graph]
  where
    names = Map.fromList $ zip (FTA.states graph) (map State [0 ..])
    rename state = names Map.! state
    transition state source =
        let (symbol, refinement, constraint) = annotate state source
         in Transition symbol refinement (map rename $ FTA.transitionChildren source) constraint

-- | Validate and construct an LTA, including guarded-cycle well-formedness.
mkAutomaton :: State -> [(State, [Transition])] -> Either AutomatonError Automaton
mkAutomaton initial rows = do
    automaton <- first fromFTAError $ FTA.mkFTA initial rows
    ensureConsistentSymbolArity automaton
    ensureGuardedPositionsAcyclic automaton
    pure automaton

-- | Translate a structural FTA error into the LTA error vocabulary.
fromFTAError :: FTA.FTAError State LiquidSymbol -> AutomatonError
fromFTAError (FTA.MissingInitialState state) = MissingInitialState state
fromFTAError (FTA.DanglingState state) = DanglingState state
fromFTAError (FTA.InconsistentArity (LiquidSymbol symbol _) expected actual) =
    InconsistentArity symbol expected actual

{- | Construct the paper's LTA with an arbitrary final-state set.

Internally, multiple final states are normalized to one fresh state whose row
is the union of their outgoing transitions. This preserves
@union [JqK | q <- Qf]@ from Figure 6 without adding epsilon transitions or
changing any constructor in the ranked alphabet. An empty final-state set uses
a fresh state with no transitions. A singleton set needs no normalization.
-}
mkAutomatonWithFinals ::
    [State] ->
    [(State, [Transition])] ->
    Either AutomatonError Automaton
mkAutomatonWithFinals finals rows =
    case missingFinals of
        missing : _ -> Left $ MissingFinalState missing
        [] -> case uniqueFinals of
            [final] -> mkAutomaton final rows
            _ -> mkAutomaton normalizedFinal ((normalizedFinal, finalTransitions) : rows)
  where
    table = Map.fromListWith (flip (<>)) rows
    uniqueFinals = Set.toAscList $ Set.fromList finals
    missingFinals = filter (`Map.notMember` table) uniqueFinals
    normalizedFinal = fst $ reserveState $ unusedStates table
    finalTransitions = concatMap (table Map.!) uniqueFinals

{- | Initial state of an LTA.

It is also the single accepting state: 'mkAutomatonWithFinals' normalizes
the paper's arbitrary final-state set to one fresh state.
-}
automatonInitial :: FTA.FTA State LiquidSymbol constraint -> State
automatonInitial = FTA.initialState

{- | States of the normalized LTA.

The implementation uses the standard top-down presentation of the paper's
bottom-up transition relation. Its initial state is the single normalized
accepting state.
-}
automatonStates :: FTA.FTA State LiquidSymbol constraint -> Set.Set State
automatonStates = Set.fromList . FTA.states

-- | Finite ranked alphabet actually used by an automaton.
automatonAlphabet :: FTA.FTA State LiquidSymbol constraint -> Set.Set LiquidSymbol
automatonAlphabet automaton =
    Set.fromList
        [ FTA.transitionSymbol transition
        | transitions <- Map.elems $ automatonTransitions automaton
        , transition <- transitions
        ]

-- | Complete transition table of an LTA.
automatonTransitions ::
    FTA.FTA State LiquidSymbol constraint -> Map.Map State [FTA.Transition State LiquidSymbol constraint]
automatonTransitions = FTA.transitionTable

{- | States reached at a non-empty position below one transition.

The first component selects a child state of the transition itself. Each later
component selects the same child position of every transition available at the
states reached so far. An invalid component denotes no state. The result holds
one entry for each derivation, so a caller that needs a set must deduplicate it.
-}
statesBelow :: Map.Map State [Transition] -> Transition -> [Int] -> [State]
statesBelow table transition components =
    case components of
        [] -> []
        index : rest ->
            descend rest $ maybe [] pure $ atIndex index $ transitionChildren transition
  where
    descend [] current = current
    descend (index : rest) current =
        descend
            rest
            [ child
            | state <- current
            , outgoing <- Map.findWithDefault [] state table
            , Just child <- [atIndex index $ transitionChildren outgoing]
            ]

{- | Transitions reachable at a position below one transition (Definition 5).

The empty position denotes the supplied transition. A non-empty position first
selects one child state and then unions the alternatives encountered at each
subsequent component. An invalid component denotes the empty set.
-}
transitionsAt :: Automaton -> Transition -> Path -> [Transition]
transitionsAt automaton transition target =
    case unPath target of
        [] -> [transition]
        components ->
            concatMap (FTA.transitionsFrom automaton) $
                statesBelow (automatonTransitions automaton) transition components

-- | Every ranked symbol must keep one arity across the automaton.
ensureConsistentSymbolArity :: Automaton -> Either AutomatonError ()
ensureConsistentSymbolArity automaton = go Map.empty allTransitions
  where
    allTransitions = concat $ Map.elems $ automatonTransitions automaton

    go _ [] = Right ()
    go arities (transition : rest) =
        let symbol = transitionSymbol transition
            arity = length $ transitionChildren transition
         in case Map.lookup symbol arities of
                Nothing -> go (Map.insert symbol arity arities) rest
                Just expected
                    | expected == arity -> go arities rest
                    | otherwise -> Left (InconsistentArity symbol expected arity)

-- | No guard may inspect a position whose state is recursive.
ensureGuardedPositionsAcyclic :: Automaton -> Either AutomatonError ()
ensureGuardedPositionsAcyclic automaton =
    case referencesIntoCycles of
        (state, target) : _ -> Left (CyclicGuardReference state target)
        [] -> Right ()
  where
    cyclic = FTA.cyclicStates automaton
    referencesIntoCycles =
        [ (referenced, target)
        | (state, transitions) <- Map.toList $ automatonTransitions automaton
        , transition <- transitions
        , target <- constraintPaths $ transitionConstraint transition
        , referenced <- Set.toList $ statesAtPath automaton state transition target
        , Set.member referenced cyclic
        ]

-- | States that one guarded position of a transition can reach.
statesAtPath :: Automaton -> State -> Transition -> Path -> Set.Set State
statesAtPath automaton parent transition target =
    case unPath target of
        [] -> Set.singleton parent
        components ->
            Set.fromList $ statesBelow (automatonTransitions automaton) transition components

-- | Unused identities, excluding child references before graph validation.
unusedStates :: Map.Map State [Transition] -> [State]
unusedStates table =
    filter (`Set.notMember` occupied) $ map State $ [0 .. maxBound] <> [minBound .. -1]
  where
    occupied =
        Map.keysSet table
            `Set.union` Set.fromList
                [ child
                | transitions <- Map.elems table
                , transition <- transitions
                , child <- transitionChildren transition
                ]

{- | Consume one unused identity from the state domain.

The domain is every 'Int' identity not already in use, so it is exhausted
only after every machine integer names a state.
-}
reserveState :: [State] -> (State, [State])
reserveState (state : remaining) = (state, remaining)
reserveState [] = error "microlta bug in Data.LTA.reserveState: the state domain is exhausted"

-- | Safe zero-based list lookup.
atIndex :: Int -> [a] -> Maybe a
atIndex index values
    | index < 0 = Nothing
    | otherwise = case drop index values of
        value : _ -> Just value
        [] -> Nothing
