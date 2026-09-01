{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}

{- | Ordinary finite-state tree automata.

An FTA has a finite set of states and ranked transitions. The @guard@ parameter
is merely a transition annotation: use @()@ for an ordinary FTA,
"Data.ECTA.Paths" equality constraints for an ECTA view, or a liquid guard for
an LTA. Constraint theories stay in their own packages.

Cycles are valid and describe infinite tree languages. Consumers that require
a finite language can inspect 'cycleState'.
-}
module Data.Tree.FTA (
    FTA,
    PlainFTA,
    Transition (..),
    FTAError (..),
    initialState,
    transitionTable,
    mkFTA,
    states,
    transitionsFrom,
    cycleState,
    mapGuards,
    stripGuards,
    accepts,
) where

import Control.Monad (foldM)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.Tree.Term (Term (Term))

-- | One ranked transition from a parent state to child states.
data Transition state symbol guard = Transition
    { transitionSymbol :: !symbol
    -- ^ Constructor at the root of this transition.
    , transitionChildren :: ![state]
    -- ^ States accepting the constructor arguments, from left to right.
    , transitionGuard :: !guard
    -- ^ Constraint-specific annotation; @()@ for an ordinary FTA.
    }
    deriving (Eq, Show)

-- | A validated finite-state tree automaton with one initial state.
data FTA state symbol guard = FTA
    { initialState :: !state
    -- ^ State from which whole-term recognition starts.
    , transitionTable :: !(Map state [Transition state symbol guard])
    -- ^ Complete outgoing-transition rows, keyed by parent state.
    }
    deriving (Eq, Show)

-- | An ordinary FTA with no transition constraints.
type PlainFTA state symbol = FTA state symbol ()

-- | A structural error found while constructing an FTA.
data FTAError state symbol
    = -- | The initial state has no row in the transition table.
      MissingInitialState !state
    | -- | A transition refers to a state with no row.
      DanglingState !state
    | -- | The same alphabet symbol occurs at two different arities.
      InconsistentArity !symbol !Int !Int
    deriving (Eq, Show)

-- | Validate and construct an FTA. Cyclic automata are accepted.
mkFTA ::
    (Ord state, Ord symbol) =>
    state ->
    [(state, [Transition state symbol guard])] ->
    Either (FTAError state symbol) (FTA state symbol guard)
mkFTA initial rows = do
    let table = Map.fromListWith (flip (<>)) rows
    ensureInitial table
    ensureClosed table
    ensureRanked table
    pure FTA{initialState = initial, transitionTable = table}
  where
    ensureInitial table
        | Map.member initial table = Right ()
        | otherwise = Left (MissingInitialState initial)

    ensureClosed table =
        case [ child
             | outgoing <- Map.elems table
             , transition <- outgoing
             , child <- transitionChildren transition
             , Map.notMember child table
             ] of
            dangling : _ -> Left (DanglingState dangling)
            [] -> Right ()

    ensureRanked table = do
        _ <- foldM rememberArity Map.empty (concat $ Map.elems table)
        pure ()

    rememberArity arities transition =
        let symbol = transitionSymbol transition
            arity = length (transitionChildren transition)
         in case Map.lookup symbol arities of
                Nothing -> Right (Map.insert symbol arity arities)
                Just expected
                    | expected == arity -> Right arities
                    | otherwise -> Left (InconsistentArity symbol expected arity)

-- | All states in ascending key order.
states :: FTA state symbol guard -> [state]
states = Map.keys . transitionTable

-- | Outgoing alternatives of one state.
transitionsFrom :: (Ord state) => FTA state symbol guard -> state -> [Transition state symbol guard]
transitionsFrom automaton state =
    Map.findWithDefault [] state (transitionTable automaton)

-- | Find one state on a cycle, if the automaton is cyclic.
cycleState :: (Ord state) => FTA state symbol guard -> Maybe state
cycleState automaton = go Set.empty (states automaton)
  where
    go _ [] = Nothing
    go visited (state : rest)
        | Set.member state visited = go visited rest
        | otherwise = case visit Set.empty visited state of
            Left cyclic -> Just cyclic
            Right visited' -> go visited' rest

    visit visiting visited state
        | Set.member state visiting = Left state
        | Set.member state visited = Right visited
        | otherwise = do
            visitedChildren <-
                foldM
                    (visit $ Set.insert state visiting)
                    visited
                    [ child
                    | transition <- transitionsFrom automaton state
                    , child <- transitionChildren transition
                    ]
            pure (Set.insert state visitedChildren)

-- | Change transition annotations without changing the accepted tree shapes.
mapGuards :: (guard -> other) -> FTA state symbol guard -> FTA state symbol other
mapGuards transform FTA{initialState, transitionTable} =
    FTA
        initialState
        (fmap (map mapTransition) transitionTable)
  where
    mapTransition Transition{transitionSymbol, transitionChildren, transitionGuard} =
        Transition transitionSymbol transitionChildren (transform transitionGuard)

-- | Forget transition annotations, yielding an ordinary FTA.
stripGuards :: FTA state symbol guard -> PlainFTA state symbol
stripGuards = mapGuards (const ())

-- | Decide whether an ordinary FTA accepts a concrete term.
accepts :: (Ord state, Eq symbol) => PlainFTA state symbol -> Term symbol -> Bool
accepts automaton = acceptsFrom (initialState automaton)
  where
    acceptsFrom state (Term symbol children) =
        any (acceptsTransition symbol children) (transitionsFrom automaton state)

    acceptsTransition symbol children transition =
        transitionSymbol transition == symbol
            && length (transitionChildren transition) == length children
            && and
                ( zipWith
                    acceptsFrom
                    (transitionChildren transition)
                    children
                )
