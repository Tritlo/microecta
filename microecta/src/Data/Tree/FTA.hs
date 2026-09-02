{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}

{- | Ordinary finite-state tree automata.

An FTA has a finite set of states and ranked transitions. The @guard@ parameter
is merely a transition annotation: use @()@ for an ordinary FTA,
"Data.ECTA.Paths" equality constraints for an ECTA view, or a liquid guard for
an LTA. Constraint theories stay in their own packages.

Cycles are valid and describe infinite tree languages. Consumers that require
a finite language can inspect 'cycleState'. 'intersect' constructs the standard
reachable product; 'intersectWith' lets a constraint layer decide how matching
symbols and transition annotations combine.
-}
module Data.Tree.FTA (
    FTA,
    PlainFTA,
    ProductState (..),
    Transition (..),
    FTAError (..),
    initialState,
    transitionTable,
    mkFTA,
    states,
    transitionsFrom,
    cyclicStates,
    cycleState,
    mapGuards,
    stripGuards,
    intersect,
    intersectWith,
    accepts,
) where

import Control.Monad (foldM)
import Data.Graph (SCC (AcyclicSCC, CyclicSCC), stronglyConnComp)
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

-- | A state in the product of two tree automata.
data ProductState left right = ProductState
    { productLeftState :: !left
    -- ^ State contributed by the left automaton.
    , productRightState :: !right
    -- ^ State contributed by the right automaton.
    }
    deriving (Eq, Ord, Show)

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
cycleState = Set.lookupMin . cyclicStates

{- | All states that participate in a dependency cycle.

A singleton strongly connected component is cyclic only when it has a direct
self-edge. This is useful to consumers such as LTAs, which permit recursive
languages but restrict what constraints may inspect inside them.
-}
cyclicStates :: (Ord state) => FTA state symbol guard -> Set.Set state
cyclicStates automaton =
    Set.fromList $ concatMap componentStates components
  where
    components = stronglyConnComp $ map dependencyNode (states automaton)

    dependencyNode state =
        ( state
        , state
        , [ child
          | transition <- transitionsFrom automaton state
          , child <- transitionChildren transition
          ]
        )

    componentStates (CyclicSCC component) = component
    componentStates (AcyclicSCC state)
        | state `elem` directChildren state = [state]
        | otherwise = []

    directChildren state =
        [ child
        | transition <- transitionsFrom automaton state
        , child <- transitionChildren transition
        ]

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

{- | Intersect two automata with the same ranked alphabet.

Only reachable product states are constructed. Transition annotations from the
two operands are paired; use 'intersectWith' when the constraint theory has a
more useful way to combine them. Applying 'stripGuards' to the result of two
plain FTAs recovers a 'PlainFTA'.
-}
intersect ::
    (Ord leftState, Ord rightState, Ord symbol) =>
    FTA leftState symbol leftGuard ->
    FTA rightState symbol rightGuard ->
    Either
        (FTAError (ProductState leftState rightState) symbol)
        (FTA (ProductState leftState rightState) symbol (leftGuard, rightGuard))
intersect = intersectWith sameSymbol (,)
  where
    sameSymbol left right
        | left == right = Just left
        | otherwise = Nothing

{- | Product intersection with explicit symbol matching and guard composition.

The symbol callback returns the result label for compatible transitions and
'Nothing' for disjoint ones. Children are intersected position by position.
The result is validated because a callback may map differently ranked input
symbols to the same output symbol.
-}
intersectWith ::
    (Ord leftState, Ord rightState, Ord resultSymbol) =>
    (leftSymbol -> rightSymbol -> Maybe resultSymbol) ->
    (leftGuard -> rightGuard -> resultGuard) ->
    FTA leftState leftSymbol leftGuard ->
    FTA rightState rightSymbol rightGuard ->
    Either
        (FTAError (ProductState leftState rightState) resultSymbol)
        (FTA (ProductState leftState rightState) resultSymbol resultGuard)
intersectWith matchSymbol combineGuard left right =
    mkFTA initial $ build Set.empty [initial] []
  where
    initial = ProductState (initialState left) (initialState right)

    build _ [] rows = reverse rows
    build visited (productState : pending) rows
        | Set.member productState visited = build visited pending rows
        | otherwise =
            build
                (Set.insert productState visited)
                (concatMap transitionChildren outgoing <> pending)
                ((productState, outgoing) : rows)
      where
        outgoing = intersectState productState

    intersectState (ProductState leftState rightState) =
        [ Transition
            resultSymbol
            (zipWith ProductState leftChildren rightChildren)
            (combineGuard leftGuard rightGuard)
        | Transition leftSymbol leftChildren leftGuard <- transitionsFrom left leftState
        , Transition rightSymbol rightChildren rightGuard <- transitionsFrom right rightState
        , length leftChildren == length rightChildren
        , Just resultSymbol <- [matchSymbol leftSymbol rightSymbol]
        ]

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
