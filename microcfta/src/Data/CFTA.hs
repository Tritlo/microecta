{-# LANGUAGE DeriveFunctor #-}

{- | Ordinary finite-state tree automata.

An FTA has a finite set of states and ranked transitions. The @constraint@ parameter
is only a transition annotation: use @()@ for an ordinary FTA, or a constraint
from one of the constraint theories.

Cycles are valid and describe infinite tree languages. Consumers that require
a finite language can inspect 'cycleState'. 'intersect' constructs the standard
reachable product; 'intersectWith' lets a constraint layer decide how matching
symbols and transition annotations combine.
-}
module Data.CFTA (
    FTA,
    PlainFTA,
    ProductState (..),
    Transition (..),
    FTAError (..),
    initialState,
    transitionTable,
    mkFTA,
    fromTerms,
    states,
    transitionsFrom,
    cyclicStates,
    cycleState,
    mapConstraints,
    mapSymbols,
    mapStates,
    trim,
    annotate,
    dropConstraints,
    boundDepth,
    intersect,
    intersectWith,
    accepts,
    acceptsM,
    statesAt,
    terms,
    termsUpToM,
    ViewPath,
    StateView (..),
    toTree,
) where

import Control.Monad (foldM_, void)
import qualified Control.Monad.State.Strict as State
import qualified Data.Bifunctor as Bifunctor
import Data.Graph (SCC (CyclicSCC), stronglyConnComp)
import Data.Hashable (Hashable)
import Data.List ((!?))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (maybeToList)
import qualified Data.Set as Set
import qualified Data.Tree as Tree

import Data.CFTA.Internal.Tree (StateView (..), ViewPath, allM, anyM, termsBy, termsUpToBy, toTreeBy, trimRows)
import Data.CFTA.Path (Path (ConsPath, EmptyPath))

-- | One ranked transition from a parent state to child states.
data Transition state symbol constraint = Transition
    { transitionSymbol :: !symbol
    -- ^ Constructor at the root of this transition.
    , transitionChildren :: ![state]
    -- ^ States accepting the constructor arguments, from left to right.
    , transitionConstraint :: !constraint
    -- ^ Constraint-specific annotation; @()@ for an ordinary FTA.
    }
    deriving (Eq, Show, Functor)

-- | A validated finite-state tree automaton with one initial state.
data FTA state symbol constraint = FTA
    { initialState :: !state
    -- ^ State from which whole-term recognition starts.
    , transitionTable :: !(Map state [Transition state symbol constraint])
    -- ^ Complete outgoing-transition rows, keyed by parent state.
    }
    deriving (Eq, Show, Functor)

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

{- | Expose the reachable grammar as a finite tree of typed labels.

'Left' labels contain state definitions or references. 'Right' labels contain
the original transitions, including symbols, child states, and annotations.
Each node label also retains its 'viewPath' from the root of this view.
Use @fmap (either renderState renderTransition)@ to prepare a tree for
'Tree.drawTree'. Each state is expanded once, so sharing and recursion keep
the view finite. This operation does not enumerate terms or interpret constraints.
-}
toTree ::
    (Ord state) =>
    FTA state symbol constraint -> Tree.Tree (Either (StateView state) (Transition state symbol constraint))
toTree automaton = toTreeBy (transitionsFrom automaton) transitionChildren $ initialState automaton

-- | Validate and construct an FTA. Cyclic automata are accepted.
mkFTA ::
    (Ord state, Ord symbol) =>
    state ->
    [(state, [Transition state symbol constraint])] ->
    Either (FTAError state symbol) (FTA state symbol constraint)
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

    ensureRanked table = foldM_ rememberArity Map.empty (concat $ Map.elems table)

    rememberArity arities transition =
        let symbol = transitionSymbol transition
            arity = length (transitionChildren transition)
         in case Map.lookup symbol arities of
                Nothing -> Right (Map.insert symbol arity arities)
                Just expected
                    | expected == arity -> Right arities
                    | otherwise -> Left (InconsistentArity symbol expected arity)

{- | Build the exact finite language of a list of terms.

Equal subterms share one state. The initial state contains the complete terms.
Duplicate terms are removed and alternatives use ascending term order.
-}
fromTerms ::
    (Ord symbol) =>
    [Tree.Tree symbol] -> Either (FTAError (Maybe (Tree.Tree symbol)) symbol) (PlainFTA (Maybe (Tree.Tree symbol)) symbol)
fromTerms input =
    mkFTA Nothing $
        (Nothing, map transition distinct)
            : [(Just term, [transition term]) | term <- Set.toList $ Set.fromList $ concatMap subterms distinct]
  where
    distinct = Set.toList $ Set.fromList input
    transition (Tree.Node symbol children) = Transition symbol (map Just children) ()
    subterms term@(Tree.Node _ children) = term : concatMap subterms children

-- | All states in ascending key order.
states :: FTA state symbol constraint -> [state]
states = Map.keys . transitionTable

-- | Outgoing alternatives of one state.
transitionsFrom :: (Ord state) => FTA state symbol constraint -> state -> [Transition state symbol constraint]
transitionsFrom automaton state =
    Map.findWithDefault [] state (transitionTable automaton)

-- | Find one state on a cycle, if the automaton is cyclic.
cycleState :: (Ord state) => FTA state symbol constraint -> Maybe state
cycleState = Set.lookupMin . cyclicStates

{- | All states that participate in a dependency cycle.

A singleton strongly connected component is cyclic only when it has a direct
self-edge. This is useful to consumers such as LTAs, which permit recursive
languages but restrict what constraints may inspect inside them.
-}
cyclicStates :: (Ord state) => FTA state symbol constraint -> Set.Set state
cyclicStates automaton =
    Set.fromList $ concat [component | CyclicSCC component <- components]
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

-- | Change constructor labels and check that the result stays ranked.
mapSymbols ::
    (Ord state, Ord other) =>
    (symbol -> other) -> FTA state symbol constraint -> Either (FTAError state other) (FTA state other constraint)
mapSymbols transform FTA{initialState, transitionTable} =
    mkFTA initialState [(state, map transition outgoing) | (state, outgoing) <- Map.toList transitionTable]
  where
    transition Transition{transitionSymbol, transitionChildren, transitionConstraint} =
        Transition (transform transitionSymbol) transitionChildren transitionConstraint

{- | Rename states.

States that map to one name are merged, and the merged state has the
alternatives of all of them.
-}
mapStates :: (Ord other) => (state -> other) -> FTA state symbol constraint -> FTA other symbol constraint
mapStates rename automaton =
    FTA (rename $ initialState automaton) $
        Map.fromListWith
            (flip (<>))
            [ (rename state, [transition{transitionChildren = map rename $ transitionChildren transition} | transition <- outgoing])
            | (state, outgoing) <- Map.toList $ transitionTable automaton
            ]

{- | Remove states that accept nothing and states the initial state cannot reach.

Alternatives with a removed child state are removed with them. The initial
state keeps a row, which is empty when the language is empty.
-}
trim :: (Ord state) => FTA state symbol constraint -> FTA state symbol constraint
trim automaton = FTA initial $ trimTable initial $ transitionTable automaton
  where
    initial = initialState automaton

-- | 'trim' on a transition table with the given initial state.
trimTable ::
    (Ord state) => state -> Map state [Transition state symbol constraint] -> Map state [Transition state symbol constraint]
trimTable initial table = Map.insertWith (\_ kept -> kept) initial [] $ trimRows transitionChildren (Map.toList table) initial

-- | Change transition annotations without changing the accepted tree shapes.
mapConstraints :: (constraint -> other) -> FTA state symbol constraint -> FTA state symbol other
mapConstraints = fmap

{- | Set transition annotations with access to their state and constructor.

The graph structure remains unchanged. Constraint layers can interpret the
result without defining its states and transitions again.
-}
annotate ::
    (state -> Transition state symbol constraint -> other) -> FTA state symbol constraint -> FTA state symbol other
annotate transform automaton =
    automaton{transitionTable = Map.mapWithKey (map . annotateTransition) (transitionTable automaton)}
  where
    annotateTransition state transition = transition{transitionConstraint = transform state transition}

-- | Forget transition annotations, yielding an ordinary FTA.
dropConstraints :: FTA state symbol constraint -> PlainFTA state symbol
dropConstraints = void

{- | Retain terms whose leaves are at most the given depth from the root.

A leaf has depth zero. A negative bound produces an empty initial state.
Equal state-depth pairs share one row. The result has consecutive integer
states. A state that has no transition within its remaining depth keeps an
empty row; the interned import removes such dead alternatives. Labels, constraints, and transition order remain unchanged.
-}
boundDepth :: (Ord state) => Int -> FTA state symbol constraint -> FTA Int symbol constraint
boundDepth maximumDepth automaton
    | maximumDepth < 0 = FTA 0 $ Map.singleton 0 []
    | otherwise =
        let (initial, (_, rows)) = State.runState (buildState (initialState automaton, maximumDepth)) (Map.empty, Map.empty)
         in FTA initial rows
  where
    buildState key@(source, remaining) = do
        (names, _) <- State.get
        case Map.lookup key names of
            Just state -> pure state
            Nothing -> do
                let state = Map.size names
                State.modify' $ \(_, rows) -> (Map.insert key state names, rows)
                outgoing <-
                    traverse (buildTransition remaining)
                        $ filter (\transition -> remaining > 0 || null (transitionChildren transition))
                        $ transitionsFrom automaton source
                State.modify' $ Bifunctor.second (Map.insert state outgoing)
                pure state
    buildTransition remaining Transition{transitionSymbol, transitionChildren, transitionConstraint} = do
        children <- traverse (\child -> buildState (child, remaining - 1)) transitionChildren
        pure $ Transition transitionSymbol children transitionConstraint

{- | Intersect two automata with the same ranked alphabet.

Only reachable product states are constructed. Transition annotations from the
two operands are paired; use 'intersectWith' when the constraint theory has a
more useful way to combine them. Applying 'dropConstraints' to the result of two
plain FTAs recovers a 'PlainFTA'.
-}
intersect ::
    (Ord leftState, Ord rightState, Ord symbol) =>
    FTA leftState symbol leftConstraint ->
    FTA rightState symbol rightConstraint ->
    Either
        (FTAError (ProductState leftState rightState) symbol)
        (FTA (ProductState leftState rightState) symbol (leftConstraint, rightConstraint))
intersect = intersectWith sameSymbol (,)
  where
    sameSymbol left right
        | left == right = Just left
        | otherwise = Nothing

{- | Product intersection with explicit symbol matching and constraint composition.

The symbol callback returns the result label for compatible transitions and
'Nothing' for disjoint ones. Children are intersected position by position.
The result is validated because a callback may map differently ranked input
symbols to the same output symbol.
-}
intersectWith ::
    (Ord leftState, Ord rightState, Ord resultSymbol) =>
    (leftSymbol -> rightSymbol -> Maybe resultSymbol) ->
    (leftConstraint -> rightConstraint -> resultConstraint) ->
    FTA leftState leftSymbol leftConstraint ->
    FTA rightState rightSymbol rightConstraint ->
    Either
        (FTAError (ProductState leftState rightState) resultSymbol)
        (FTA (ProductState leftState rightState) resultSymbol resultConstraint)
intersectWith matchSymbol combineConstraint left right =
    mkFTA initial $ build Set.empty [initial] []
  where
    initial = ProductState (initialState left) (initialState right)

    build _ [] rows = rows
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
            (combineConstraint leftConstraint rightConstraint)
        | Transition leftSymbol leftChildren leftConstraint <- transitionsFrom left leftState
        , Transition rightSymbol rightChildren rightConstraint <- transitionsFrom right rightState
        , length leftChildren == length rightChildren
        , Just resultSymbol <- [matchSymbol leftSymbol rightSymbol]
        ]

-- | Decide whether an ordinary FTA accepts a concrete term.
accepts :: (Ord state, Eq symbol) => PlainFTA state symbol -> Tree.Tree symbol -> Bool
accepts automaton = acceptsFrom (initialState automaton)
  where
    acceptsFrom state (Tree.Node symbol children) =
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

{- | Every accepted term, ordered by depth and produced lazily.

A leaf has depth zero, and all terms of one depth precede deeper terms. A
cyclic automaton gives an infinite list; an acyclic automaton gives a finite
one. Each term appears once, even when several runs accept it. Constraints are
not interpreted: the list describes the underlying ordinary automaton. Use
'termsUpToM' to decide constraints while enumerating.
-}
terms :: (Ord state, Ord symbol, Hashable symbol) => FTA state symbol constraint -> [Tree.Tree symbol]
terms automaton =
    termsBy
        [ (state, [(transitionSymbol transition, transitionChildren transition) | transition <- outgoing])
        | (state, outgoing) <- Map.toList (transitionTable automaton)
        ]
        (initialState automaton)

{- | The terms of depth at most the bound that a check accepts.

The check sees each candidate term once, with the state and transition that
built it, so a constraint theory can decide a constraint as soon as the children
are complete. A rejected candidate is never used as a child. A leaf has
depth zero. Each state lists a term once per depth, so an ambiguous
automaton does not repeat terms.
-}
termsUpToM ::
    (Monad m, Ord state, Ord symbol, Hashable symbol) =>
    (state -> Transition state symbol constraint -> Tree.Tree symbol -> m Bool) ->
    Int ->
    FTA state symbol constraint ->
    m [Tree.Tree symbol]
termsUpToM accept bound automaton =
    termsUpToBy
        transitionSymbol
        transitionChildren
        accept
        (Map.toList $ transitionTable automaton)
        bound
        (initialState automaton)

{- | Decide whether an automaton accepts a term, with a check on each matching transition.

The check sees the state, the transition, and the complete term at that
position, so a constraint theory can decide a constraint there. It runs only
after the children have been accepted, and only for transitions whose
symbol and arity match the term. The term is accepted when some transition
matches and passes the check.
-}
acceptsM ::
    (Monad m, Ord state, Eq symbol) =>
    (state -> Transition state symbol constraint -> Tree.Tree symbol -> m Bool) ->
    FTA state symbol constraint ->
    Tree.Tree symbol ->
    m Bool
acceptsM check automaton = acceptsFrom (initialState automaton)
  where
    acceptsFrom state term@(Tree.Node symbol children) =
        anyM
            [ allM (zipWith acceptsFrom (transitionChildren transition) children) >>= \accepted ->
                if accepted then check state transition term else pure False
            | transition <- transitionsFrom automaton state
            , transitionSymbol transition == symbol
            , length (transitionChildren transition) == length children
            ]

{- | The states at a child-index path below a transition of an explicit-state automaton.

The function gives the alternatives of a state: pass @'FTA.transitionsFrom'
automaton@ for an automaton, or a lookup in a bare transition table. The
first index selects a child state of the transition; each further index
selects that child of every alternative of the states reached so far. A
state is listed once per alternative that reaches it. An empty path gives
no states.
-}
statesAt :: (state -> [Transition state symbol constraint]) -> Transition state symbol constraint -> Path -> [state]
statesAt _ _ EmptyPath = []
statesAt alternatives transition (ConsPath index rest) = descend rest (maybeToList $ transitionChildren transition !? index)
  where
    descend EmptyPath current = current
    descend (ConsPath next further) current =
        descend
            further
            [ child
            | state <- current
            , outgoing <- alternatives state
            , Just child <- [transitionChildren outgoing !? next]
            ]
