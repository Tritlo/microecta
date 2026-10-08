-- | Shared size indexing for ordinary, possibly recursive automata.
module Data.CFTA.Gen.Internal.Table (
    rowsOf,
    automatonIndex,
    tableIndex,
    tablePosition,
    minimumSizes,
) where

import Control.Monad (zipWithM)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Tree as Tree

import Data.Hashable (Hashable)
import qualified Data.IntMap.Strict as IntMap
import Data.Typeable (Typeable)

import qualified Data.CFTA as FTA
import Data.CFTA.Index (Size, TransitionIndex (..))
import Data.CFTA.Interned (Node, NodeId (..), edgeChildren, edgeSymbol, nodeIdentity, reachable)
import Data.CFTA.Ranked.Internal.Size (
    ChoiceIndex (..),
    MinimumSize (..),
    SizeIndex,
    SizedRank (..),
    choiceIndex,
    choicePosition,
    closedProbe,
    constantIndex,
    mapIndex,
    productIndex,
    productPosition,
    withKnotMetadata,
 )

{- | The rows of an interned graph, one per reachable node, keyed by node
identity. Constraints are dropped; the caller checks them first. The root
must not be the empty node.
-}
rowsOf ::
    (Hashable symbol, Typeable symbol) =>
    Node symbol -> Map.Map NodeId [FTA.Transition NodeId symbol ()]
rowsOf root =
    Map.fromDistinctAscList
        [ (NodeId ident, [FTA.Transition (edgeSymbol edge) (map nodeIdentity $ edgeChildren edge) () | edge <- edges])
        | (ident, edges) <- IntMap.toList (reachable root)
        ]

{- | Count accepting runs by their number of tree nodes.

Ranks are size-major. Ambiguous automata can assign several ranks to one term.
Each state shares one index, including recursive references to that index.
-}
automatonIndex :: (Ord state) => FTA.FTA state symbol () -> SizeIndex (Tree.Tree symbol)
automatonIndex automaton = tableIndex (FTA.initialState automaton) (FTA.transitionTable automaton)

{- | Index ordinary transition rows supplied by a graph adapter.

Missing rows accept nothing. Constraint layers must validate their annotations
before supplying ordinary rows. This worker does not interpret constraints.
-}
tableIndex ::
    (Ord state) => state -> Map.Map state [FTA.Transition state symbol ()] -> SizeIndex (Tree.Tree symbol)
tableIndex initial rows = fst (stateTable rows) initial

{- | Find the size class and the position in it of a term that the initial
state accepts, as 'tableIndex' selects the term.

The size is the number of term nodes. 'Nothing' means that the initial state
does not accept the term. The rows must be unambiguous: one run at most
accepts each term. The positions are found bottom-up, once for each subterm
and each state that accepts it, so no subterm is ranked again. Apply the
function to the rows once: each term then uses the same counts.
-}
tablePosition ::
    (Ord state, Ord symbol) =>
    state -> Map.Map state [FTA.Transition state symbol ()] -> Tree.Tree symbol -> Maybe SizedRank
tablePosition initial rows = Map.lookup initial . positionsOf
  where
    (indexOf, prefixesOf) = stateTable rows
    -- The candidates by symbol and arity. The candidates of a state share
    -- its transition indexes, so they are built once for each state.
    candidates =
        Map.fromListWith
            (flip (<>))
            [ ( (FTA.transitionSymbol transition, length $ FTA.transitionChildren transition)
              , [(state, branch, transition, prefixes, indexes)]
              )
            | state <- Map.keys rows
            , let indexes = map (NonEmpty.last . snd) $ prefixesOf state
            , (branch, (transition, prefixes)) <- zip [0 :: TransitionIndex ..] $ prefixesOf state
            ]
    -- The size and position of a term in each state that accepts it. The
    -- index of a state is a choice over its transitions, so the index of a
    -- transition is its choice index.
    positionsOf (Tree.Node symbol children) =
        Map.fromList
            [ (state, SizedRank size (choicePosition indexes (ChoiceIndex branch) size position))
            | (state, TransitionIndex branch, transition, prefixes, indexes) <-
                Map.findWithDefault [] (symbol, length children) candidates
            , Just childPositions <- [zipWithM Map.lookup (FTA.transitionChildren transition) childMaps]
            , let SizedRank size position =
                    foldl' addChild (SizedRank 1 0) $ zip3 (NonEmpty.toList prefixes) (FTA.transitionChildren transition) childPositions
            ]
      where
        childMaps = map positionsOf children

        addChild built (prefix, child, childPosition) =
            productPosition prefix (indexOf child) built childPosition

{- | The size index of each state, and the transitions of each state with the
indexes of their child prefixes.

The first prefix index holds the symbol alone. Each next prefix index adds one
child, and the last one holds the terms of the transition. Each state has one
index, which recursive references to the state share.
-}
stateTable ::
    (Ord state) =>
    Map.Map state [FTA.Transition state symbol ()] ->
    ( state -> SizeIndex (Tree.Tree symbol)
    , state -> [(FTA.Transition state symbol (), NonEmpty (SizeIndex ([Tree.Tree symbol] -> Tree.Tree symbol)))]
    )
stateTable rows = (indexOf, prefixesOf)
  where
    minima = minimumSizes rows
    prefixTable = LazyMap.map (map $ \transition -> (transition, childPrefixes transition)) rows
      where
        childPrefixes transition =
            NonEmpty.scanl
                consumeChild
                (constantIndex $ Tree.Node $ FTA.transitionSymbol transition)
                (map indexOf $ FTA.transitionChildren transition)
    -- Sampling reads this index. It is built directly, not as the last child
    -- prefix, because an index from the prefix list made each sample slower
    -- (about 1% more instructions in the sampling benchmarks).
    indexTable = LazyMap.mapWithKey stateIndex rows
      where
        stateIndex state transitions =
            -- The rows are closed, so they reach no probe of an enclosing definition.
            withKnotMetadata
                (maybe NoFiniteMember MinimumSize $ Map.lookup state minima)
                (closedProbe NoFiniteMember)
                (choiceIndex $ map transitionIndex transitions)

        transitionIndex transition =
            mapIndex ($ []) $
                foldl'
                    consumeChild
                    (constantIndex $ Tree.Node $ FTA.transitionSymbol transition)
                    (map indexOf $ FTA.transitionChildren transition)
    indexOf state
        | Map.member state minima = Map.findWithDefault emptyIndex state indexTable
        | otherwise = emptyIndex
    prefixesOf state
        | Map.member state minima = Map.findWithDefault [] state prefixTable
        | otherwise = []
    emptyIndex = choiceIndex []
    consumeChild built child = productIndex (mapIndex prepend built) child
      where
        prepend build term arguments = build (term : arguments)

{- | Find the least finite term size of each productive state.

Start with no productive states and solve the least fixed point. A cycle with
no finite base remains absent. This keeps an empty recursive index finite.
-}
minimumSizes :: (Ord state) => Map.Map state [FTA.Transition state symbol ()] -> Map.Map state Size
minimumSizes rows = converge Map.empty
  where
    converge current =
        let next = Map.foldrWithKey addMinimum current rows
         in if next == current then current else converge next
      where
        addMinimum state transitions known =
            case mapMaybe (transitionMinimum known) transitions of
                [] -> known
                sizes -> Map.insertWith min state (minimum sizes) known
    transitionMinimum known transition =
        (1 +) . sum <$> traverse (`Map.lookup` known) (FTA.transitionChildren transition)
