-- | Shared size indexing for ordinary, possibly recursive automata.
module Data.CFTA.Gen.Internal.Table (
    rowsOf,
    automatonIndex,
    tableIndex,
    minimumSizes,
) where

import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Tree as Tree

import Data.Hashable (Hashable)
import qualified Data.IntMap.Strict as IntMap
import Data.Typeable (Typeable)

import qualified Data.CFTA as FTA
import Data.CFTA.Index (Size)
import Data.CFTA.Interned (Node, NodeId (..), edgeChildren, edgeSymbol, nodeIdentity, reachable)
import Data.CFTA.Ranked.Internal.Size (
    MinimumSize (..),
    SizeIndex,
    choiceIndex,
    closedProbe,
    constantIndex,
    mapIndex,
    productIndex,
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
tableIndex initial rows = indexOf initial
  where
    minima = minimumSizes rows
    table = LazyMap.mapWithKey stateIndex rows
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

        consumeChild built child = productIndex (mapIndex prepend built) child

        prepend build term arguments = build (term : arguments)
    indexOf state
        | Map.member state minima = Map.findWithDefault emptyIndex state table
        | otherwise = emptyIndex
    emptyIndex = choiceIndex []

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
