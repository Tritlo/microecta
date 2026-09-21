-- | Shared size indexing for ordinary, possibly recursive automata.
module Data.CFTA.Gen.Internal.Automaton (
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
import Data.CFTA.Constraint (Constraint)
import Data.CFTA.Interned (Node, edgeChildren, edgeSymbol, nodeIdentity, reachable)
import Data.CFTA.Ranked.Internal.Size (
    SizeIndex,
    choiceIndex,
    constantIndex,
    mapIndex,
    productIndex,
    withMinimumMemberSize,
 )

{- | The rows of an interned graph, one per reachable node, keyed by node
identity. Constraints are dropped; the caller checks them first. The root
must not be the empty node.
-}
rowsOf ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Node symbol constraint -> Map.Map Int [FTA.Transition Int symbol ()]
rowsOf root =
    Map.fromList
        [ (ident, [FTA.Transition (edgeSymbol edge) (map nodeIdentity $ edgeChildren edge) () | edge <- edges])
        | (ident, edges) <- IntMap.toList (reachable root)
        ]

{- | Count accepting runs by their number of tree nodes.

Ranks are size-major. Ambiguous automata can assign several ranks to one term.
Each state shares one index, including recursive references to that index.
-}
automatonIndex :: (Ord state) => FTA.PlainFTA state symbol -> SizeIndex (Tree.Tree symbol)
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
    stateIndex state transitions =
        withMinimumMemberSize
            (Map.lookup state minima)
            (choiceIndex $ map transitionIndex transitions)
    indexOf state
        | Map.member state minima = Map.findWithDefault emptyIndex state table
        | otherwise = emptyIndex
    emptyIndex = choiceIndex []
    transitionIndex transition =
        mapIndex ($ []) $
            foldl'
                consumeChild
                (constantIndex $ Tree.Node $ FTA.transitionSymbol transition)
                (map indexOf $ FTA.transitionChildren transition)
    consumeChild built child = productIndex (mapIndex prepend built) child
    prepend build term arguments = build (term : arguments)

{- | Find the least finite term size of each productive state.

Start with no productive states and solve the least fixed point. A cycle with
no finite base remains absent. This keeps an empty recursive index finite.
-}
minimumSizes :: (Ord state) => Map.Map state [FTA.Transition state symbol ()] -> Map.Map state Int
minimumSizes rows = converge Map.empty
  where
    converge current =
        let next = Map.foldrWithKey addMinimum current rows
         in if next == current then current else converge next
    addMinimum state transitions known =
        case mapMaybe (transitionMinimum known) transitions of
            [] -> known
            sizes -> Map.insertWith min state (minimum sizes) known
    transitionMinimum known transition =
        (1 +) . sum <$> traverse (`Map.lookup` known) (FTA.transitionChildren transition)
