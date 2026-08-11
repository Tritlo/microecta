{- | Counting and indexing the terms an ECTA accepts.

A node's language is the union over its edges, and an edge's language is the
product of its children under its symbol. That is the same shape the
generator combinators build, so an automaton becomes a size index by
translation: 'choiceIndex' per node, 'productIndex' per edge child, and a
size-one 'constantIndex' for the symbol itself, which makes a member's size
its number of term nodes.

Recursion needs no special case. Nodes are interned, so a @Mu@ and the
occurrences inside its own unfolding share one identity: building one lazy
entry per reachable identity ties exactly the knots the automaton has.

Equality constraints are not counted. They correlate an edge's children, so
the edge's count stops being the product of theirs and becomes the size of
an intersection; an automaton carrying them is rejected rather than
miscounted.
-}
module Data.ECTA.Gen.Internal.Automaton (automatonIndex) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.ECTA (Node, edgeChildren, edgeSymbol, nodeEdges)
import Data.ECTA.Internal.ECTA.Type (Edge, edgeEcs, freeVars, nodeIdentity)
import Data.ECTA.Paths (constraintsAreContradictory, unsafeGetEclasses)
import Data.ECTA.Term (Term (Term))

import Data.ECTA.Gen.Internal (ECTAGenError (..))
import Data.ECTA.Gen.Internal.Size (
    SizeIndex,
    choiceIndex,
    constantIndex,
    mapIndex,
    productIndex,
 )

{- | Count and index the terms an automaton accepts, by size.

Fails on an automaton with free recursive variables, which is not a closed
language, and on one whose edges carry equality constraints.
-}
automatonIndex :: Node -> Either ECTAGenError (SizeIndex Term)
automatonIndex root
    | not $ Set.null $ freeVars root = Left OpenAutomaton
    | any constrained $ concatMap nodeEdges reachable = Left CannotCountConstrainedEdges
    | otherwise = Right $ indexOf root
  where
    reachable = collect Map.empty [root]
    collect seen [] = Map.elems seen
    collect seen (node : rest)
        | null edges = collect seen rest
        | Map.member (nodeIdentity node) seen = collect seen rest
        | otherwise =
            collect
                (Map.insert (nodeIdentity node) node seen)
                (concatMap edgeChildren edges <> rest)
      where
        edges = nodeEdges node

    -- One lazy entry per reachable identity, referring to each other: a
    -- recursive automaton becomes a recursive index with no extra work.
    table = Map.fromList [(nodeIdentity node, nodeIndex node) | node <- reachable]
    nodeIndex node = choiceIndex $ map edgeIndex $ nodeEdges node

    indexOf node = case nodeEdges node of
        [] -> emptyIndex
        _ -> Map.findWithDefault emptyIndex (nodeIdentity node) table
    emptyIndex = choiceIndex []

    -- The symbol contributes the one choice that makes a term node count
    -- toward size; children are consumed left to right into its arguments.
    edgeIndex edge =
        mapIndex ($ []) $
            foldl
                consumeChild
                (constantIndex $ Term $ edgeSymbol edge)
                (map indexOf $ edgeChildren edge)
    consumeChild built child = productIndex (mapIndex prepend built) child
    prepend build term arguments = build (term : arguments)

-- | Whether an edge carries equality constraints.
constrained :: Edge -> Bool
constrained edge =
    constraintsAreContradictory constraints
        || not (null $ unsafeGetEclasses constraints)
  where
    constraints = edgeEcs edge
