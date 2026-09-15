{- | Counting and indexing the terms an ECTA accepts.

A node's language is the union over its edges, and an edge's language is the
product of its children under its symbol. That is the same shape the
generator combinators build, so an automaton becomes a size index by
translation: @choiceIndex@ per node, @productIndex@ per edge child, and a
size-one @constantIndex@ for the symbol itself, which makes a member's size
its number of term nodes.

Recursion needs no special case. Nodes are interned, so a @Mu@ and the
occurrences inside its own unfolding share one identity: building one lazy
entry per reachable identity ties exactly the knots the automaton has.

Equality constraints are not counted. They correlate an edge's children, so
the edge's count stops being the product of theirs and becomes the size of
an intersection; an automaton carrying them is rejected rather than
miscounted.

Ambiguity is not counted either. The union over a node's edges counts
accepting runs, so a node with two edges that accept a common term counts that
term twice; such an automaton is rejected rather than miscounted.
-}
module Data.ECTA.Gen.Internal.Automaton (automatonIndex) where

import Data.List (tails)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.ECTA (Edge, Node, edgeChildren, edgeEcs, edgeSymbol, intersect, nodeEdges)
import Data.ECTA.Internal.ECTA.Type (freeVars, nodeIdentity)
import Data.ECTA.Paths (EqConstraints (EmptyConstraints))
import Data.ECTA.Term (Symbol, Term)

import Data.ECTA.Gen.Internal (ECTAGenError (..))
import qualified Data.Tree.FTA as FTA
import qualified Data.Tree.FTA.Gen.Internal.Automaton as Ordinary
import Data.Tree.Gen.Internal.Size (SizeIndex)

{- | Count and index the terms an automaton accepts, by size.

Fails on an automaton with free recursive variables, which is not a closed
language, on one whose edges carry equality constraints, and on an ambiguous
one, whose runs outnumber its terms.
-}
automatonIndex :: Node Symbol -> Either ECTAGenError (SizeIndex (Term Symbol))
automatonIndex root
    | not $ Set.null $ freeVars root = Left OpenAutomaton
    | any (any constrained . nodeEdges) reachable = Left CannotCountConstrainedEdges
    | any ambiguous reachable = Left AmbiguousAutomaton
    | otherwise = Right $ Ordinary.tableIndex (stateOf root) (ordinaryRows reachable)
  where
    reachable = reachableNodes root

-- | Name an ordinary node or the empty language without forcing its identity.
stateOf :: Node Symbol -> Maybe Int
stateOf node
    | null (nodeEdges node) = Nothing
    | otherwise = Just $ nodeIdentity node

-- | Expose the validated unconstrained rows to the common index compiler.
ordinaryRows :: [Node Symbol] -> Map.Map (Maybe Int) [FTA.Transition (Maybe Int) Symbol ()]
ordinaryRows nodes = Map.fromList [(stateOf node, map transition $ nodeEdges node) | node <- nodes]
  where
    transition edge = FTA.Transition (edgeSymbol edge) (map stateOf $ edgeChildren edge) ()

-- | Every node reachable from a root, one per interned identity.
reachableNodes :: Node Symbol -> [Node Symbol]
reachableNodes root = collect Map.empty [root]
  where
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

-- | Whether a node accepts any term at all.
productive :: Node Symbol -> Bool
productive node
    | null (nodeEdges node) = False
    | otherwise = Map.member (stateOf node) $ Ordinary.minimumSizes $ ordinaryRows $ reachableNodes node

{- | Whether a node has two edges that accept a common term.

The edges here carry no equality constraints, so two edges with the same
symbol and arity share a term exactly when every child position does, and a
child position shares one exactly when the intersection of the two children
is productive.
-}
ambiguous :: Node Symbol -> Bool
ambiguous node =
    or
        [ overlapping left right
        | left : rest <- tails $ nodeEdges node
        , right <- rest
        ]
  where
    overlapping left right =
        edgeSymbol left == edgeSymbol right
            && length (edgeChildren left) == length (edgeChildren right)
            && and
                ( zipWith
                    (\l r -> productive $ intersect l r)
                    (edgeChildren left)
                    (edgeChildren right)
                )

-- | Whether an edge carries equality constraints.
constrained :: Edge Symbol -> Bool
constrained edge = case edgeEcs edge of
    EmptyConstraints -> False
    _ -> True
