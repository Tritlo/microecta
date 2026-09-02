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
import Data.ECTA.Term (Symbol, Term (Term))

import Data.ECTA.Gen.Internal (ECTAGenError (..))
import Data.ECTA.Gen.Internal.Size (
    SizeIndex,
    choiceIndex,
    constantIndex,
    mapIndex,
    productIndex,
    withMinimumMemberSize,
 )

{- | Count and index the terms an automaton accepts, by size.

Fails on an automaton with free recursive variables, which is not a closed
language, on one whose edges carry equality constraints, and on an ambiguous
one, whose runs outnumber its terms.
-}
automatonIndex :: Node Symbol -> Either ECTAGenError (SizeIndex (Term Symbol))
automatonIndex root
    | not $ Set.null $ freeVars root = Left OpenAutomaton
    | any constrained $ concatMap nodeEdges reachable = Left CannotCountConstrainedEdges
    | any ambiguous reachable = Left AmbiguousAutomaton
    | otherwise = Right $ indexOf root
  where
    reachable = reachableNodes root

    -- One lazy entry per reachable identity, referring to each other: a
    -- recursive automaton becomes a recursive index with no extra work.
    table = Map.fromList [(nodeIdentity node, nodeIndex node) | node <- reachable]
    nodeIndex node =
        withMinimumMemberSize
            (Map.lookup (nodeIdentity node) minima)
            (choiceIndex $ map edgeIndex $ nodeEdges node)

    -- A node with no minimum size accepts nothing, and its table entry counts
    -- an unbounded run of zeroes that 'sizeClassOf' would walk forever. The
    -- empty index counts nothing at all, so every product or choice over it
    -- stays finite.
    indexOf node
        | null (nodeEdges node) = emptyIndex
        | Map.member (nodeIdentity node) minima =
            Map.findWithDefault emptyIndex (nodeIdentity node) table
        | otherwise = emptyIndex
    emptyIndex = choiceIndex []

    minima = minimumSizes reachable

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

{- | The size of the shortest term each node accepts, by interned identity.

Solved independently of the lazy count knot. Starting with no productive
nodes and adding known minima is the least fixed point, so a cycle without a
base remains absent, and an absent node is one that accepts nothing.
-}
minimumSizes :: [Node Symbol] -> Map.Map Int Int
minimumSizes nodes = converge Map.empty
  where
    converge current =
        let next = foldr addMinimum current nodes
         in if next == current then current else converge next

    addMinimum node known = case nodeMinimum known node of
        Nothing -> known
        Just size -> Map.insertWith min (nodeIdentity node) size known

    nodeMinimum known node = minimumOf $ map (edgeMinimum known) $ nodeEdges node
    edgeMinimum known edge =
        (1 +) . sum
            <$> traverse
                (\child -> Map.lookup (nodeIdentity child) known)
                (edgeChildren edge)

    minimumOf sizes = case [size | Just size <- sizes] of
        [] -> Nothing
        liveSizes -> Just $ minimum liveSizes

-- | Whether a node accepts any term at all.
productive :: Node Symbol -> Bool
productive node
    | null (nodeEdges node) = False
    | otherwise = Map.member (nodeIdentity node) $ minimumSizes $ reachableNodes node

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
