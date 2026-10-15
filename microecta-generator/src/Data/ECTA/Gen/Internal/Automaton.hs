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

Ranks order the edges of a node by arity, then by the text of the symbol,
then by the canonical classes of their children ('canonicalClasses'), so they
do not depend on the order in which the process interned the automaton. Edges
whose keys are equal keep the node's order, which is interning order; in an
automaton without ambiguity no two edges of a node have equal keys.
-}
module Data.ECTA.Gen.Internal.Automaton (automatonIndex) where

import qualified Data.IntMap.Strict as IntMap
import Data.List (sort, sortOn, tails)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.ECTA (Edge, Node, edgeChildren, edgeEcs, edgeSymbol, intersect, nodeEdges)
import Data.ECTA.Internal.ECTA.Type (freeVars, nodeIdentity)
import Data.ECTA.Paths (EqConstraints (EmptyConstraints))
import Data.ECTA.Term (Symbol (Symbol), Term (Term))

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
            (choiceIndex $ map edgeIndex $ sortOn edgeKey $ nodeEdges node)

    -- A node keeps its edges in interning order, which depends on what the
    -- process built before. Arity first puts the leaves of a size class
    -- before its constructors; the symbol text is stable across processes,
    -- where 'Ord' on 'Symbol' compares intern identities. The classes of the
    -- children order the edges with one arity and symbol.
    edgeKey edge = (symbolKey edge, map classOf $ edgeChildren edge)
    symbolKey edge = (length (edgeChildren edge), case edgeSymbol edge of Symbol text -> text)
    classes =
        canonicalClasses $
            IntMap.fromList
                [ (nodeIdentity node, [(symbolKey edge, map nodeIdentity $ edgeChildren edge) | edge <- nodeEdges node])
                | node <- reachable
                ]
    classOf child = IntMap.findWithDefault (-1) (nodeIdentity child) classes

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

{- | Canonical classes for the nodes of a graph, which can have cycles.

A node is a list of edges, and an edge is a key and the identities of its
children. Every node starts in one class. Each round keys a node by its class
and the sorted keys of its edges with the classes of their children, and
numbers the classes in the order of those keys. The rounds stop when no class
splits (ordered partition refinement). The classes depend on the content of
the graph only, not on the identities of its nodes. A node keeps its class
first in its key, so two nodes keep their order once a round separates them,
and the order of two nodes does not depend on the rest of the graph. Two
nodes share a class when their edges are the same up to the classes of their
children.
-}
canonicalClasses :: (Ord key) => IntMap.IntMap [(key, [Int])] -> IntMap.IntMap Int
canonicalClasses graph = refine (IntMap.map (const 0) graph) (min 1 $ IntMap.size graph)
  where
    refine classes count
        | count' == count = classes'
        | otherwise = refine classes' count'
      where
        keys =
            IntMap.mapWithKey
                ( \nodeId edges ->
                    (classes IntMap.! nodeId, sort [(key, [IntMap.findWithDefault (-1) child classes | child <- children]) | (key, children) <- edges])
                )
                graph
        numbers = Map.fromList $ zip (Set.toAscList $ Set.fromList $ IntMap.elems keys) [0 :: Int ..]
        classes' = IntMap.map (numbers Map.!) keys
        count' = Map.size numbers

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
