{- | Equality-constrained finite tree automata.

This is the main public API for the ECTA core.

A @Node@ represents a set of accepted terms. Each outgoing @Edge@ is one
alternative: it has a symbol, child nodes, and optional equality constraints
over paths into those children. @microecta@ keeps the original ECTA algorithms
for intersection, reduction, refolding, and enumeration, but leaves out the
larger application layers from @ecta@.

The usual workflow is:

1. Build nodes with @Node@, @Edge@, and 'mkEdge'.
2. Combine nodes with 'union' and 'intersect'.
3. Propagate equality constraints with 'reducePartially'.
4. Remove implied alternatives with 'withoutRedundantEdges'.
5. Enumerate accepted terms with 'getAllTerms' or 'getAllTermsPrune'.

Recursive automata are represented with 'createMu'. Internally nodes and edges
are hash-consed, so equality and memoized operations can use compact identities
instead of repeatedly traversing the same graph.
-}
module Data.ECTA (
    Edge (Edge),
    mkEdge,
    edgeChildren,
    edgeSymbol,
    Node (Node, EmptyNode),
    nodeEdges,
    numNestedMu,
    createMu,

    -- * Operations
    nodeMapChildren,
    pathsMatching,
    mapNodes,
    refold,
    unfoldBounded,
    crush,
    onNormalNodes,
    nodeCount,
    edgeCount,
    maxIndegree,
    union,
    intersect,
    withoutRedundantEdges,
    reducePartially,

    -- * Enumeration
    EnumerateM,
    runEnumerateM,
    enumerateFully,
    getAllTerms,
    getAllTermsPrune,
    getAllTruncatedTerms,
) where

import Data.ECTA.Internal.ECTA.Enumeration
import Data.ECTA.Internal.ECTA.Operations
import Data.ECTA.Internal.ECTA.Type
