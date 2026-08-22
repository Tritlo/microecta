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
5. Check concrete or template membership with 'nodeRepresents' or
   'nodeRepresentsTemplate'.
6. Enumerate accepted terms with 'getAllTerms' or 'getAllTermsPrune'.

A pruning oracle passed to 'getAllTermsPrune' sees each UVar twice: as
@Right node@ before the node is expanded, and as @Left fragment@ after. It
carries its own state down each branch, so a check that cannot be settled
while a hole is still unexpanded can be parked in that state under the hole's
'getUVarRepresentative' and settled when the oracle is called for that UVar.
'getAllTermsPruneWith' additionally lets the oracle say which hole it would
like expanded next, so a parked check resolves before the branch it will kill
is enumerated. Deciding which terms are worth rejecting is entirely the
oracle's business; this module supplies only the callbacks,
'expandPartialTermFrag' to read a partial term, and 'nodeRepresentsTemplate'
to test a node.

Recursive automata are represented with 'createMu'. Internally nodes and edges
are hash-consed, so equality and memoized operations can use compact identities
instead of repeatedly traversing the same graph.

Build ECTAs from one thread. The hash-consing and memo tables behind that
sharing are process-global and unsynchronized, so concurrently constructing
nodes or forcing new memoized operations can hand back structurally equal
values that compare unequal. Reading values that already exist is ordinary
pure code and is safe from any thread.
-}
module Data.ECTA (
    Edge (Edge),
    mkEdge,
    edgeChildren,
    edgeEcs,
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
    dropEdgeConstraints,
    dropConstraints,

    -- * Membership
    nodeRepresents,
    edgeRepresents,
    nodeRepresentsTemplate,
    edgeRepresentsTemplate,

    -- * Enumeration
    EnumerateM,
    runEnumerateM,
    TermFragment (..),
    enumerateFully,
    getAllTerms,
    getAllTermsPrune,
    getAllTruncatedTerms,

    -- * Pruning oracles
    UVar,
    uvarToInt,
    getUVarRepresentative,
    expandPartialTermFrag,
    getAllTermsPruneWith,
    ExpansionOrder,
    noExpansionPreference,
) where

import Data.ECTA.Internal.ECTA.Enumeration
import Data.ECTA.Internal.ECTA.Operations
import Data.ECTA.Internal.ECTA.Type
import Data.Persistent.UnionFind (UVar, uvarToInt)
