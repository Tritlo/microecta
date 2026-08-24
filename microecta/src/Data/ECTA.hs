{- | Equality-constrained finite tree automata.

This is the main public API for the ECTA core.

A @Node symbol@ represents a set of accepted terms. Each outgoing @Edge@ is one
alternative: it has a symbol, child nodes, and optional equality constraints
over paths into those children. @microecta@ keeps the original ECTA algorithms
for intersection, reduction, refolding, and enumeration, but leaves out the
larger application layers from @ecta@.

The alphabet is a type parameter. Constructing an edge requires
@Hashable symbol@ and @Typeable symbol@ so its symbol can be hash-consed in a
type-safe cache. Building a node from existing edges needs only @Typeable@;
operations that rebuild edges require both constraints. Inspection is
unconstrained, and pure term/template matching needs only 'Eq'. The provided
'Data.ECTA.Term.Symbol' type is an interned text alphabet with a
'Data.String.IsString' instance, so existing @OverloadedStrings@ code keeps
working.

The usual workflow is:

1. Build nodes with @Node@, @Edge@, and 'mkEdge'.
2. Combine nodes with 'union' and 'intersect'.
3. Propagate equality constraints with 'reducePartially'.
4. Remove implied alternatives with 'withoutRedundantEdges'.
5. Check concrete membership with 'nodeRepresents', or restrict a language
   with 'termsMatching'.
6. Enumerate accepted terms with 'getAllTerms' or 'getAllTermsPrune'.

A pruning oracle passed to 'getAllTermsPrune' sees each UVar that is actually
expanded twice: as @Right node@ before expansion, and as @Left fragment@
after. A bare unconstrained 'Mu' terminates enumeration without being expanded
and therefore produces neither callback. The oracle carries its own state down
each branch, so a check that cannot be settled while a hole is still
unexpanded can be parked in that state under the hole's
'getUVarRepresentative' and settled when the oracle is called for that UVar.
'getAllTermsPruneWith' additionally lets the oracle say which hole it would
like expanded next, so a parked check resolves before the branch it will kill
is enumerated. Deciding which terms are worth rejecting is entirely the
oracle's business; this module supplies only the callbacks and
'expandPartialTermFrag' to read a partial term. Its 'PartialSymbol' result
keeps concrete symbols, unexpanded variables, and truncated recursion
structurally distinct.

A node is a set of alternatives, and enumeration reads them back:

>>> let choices = Node [Edge "a" [], Edge "b" []] :: Node Symbol
>>> getAllTerms choices
[Term "a" [],Term "b" []]

'intersect' keeps what both accept:

>>> let other = Node [Edge "b" [], Edge "c" []] :: Node Symbol
>>> getAllTerms (intersect choices other)
[Term "b" []]

An equality constraint ties two positions together, which is what an ECTA has
that an ordinary tree automaton does not:

>>> let alts = Node [Edge "a" [], Edge "b" []] :: Node Symbol
>>> getAllTerms (Node [mkEdge "p" [alts, alts] (mkEqConstraints [[path [0], path [1]]])])
[Term "p" [Term "a" [],Term "a" []],Term "p" [Term "b" [],Term "b" []]]

Templates restrict that language without discarding its constraints. Here the
right child fixes the hole on the left because the edge requires equality:

>>> let pairs = Node [mkEdge "pair" [alts, alts] (mkEqConstraints [[path [0], path [1]]])]
>>> let rightIsA = TemplateNode "pair" [Hole, TemplateNode "a" []]
>>> getAllTerms (termsMatching rightIsA pairs)
[Term "pair" [Term "a" [],Term "a" []]]

An algebraic datatype works as the alphabet too; no string conversion is
involved. 'getAllTermsWith' takes the symbol to use if enumeration truncates at
recursion:

>>> data NatSymbol = Zero | Succ | Recursion deriving (Eq, Generic, Show)
>>> instance Hashable NatSymbol
>>> let zeroOrOne = Node [Edge Zero [], Edge Succ [Node [Edge Zero []]]]
>>> getAllTermsWith Recursion zeroOrOne
[Term Zero [],Term Succ [Term Zero []]]

Recursive automata are represented with 'createMu'. Internally nodes and edges
are hash-consed, so equality and memoized operations can use compact identities
instead of repeatedly traversing the same graph.

Build ECTAs from any thread. The hash-consing and memo tables behind that
sharing are process-global, and each is an immutable map in an @IORef@ read
without blocking and updated atomically. Losing a race costs a recomputation
and nothing else, because the values are pure.

Those tables also never evict. Memory grows with the number of distinct nodes,
edges and symbols ever built -- not with the work done on them -- and is never
released, so a long-lived process that keeps constructing unrelated automata
will grow without bound. The package README quantifies this.
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

    -- * Concrete membership
    nodeRepresents,
    edgeRepresents,

    -- * Templates
    Template (..),
    matchesTemplate,
    termsMatching,

    -- * Enumeration

    {- |
    Enumeration stops at recursion. Unfold first to see past it:

    >>> let nat = createMu (\r -> Node [Edge "z" [], Edge "s" [r]]) :: Node Symbol
    >>> getAllTerms nat
    [Term "Mu" []]
    >>> getAllTerms (unfoldBounded 2 nat)
    [Term "z" [],Term "s" [Term "z" []]]
    -}
    EnumerateM,
    runEnumerateM,
    TermFragment (..),
    PartialSymbol (..),
    enumerateFully,
    getAllTerms,
    getAllTermsWith,
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
import Data.ECTA.Template
import Data.Persistent.UnionFind (UVar, uvarToInt)

{- $setup
>>> :set -XDeriveGeneric -XOverloadedStrings
>>> import Data.Hashable (Hashable)
>>> import Data.ECTA.Paths
>>> import Data.ECTA.Term
>>> import GHC.Generics (Generic)
-}
