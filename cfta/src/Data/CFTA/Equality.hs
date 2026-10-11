{- | Equality-constrained finite tree automata.

Import this module to use equality-constrained automata.

A @Node symbol@ represents a set of accepted terms. Each outgoing @Edge@ is one
alternative: it has a symbol, child nodes, and a 'Constraint', here the path
equalities over its children ('equalityConstraint'). The representation and
the graph operations are those of the shared interned automaton. This module
adds equality interpretation, path reduction, and constrained enumeration.

The alphabet is a type parameter. Constructing an edge requires
@Hashable symbol@ and @Typeable symbol@, so its symbol can be hash-consed in a
type-safe cache. Building a node from existing edges needs only @Typeable@ for
the symbol; operations that rebuild edges require both. Field accessors such as
'edgeSymbol' are unconstrained. Reading the edges of a node with 'nodeEdges'
needs the same constraints as an edge, because it unfolds @Mu@. Pure
term/template matching needs only 'Eq'. The provided 'Data.CFTA.Symbol.Symbol'
type is an interned text alphabet with a 'Data.String.IsString' instance, so
existing @OverloadedStrings@ code keeps working.

The usual workflow is:

1. Build nodes with @Node@, @Edge@, and 'mkEdge'.
2. Combine nodes with 'union' and 'intersect'.
3. Propagate equality constraints with 'reducePartially'.
4. Remove implied alternatives with 'withoutRedundantEdges'.
5. Check concrete membership with 'accepts', or restrict a language
   with 'termsMatching'.
6. Enumerate accepted terms with 'terms' or 'termsPrune'.

'termsPrune' calls an oracle two times for each UVar that it expands: with
@Right node@ before the expansion, and with @Left fragment@ after it. The
oracle returns 'True' to remove the branch. The Haddock of 'termsPrune' shows
how to park a check on a hole. 'termsPruneWith' takes the recursion symbol as
an argument, and it lets the oracle select the next hole.

A node is a set of alternatives, and enumeration reads them back:

>>> let choices = Node [Edge "a" [], Edge "b" []] :: Node Symbol
>>> terms choices
[Node "a" [],Node "b" []]

'intersect' keeps what both accept:

>>> let other = Node [Edge "b" [], Edge "c" []] :: Node Symbol
>>> terms (intersect choices other)
[Node "b" []]

An equality constraint ties two positions together, which is what an ECTA has
that an ordinary tree automaton does not:

>>> let alts = Node [Edge "a" [], Edge "b" []] :: Node Symbol
>>> terms (Node [mkEdge "p" [alts, alts] (equalityConstraint $ mkEqConstraints [[path [0], path [1]]])])
[Node "p" [Node "a" [],Node "a" []],Node "p" [Node "b" [],Node "b" []]]

Templates restrict that language without discarding its constraints. Here the
right child fixes the hole on the left because the edge requires equality:

>>> let pairs = Node [mkEdge "pair" [alts, alts] (equalityConstraint $ mkEqConstraints [[path [0], path [1]]])]
>>> let rightIsA = TemplateNode "pair" [Hole, TemplateNode "a" []]
>>> terms (termsMatching rightIsA pairs)
[Node "pair" [Node "a" [],Node "a" []]]

An algebraic datatype works as the alphabet too; no string conversion is
involved. 'termsWith' takes the symbol to use if enumeration truncates at
recursion:

>>> data NatSymbol = Zero | Succ | Recursion deriving (Eq, Ord, Generic, Show)
>>> instance Hashable NatSymbol
>>> let zeroOrOne = Node [Edge Zero [], Edge Succ [Node [Edge Zero []]]] :: Node NatSymbol
>>> termsWith Recursion zeroOrOne
[Node Zero [],Node Succ [Node Zero []]]

Recursive automata are represented with 'createMu'. Internally nodes and edges
are hash-consed, so equality and memoized operations can use compact identities
instead of repeatedly traversing the same graph.

Build ECTAs from any thread. The hash-consing and memo tables behind that
sharing are process-global, and each is an immutable map in an @IORef@ read
without blocking and updated atomically. Losing a race costs a recomputation
and nothing else, because the values are pure.

Those tables also never evict. Memory grows with the number of distinct nodes,
edges and symbols ever built. The memo tables also keep one entry for each
distinct argument of each memoized operation that ran over them. The memory is
never released, so a long-lived process that keeps constructing unrelated automata
will grow without bound. The package README quantifies this.
-}
module Data.CFTA.Equality (
    -- * Automata
    module Data.CFTA.Interned,

    -- * Paths and path equalities
    module Data.CFTA.Path,
    module Data.CFTA.Equality.Constraint,

    -- * Equality operations
    module Data.CFTA.Equality.Operations,

    -- * Templates
    module Data.CFTA.Template,

    -- * Enumeration

    {- |
    Enumeration stops at recursion. Unfold first to see past it:

    >>> let nat = createMu (\r -> Node [Edge "z" [], Edge "s" [r]]) :: Node Symbol
    >>> terms nat
    [Node "Mu" []]
    >>> terms (unfoldBounded 2 nat)
    [Node "z" [],Node "s" [Node "z" []]]
    -}
    module Data.CFTA.Enumeration,
    UVar,
    uvarToInt,
) where

import Data.CFTA.Enumeration
import Data.CFTA.Equality.Constraint
import Data.CFTA.Equality.Operations
import Data.CFTA.Internal.UnionFind (UVar, uvarToInt)
import Data.CFTA.Interned
import Data.CFTA.Path
import Data.CFTA.Template

{- $setup
>>> :set -XDeriveGeneric -XOverloadedStrings
>>> import Data.Hashable (Hashable)
>>> import Data.CFTA.Equality.Constraint
>>> import Data.CFTA.Symbol
>>> import GHC.Generics (Generic)
-}
