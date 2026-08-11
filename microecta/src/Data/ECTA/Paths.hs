{- | Paths and equality constraints used by ECTA edges.

Paths are lists of child indexes. For example, @path [1,0]@ means "the first
child of the second child" of an edge. Equality constraints group paths that
must denote equal subterms whenever an edge is used.

Most users only need 'path', 'mkEqConstraints', 'EmptyConstraints', and the
query helpers. The trie and e-class types are exposed because some downstream
code inspects constraint structure directly, but they are still considered part
of the low-level ECTA machinery.
-}
module Data.ECTA.Paths (
    -- * Paths
    Path (EmptyPath, ConsPath),
    unPath,
    path,
    Pathable (..),
    pathHeadUnsafe,
    pathTailUnsafe,
    isSubpath,
    PathTrie (TerminalPathTrie),
    isEmptyPathTrie,
    isTerminalPathTrie,
    getMaxNonemptyIndex,
    toPathTrie,
    fromPathTrie,
    pathTrieDescend,
    PathEClass (getPathTrie),
    unPathEClass,
    hasSubsumingMember,
    completedSubsumptionOrdering,

    -- * Equality constraints over paths
    EqConstraints (EmptyConstraints),
    unsafeGetEclasses,
    mkEqConstraints,
    combineEqConstraints,
    eqConstraintsDescend,
    constraintsAreContradictory,
    constraintsImply,
    subsumptionOrderedEclasses,
    unsafeSubsumptionOrderedEclasses,
) where

import Data.ECTA.Internal.Paths
