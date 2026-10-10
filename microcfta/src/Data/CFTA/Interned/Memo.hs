{-# LANGUAGE AllowAmbiguousTypes #-}

{- | Hash-based memoization.

The shared automaton engine uses stable global memo tables for interning and recursive
graph operations. 'memo' is convenient when the memoized function is a
monomorphic top-level value. Polymorphic functions should allocate an explicit
'MemoCache' or 'TypeableMemoCache' once and use the corresponding @With@
operation, so typeclass dictionaries cannot accidentally turn the table into a
per-call allocation.

Safe from any thread. The table is a 'Table' of immutable maps in @IORef@s,
read without blocking and updated with 'atomicModifyIORef''. Two racers may
both compute a result. Every function memoized here is pure, so both results
are the same. The first installed thunk wins, and the other racer returns that
stored thunk. Only the computation is duplicated.

The lazy map is important: an atomic update installs the result thunk without
forcing the memoized computation. That computation may itself intern or call
other memoized functions, so it must run outside the update.

The tables never evict, so a memoized function retains an entry for every
distinct argument it has ever been applied to, for the lifetime of the process.
That avoids repeated work. It also means that memory grows with the
number of distinct inputs rather than with the work done. See the memory
section of the package README.

The tables are global for the reason that the intern tables are global. A
memoized function is a pure function of interned values, so its table changes
no result, only the time to compute it. A global table shares results between
calls: two generators that reduce one automaton reduce it once. A table that
the caller gives would make every operation monadic, and the sharing would
stop at the boundary of each call.
-}
module Data.CFTA.Interned.Memo (
    MemoCache,
    TypeableMemoCache,
    newMemoCache,
    newTypeableMemoCache,
    memo,
    memo2,
    memoWith,
    memoTypeableWith,
    memo2TypeableWith,
) where

import Data.CFTA.Interned.Cache (CacheFamily, Table, insertKeepingFirst, newCacheFamily, newTable, selectCache)
import Data.Hashable (Hashable (..))
import GHC.IO (unsafeDupablePerformIO)
import Type.Reflection (Typeable)

{- | Memoize a pure unary function in a process-global mutable hash table.

Two threads can build the memoized function at the same time, and each then
allocates a table. Either table gives the same results, because the function
is pure, so the allocation needs no protection against duplication.
-}
memo :: (Hashable a) => (a -> b) -> (a -> b)
{-# NOINLINE memo #-}
memo f = unsafeDupablePerformIO $ do
    table <- newMemoCache
    pure (memoWith table f)

{- | Memoize a pure binary function in one table keyed by the pair.

Nesting two unary tables instead would allocate a fresh hash table for every
distinct first argument, before storing a single entry. The two forms differ
by less than 0.02% in instruction count, on the core benchmark and on the
generator benchmarks.
-}
memo2 :: (Hashable a, Hashable b) => (a -> b -> c) -> a -> b -> c
memo2 f = curry (memo (uncurry f))

{- | A memo table whose argument and result types are known statically.

The table is separate from the function so polymorphic callers can keep its
lifetime explicit. Reusing one table for different functions is invalid.
-}
newtype MemoCache a b = MemoCache (Table a b)

{- | Allocate an empty statically typed memo table.

A memo table has one shard. Many memo tables serve one traversal and then
become garbage, and a table with many shards allocates one reference for each
shard.
-}
newMemoCache :: IO (MemoCache a b)
newMemoCache = MemoCache <$> newTable 0

-- | Memoize one application in an explicitly supplied table.
memoWith :: (Hashable a) => MemoCache a b -> (a -> b) -> a -> b
{-# INLINEABLE memoWith #-}
memoWith (MemoCache table) f x = unsafeDupablePerformIO $ insertKeepingFirst table x (f x)

{- | A family of memo tables for one function.

Each symbol type has its own table, and the symbol type must determine the
function's argument and result types. Individual entries
contain ordinary typed keys and values.
-}
newtype TypeableMemoCache = TypeableMemoCache CacheFamily

-- | Allocate an empty memo-table family.
newTypeableMemoCache :: IO TypeableMemoCache
newTypeableMemoCache = TypeableMemoCache <$> newCacheFamily

-- | Memoize one application in the table for the symbol type.
memoTypeableWith ::
    forall symbol a b.
    (Hashable a, Typeable symbol) =>
    TypeableMemoCache ->
    (a -> b) ->
    a ->
    b
{-# INLINE memoTypeableWith #-}
memoTypeableWith (TypeableMemoCache family) =
    memoWith (selectCache @symbol family (newMemoCache @a @b))

-- | Binary variant of 'memoTypeableWith', keyed by the argument pair.
memo2TypeableWith ::
    forall symbol a b c.
    (Hashable a, Hashable b, Typeable symbol) =>
    TypeableMemoCache ->
    (a -> b -> c) ->
    a ->
    b ->
    c
memo2TypeableWith cache f = curry (memoTypeableWith @symbol cache (uncurry f))
