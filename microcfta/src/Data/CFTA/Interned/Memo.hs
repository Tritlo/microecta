{-# LANGUAGE AllowAmbiguousTypes #-}

{- | Quick-and-dirty hash-based memoization.

The shared automaton engine uses stable global memo tables for interning and recursive
graph operations. 'memo' is convenient when the memoized function is a
monomorphic top-level value. Polymorphic functions should allocate an explicit
'MemoCache' or 'TypeableMemoCache' once and use the corresponding @With@
operation, so typeclass dictionaries cannot accidentally turn the table into a
per-call allocation.

Safe from any thread. The table is a 'Table' of immutable maps in @IORef@s,
read without blocking and updated with 'atomicModifyIORef''. Two racers may
install different thunks and return their own result, but both compute the same answer
because every function memoized here is pure.

The lazy map is important: an atomic update installs the result thunk without
forcing the memoized computation. That computation may itself intern or call
other memoized functions, so it must run outside the update.

The tables never evict, so a memoized function retains an entry for every
distinct argument it has ever been applied to, for the lifetime of the process.
That is what makes repeated work free, and it means memory grows with the
number of distinct inputs rather than with the work done. See the memory
section of the package README.
-}
module Data.CFTA.Interned.Memo (
    MemoCache,
    TypeableMemoCache,
    newMemoCache,
    newTypeableMemoCache,
    memo,
    memo2,
    memoWith,
    memo2With,
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
distinct first argument, before storing a single entry. One table keyed by the
pair costs the same time on the core benchmark.
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

-- | Binary variant of 'memoWith', using one table keyed by the pair.
memo2With :: (Hashable a, Hashable b) => MemoCache (a, b) c -> (a -> b -> c) -> a -> b -> c
{-# INLINE memo2With #-}
memo2With cache f = curry (memoWith cache (uncurry f))

{- | A family of memo tables for one function.

Each symbol and constraint type has its own table, and these two types must
determine the function's argument and result types. Individual entries
contain ordinary typed keys and values.
-}
newtype TypeableMemoCache = TypeableMemoCache CacheFamily

-- | Allocate an empty memo-table family.
newTypeableMemoCache :: IO TypeableMemoCache
newTypeableMemoCache = TypeableMemoCache <$> newCacheFamily

-- | Memoize one application in the table for the symbol and constraint types.
memoTypeableWith ::
    forall symbol constraint a b.
    (Hashable a, Typeable symbol, Typeable constraint) =>
    TypeableMemoCache ->
    (a -> b) ->
    a ->
    b
{-# INLINE memoTypeableWith #-}
memoTypeableWith (TypeableMemoCache family) =
    memoWith (selectCache @symbol @constraint family (newMemoCache @a @b))

-- | Binary variant of 'memoTypeableWith', keyed by the argument pair.
memo2TypeableWith ::
    forall symbol constraint a b c.
    (Hashable a, Hashable b, Typeable symbol, Typeable constraint) =>
    TypeableMemoCache ->
    (a -> b -> c) ->
    a ->
    b ->
    c
memo2TypeableWith cache f = curry (memoTypeableWith @symbol @constraint cache (uncurry f))
