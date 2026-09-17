{- | Quick-and-dirty hash-based memoization.

The shared automaton engine uses stable global memo tables for interning and recursive
graph operations. 'memo' is convenient when the memoized function is a
monomorphic top-level value. Polymorphic functions should allocate an explicit
'MemoCache' or 'TypeableMemoCache' once and use the corresponding @With@
operation, so typeclass dictionaries cannot accidentally turn the table into a
per-call allocation.

Safe from any thread. The table is an immutable map in an @IORef@, read
without blocking and updated with 'atomicModifyIORef''. Two racers may install
different thunks and return their own result, but both compute the same answer
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
module Data.Tree.FTA.Interned.Memo (
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

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Hashable (Hashable (..))
import Data.IORef (IORef, newIORef)
import Data.Tree.FTA.Interned.Cache (CacheFamily, insertKeepingFirst, newCacheFamily, selectCache)
import GHC.IO (unsafeDupablePerformIO)
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (Typeable)

-- | Memoize a pure unary function in a process-global mutable hash table.
memo :: (Hashable a) => (a -> b) -> (a -> b)
{-# NOINLINE memo #-}
memo f = unsafePerformIO $ do
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
newtype MemoCache a b = MemoCache (IORef (HashMap a b))

-- | Allocate an empty statically typed memo table.
newMemoCache :: IO (MemoCache a b)
newMemoCache = MemoCache <$> newIORef HashMap.empty

-- | Memoize one application in an explicitly supplied table.
memoWith :: (Hashable a) => MemoCache a b -> (a -> b) -> a -> b
{-# INLINEABLE memoWith #-}
memoWith (MemoCache ref) f x = unsafeDupablePerformIO $ insertKeepingFirst ref x (f x)

-- | Binary variant of 'memoWith', using one table keyed by the pair.
memo2With :: (Hashable a, Hashable b) => MemoCache (a, b) c -> (a -> b -> c) -> a -> b -> c
{-# INLINE memo2With #-}
memo2With cache f = curry (memoWith cache (uncurry f))

{- | A family of typed memo tables.

Each argument and result type pair has its own table. Type checks select the
whole table. Individual entries contain ordinary typed keys and values.
A family belongs to one function.
-}
newtype TypeableMemoCache = TypeableMemoCache CacheFamily

-- | Allocate an empty memo-table family.
newTypeableMemoCache :: IO TypeableMemoCache
newTypeableMemoCache = TypeableMemoCache <$> newCacheFamily

-- | Memoize one application in the table for its argument and result types.
memoTypeableWith ::
    forall a b.
    (Hashable a, Typeable a, Typeable b) =>
    TypeableMemoCache ->
    (a -> b) ->
    a ->
    b
{-# INLINE memoTypeableWith #-}
memoTypeableWith (TypeableMemoCache family) =
    memoWith (selectCache family (newMemoCache @a @b))

-- | Binary variant of 'memoTypeableWith', keyed by the argument pair.
memo2TypeableWith ::
    (Hashable a, Hashable b, Typeable a, Typeable b, Typeable c) =>
    TypeableMemoCache ->
    (a -> b -> c) ->
    a ->
    b ->
    c
memo2TypeableWith cache f = curry (memoTypeableWith cache (uncurry f))
