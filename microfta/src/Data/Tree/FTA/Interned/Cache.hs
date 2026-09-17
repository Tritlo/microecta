{- | Interning tables and process-global cache families.

Interning is backed by immutable hash maps in 'IORef's.

Interning is safe from any thread. Lookups read the current map without
blocking. Inserts use 'atomicModifyIORef'' and retain an existing entry, then
re-read the map and return the winner, so one structure keeps one 'Id' however
many threads raced for it.

The candidate value is kept lazy during the atomic update. This matters for
recursive nodes: forcing the candidate builds its body, which may intern more
nodes. The structural shape used as the key has already been computed before
the update, so neither hashing nor collision checks need to force the
candidate.

'unsafeDupablePerformIO' may run an insertion more than once. Duplicate runs
can consume unused ids, but the atomic update and final read make them converge
on the same canonical value.

The cache never evicts and holds every distinct value ever interned, so it
grows with the size of that set and is never released. See the memory section
of the package README.
-}
module Data.Tree.FTA.Interned.Cache (
    Id,
    Cache,
    freshCacheWith,
    insertKeepingFirst,
    intern,
    CacheFamily,
    newCacheFamily,
    selectCache,
) where

import Data.Dynamic (Dynamic, fromDynamic, toDyn)
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Hashable
import Data.IORef
import Data.Maybe (fromMaybe, listToMaybe, mapMaybe)
import GHC.IO (unsafeDupablePerformIO)
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (Typeable)

-- | Dense identity assigned to each interned value.
type Id = Int

-- | The interning table for one type, plus the counter that names new entries.
data Cache key value = Cache
    { fresh :: !(IORef Id)
    -- ^ Next id to allocate. Ids of values that lose an insert race go unused.
    , content :: !(IORef (HashMap key value))
    -- ^ Map from uninterned keys to canonical interned values.
    }

-- | Allocate a typed cache that uses a shared identity counter.
freshCacheWith :: IORef Id -> IO (Cache key value)
freshCacheWith ids = Cache ids <$> newIORef HashMap.empty

{- | Insert a value unless the key is present, and return the stored value.

The first writer wins and nothing forces the value: forcing it may build a
value that interns or memoizes, which would re-enter this update and
diverge. The winner is read back outside the update. The pragma matters:
callers lose their specialization when this is a separate function.
-}
insertKeepingFirst :: (Hashable key) => IORef (HashMap key value) -> key -> value -> IO value
{-# INLINE insertKeepingFirst #-}
insertKeepingFirst ref key value = do
    existing <- HashMap.lookup key <$> readIORef ref
    case existing of
        Just found -> pure found
        Nothing -> do
            atomicModifyIORef' ref $ \table -> (HashMap.insertWith (\_new old -> old) key value table, ())
            fromMaybe value . HashMap.lookup key <$> readIORef ref

{- | Return the canonical interned representative for an uninterned value.

The uninterned value is the cache key. The identify function attaches a fresh
identity when the value is new.
-}
intern :: (Hashable key) => Cache key value -> (Id -> key -> value) -> key -> value
{-# INLINEABLE intern #-}
intern cache identify !key = unsafeDupablePerformIO $ do
    existing <- HashMap.lookup key <$> readIORef (content cache)
    case existing of
        Just found -> return found
        Nothing -> do
            i <- atomicModifyIORef' (fresh cache) (\next -> (next + 1, next))
            insertKeepingFirst (content cache) key (identify i key)

-- | A small set of typed caches. Each family belongs to one operation.
newtype CacheFamily = CacheFamily (IORef [Dynamic])

-- | Allocate an empty family.
newCacheFamily :: IO CacheFamily
newCacheFamily = CacheFamily <$> newIORef []

-- | Get the cache for one type. Concurrent allocations keep the first cache.
selectCache :: forall cache. (Typeable cache) => CacheFamily -> IO cache -> cache
{-# NOINLINE selectCache #-}
selectCache (CacheFamily ref) allocate = unsafePerformIO $ do
    existing <- findCache <$> readIORef ref
    case existing of
        Just found -> pure found
        Nothing -> do
            candidate <- allocate
            atomicModifyIORef' ref $ \entries -> case findCache entries of
                Just found -> (entries, found)
                Nothing -> (toDyn candidate : entries, candidate)
  where
    findCache = listToMaybe . mapMaybe fromDynamic
