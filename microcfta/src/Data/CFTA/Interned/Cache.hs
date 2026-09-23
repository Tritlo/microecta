{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

{- | Interning tables and process-global cache families.

Interning is backed by a 'Table': immutable hash maps in 'IORef's, one for
each shard of the key's hash.

Interning is safe from any thread. Lookups read the current shard without
blocking. Inserts use 'atomicModifyIORef'' and retain an existing entry, then
re-read the shard and return the winner, so one structure keeps one 'Id'
however many threads raced for it.

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
module Data.CFTA.Interned.Cache (
    Id,
    IdSupply,
    newIdSupply,
    Table,
    newTable,
    Cache,
    freshCacheWith,
    insertKeepingFirst,
    intern,
    CacheFamily,
    newCacheFamily,
    selectCache,
) where

import Control.Monad (replicateM)
import Data.Array.Byte (MutableByteArray (..))
import Data.Bits (finiteBitSize, shiftR)
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Hashable
import Data.IORef
import Data.Maybe (fromMaybe, listToMaybe)
import GHC.Arr (Array, listArray, unsafeAt)
import GHC.Exts (Any, Int (I#), RealWorld, fetchAddIntArray#, newByteArray#, writeIntArray#)
import GHC.IO (IO (IO), unsafeDupablePerformIO)
import Type.Reflection (SomeTypeRep (..), Typeable, typeRep)
import Unsafe.Coerce (unsafeCoerce)

-- | Identity assigned to each interned value. Identities are unique, not dense.
type Id = Int

{- | A supply of identities.

The supply is one counter that takes atomic fetch-and-add increments, so
threads draw distinct identities and never retry, as an 'IORef' update can.
One thread draws 0, 1, 2, and so on, in the order that it interns values. Nodes order their edges by identity, so this order makes
enumeration and sampling deterministic in a single-threaded program.
-}
newtype IdSupply = IdSupply (MutableByteArray RealWorld)

-- | Allocate a supply that starts at 0.
newIdSupply :: IO IdSupply
newIdSupply = IO $ \state -> case newByteArray# 8# state of
    (# state', counter #) -> case writeIntArray# counter 0# 0# state' of
        state'' -> (# state'', IdSupply (MutableByteArray counter) #)

-- | Draw a fresh identity.
nextId :: IdSupply -> IO Id
nextId (IdSupply (MutableByteArray counter)) = IO $ \state -> case fetchAddIntArray# counter 0# 1# state of
    (# state', previous #) -> (# state', I# previous #)

{- | A hash table split into shards by the high bits of the key's hash.

Each shard is an immutable map in an 'IORef'. A shard is a smaller tree than
one map for the whole table, so a lookup visits fewer levels and an insert
copies a shorter path. The maps index their trees by the low bits of the
hash, so the shard takes the high bits. Keys are stored with their hash, so
choosing the shard and searching it hash the key once.
-}
data Table key value = Table !Int !(Array Int (IORef (HashMap (Hashed key) value)))

-- | Allocate an empty table whose shard is chosen by the given number of hash bits.
newTable :: Int -> IO (Table key value)
newTable bits =
    Table (finiteBitSize (0 :: Word) - bits) . listArray (0, shardCount - 1)
        <$> replicateM shardCount (newIORef HashMap.empty)
  where
    shardCount = 2 ^ bits

-- | The shard that holds a key.
shardOf :: Table key value -> Hashed key -> IORef (HashMap (Hashed key) value)
{-# INLINE shardOf #-}
shardOf (Table shift shards) key =
    shards `unsafeAt` fromIntegral ((fromIntegral (hashedHash key) :: Word) `shiftR` shift)

-- | The interning table for one type, plus the counter that names new entries.
data Cache key value = Cache
    { fresh :: !IdSupply
    -- ^ Where new ids come from. Ids of values that lose an insert race go unused.
    , content :: !(Table key value)
    -- ^ Map from uninterned keys to canonical interned values.
    }

{- | Allocate a typed cache that uses a shared identity counter.

An interning table grows with every distinct value it has seen, so it has 256
shards: each shard stays a shallow tree, and threads that insert into
different shards do not retry each other's updates.
-}
freshCacheWith :: IdSupply -> IO (Cache key value)
freshCacheWith ids = Cache ids <$> newTable 8

{- | Insert a value unless the key is present, and return the stored value.

The first writer wins and nothing forces the value: forcing it may build a
value that interns or memoizes, which would re-enter this update and
diverge. The winner is read back outside the update. The pragma matters:
callers lose their specialization when this is a separate function.
-}
insertKeepingFirst :: (Hashable key) => Table key value -> key -> value -> IO value
{-# INLINE insertKeepingFirst #-}
insertKeepingFirst table key = insertHashed table (hashed key)

-- | 'insertKeepingFirst' for a key whose hash is already stored.
insertHashed :: (Eq key) => Table key value -> Hashed key -> value -> IO value
{-# INLINE insertHashed #-}
insertHashed table key value = do
    existing <- HashMap.lookup key <$> readIORef shard
    case existing of
        Just found -> pure found
        Nothing -> do
            atomicModifyIORef' shard $ \entries -> (HashMap.insertWith (\_new old -> old) key value entries, ())
            fromMaybe value . HashMap.lookup key <$> readIORef shard
  where
    shard = shardOf table key

{- | Return the canonical interned representative for an uninterned value.

The uninterned value is the cache key. The identify function attaches a fresh
identity when the value is new. The pragma matters: when 'intern' is only
inlinable, the call sites of theories other than the equality theory hash the
key through class dictionaries.
-}
intern :: (Hashable key) => Cache key value -> (Id -> key -> value) -> key -> value
{-# INLINE intern #-}
intern cache identify !key = unsafeDupablePerformIO $ do
    existing <- HashMap.lookup hashedKey <$> readIORef (shardOf (content cache) hashedKey)
    case existing of
        Just found -> return found
        Nothing -> do
            i <- nextId (fresh cache)
            insertHashed (content cache) hashedKey (identify i key)
  where
    hashedKey = hashed key

{- | A small set of caches, one for each symbol and constraint type.

A family belongs to one operation, and the symbol and constraint types
determine the type of its cache. The key is the pair of their type
representations. The caller already has both, so selecting a cache builds
no type representation and computes no fingerprint.
-}
newtype CacheFamily = CacheFamily (IORef [(SomeTypeRep, SomeTypeRep, Any)])

-- | Allocate an empty family.
newCacheFamily :: IO CacheFamily
newCacheFamily = CacheFamily <$> newIORef []

{- | Get the cache for one symbol and constraint type. Concurrent allocations
keep the first cache.

The caller guarantees that, in this family, the symbol and constraint types
determine the cache type. The stored cache is coerced back on that
guarantee. Every intern and memo call selects a cache, so the selection must
not use 'System.IO.Unsafe.unsafePerformIO': with more than one capability, its
protection against duplication walks the thread's stack on each call. A
duplicated selection is harmless, because the atomic update keeps the first
cache.
-}
selectCache ::
    forall symbol constraint cache.
    (Typeable symbol, Typeable constraint) =>
    CacheFamily ->
    IO cache ->
    cache
{-# NOINLINE selectCache #-}
selectCache (CacheFamily ref) allocate = unsafeDupablePerformIO $ do
    existing <- findCache <$> readIORef ref
    case existing of
        Just found -> pure found
        Nothing -> do
            candidate <- allocate
            atomicModifyIORef' ref $ \entries -> case findCache entries of
                Just found -> (entries, found)
                Nothing -> ((symbolKey, constraintKey, unsafeCoerce candidate) : entries, candidate)
  where
    symbolKey = SomeTypeRep (typeRep @symbol)
    constraintKey = SomeTypeRep (typeRep @constraint)
    findCache entries =
        listToMaybe
            [ unsafeCoerce cache
            | (symbolType, constraintType, cache) <- entries
            , symbolType == symbolKey
            , constraintType == constraintKey
            ]
