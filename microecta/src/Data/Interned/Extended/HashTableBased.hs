{- | Tiny hash-consing abstraction backed by mutable cuckoo hash tables.

Not thread-safe. The cache is a process-global mutable table read and written
through 'unsafeDupablePerformIO', so two threads interning the same value can
both miss, both allocate an 'Id', and produce two values that structurally
agree but compare unequal. Intern from one thread; reading already-constructed
values is then ordinary pure code and is safe from any thread.
-}
module Data.Interned.Extended.HashTableBased (
    Id,
    Cache (..),
    freshCache,
    Interned (..),
    intern,
) where

import qualified Data.HashTable.IO as HT
import Data.Hashable
import Data.IORef
import GHC.IO (unsafeDupablePerformIO)

-- | Dense identity assigned to each interned value.
type Id = Int

{- | The interning table for one type, plus the counter that names new entries.

The counter is a separate 'IORef' rather than the table's own size: reading
the size instead (see https://github.com/gregorycollins/hashtables/pull/68)
was measured slower.
-}
data Cache t = Cache
    { fresh :: !(IORef Id)
    -- ^ Next id to allocate.
    , content :: !(HT.CuckooHashTable (Description t) t)
    -- ^ Map from structural descriptions to canonical interned values.
    }

-- | Allocate an empty interning cache.
freshCache :: IO (Cache t)
freshCache =
    Cache
        <$> newIORef 0
        <*> HT.new

-- | Values that can be hash-consed through a global cache.
class
    ( Eq (Description t)
    , Hashable (Description t)
    ) =>
    Interned t
    where
    -- | Hashable structural representation used as the cache key.
    data Description t

    -- | Non-canonical input used to build an interned value.
    type Uninterned t

    -- | Compute the cache key for an uninterned value.
    describe :: Uninterned t -> Description t

    -- | Attach a freshly allocated identity to an uninterned value.
    identify :: Id -> Uninterned t -> t

    -- | Process-global cache for this interned type.
    cache :: Cache t

-- | Return the canonical interned representative for an uninterned value.
intern :: (Interned t) => Uninterned t -> t
intern !bt = unsafeDupablePerformIO $ do
    let c = cache
    let refI = fresh c
    let ht = content c
    v <- HT.lookup ht dt
    case v of
        Nothing -> do
            i <- atomicModifyIORef' refI (\i -> (i + 1, i))
            let t = identify i bt
            HT.insert ht dt t
            return t
        Just t -> return t
  where
    !dt = describe bt
