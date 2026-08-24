{- | Tiny hash-consing abstraction backed by immutable hash maps in 'IORef's.

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
module Data.Interned.Extended.HashTableBased (
    Id,
    Cache (..),
    freshCache,
    freshCachePair,
    Interned (..),
    intern,
) where

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Hashable
import Data.IORef
import Data.Maybe (fromMaybe)
import GHC.IO (unsafeDupablePerformIO)

-- | Dense identity assigned to each interned value.
type Id = Int

-- | The interning table for one type, plus the counter that names new entries.
data Cache t = Cache
    { fresh :: !(IORef Id)
    -- ^ Next id to allocate. Ids of values that lose an insert race go unused.
    , content :: !(IORef (HashMap (Description t) t))
    -- ^ Map from structural descriptions to canonical interned values.
    }

-- | Allocate an empty interning cache.
freshCache :: IO (Cache t)
freshCache =
    Cache
        <$> newIORef 0
        <*> newIORef HashMap.empty

{- | Allocate two empty caches that draw identities from one counter.

Use this when one logical interned type has separate fast-path and fallback
tables: their contents need not mix, but their public identities must remain
globally distinct.
-}
freshCachePair :: IO (Cache left, Cache right)
freshCachePair = do
    ids <- newIORef 0
    left <- Cache ids <$> newIORef HashMap.empty
    right <- Cache ids <$> newIORef HashMap.empty
    return (left, right)

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
intern :: forall t. (Interned t) => Uninterned t -> t
intern !bt = unsafeDupablePerformIO $ do
    existing <- HashMap.lookup dt <$> readIORef (content c)
    case existing of
        Just t -> return t
        Nothing -> do
            i <- atomicModifyIORef' (fresh c) (\next -> (next + 1, next))
            let t = identify i bt
            -- insertWith keeps whatever is already there, so the first writer
            -- wins and nothing forces @t@: forcing it builds the value, which
            -- interns, which would re-enter this update and diverge.
            atomicModifyIORef' (content c) $ \m ->
                (HashMap.insertWith (\_new old -> old) dt t m, ())
            -- Re-read outside the update to pick up whoever won.
            fromMaybe t . HashMap.lookup dt <$> readIORef (content c)
  where
    c = cache :: Cache t
    !dt = describe bt
