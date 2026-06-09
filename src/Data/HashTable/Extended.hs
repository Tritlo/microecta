-- | Small helpers for the mutable hash tables used by memoization and interning.
module Data.HashTable.Extended (
    getKeys,
    resetHashTable,
    AnyHashTable (..),
) where

import Data.HashTable.Class (HashTable)
import qualified Data.HashTable.IO as HT
import Data.Hashable (Hashable)

------------------------------------------------------------------------------

-- | Return all keys currently present in a mutable hash table.
getKeys :: (HashTable h) => HT.IOHashTable h k v -> IO [k]
getKeys ht = HT.foldM f [] ht
  where
    f !l !(k, _) = return (k : l)

-- | Remove every entry from an existentially wrapped mutable hash table.
resetHashTable :: AnyHashTable -> IO ()
resetHashTable (AnyHashTable ht) = do
    keys <- getKeys ht
    mapM_ (\k -> HT.mutate ht k (const (Nothing, ()))) keys

-- | Existential wrapper for hash tables whose concrete key and value types are hidden.
data AnyHashTable where
    -- | Wrap a mutable hash table that can be cleared by key deletion.
    AnyHashTable :: (HashTable h, Eq k, Hashable k) => HT.IOHashTable h k v -> AnyHashTable
