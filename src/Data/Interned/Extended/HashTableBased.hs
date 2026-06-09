{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Interned.Extended.HashTableBased (
    Id,
    Cache (..),
    freshCache,
    cacheSize,
    resetCache,
    Interned (..),
    intern,
) where

import qualified Data.HashTable.IO as HT
import Data.Hashable
import Data.IORef
import GHC.IO (unsafeDupablePerformIO)

import Data.HashTable.Extended

type Id = Int

{- | Tried using the BasicHashtable size function to remove need for this IORef
(see https://github.com/gregorycollins/hashtables/pull/68), but it was slower.
-}
data Cache t = Cache
    { fresh :: !(IORef Id)
    , content :: !(HT.CuckooHashTable (Description t) t)
    }

freshCache :: IO (Cache t)
freshCache =
    Cache
        <$> newIORef 0
        <*> HT.new

cacheSize :: Cache t -> IO Int
cacheSize Cache{fresh = refI} = readIORef refI

resetCache :: (Interned t) => Cache t -> IO ()
resetCache Cache{fresh = refI, content = ht} = do
    writeIORef refI 0
    resetHashTable (AnyHashTable ht)

class
    ( Eq (Description t)
    , Hashable (Description t)
    ) =>
    Interned t
    where
    data Description t
    type Uninterned t
    describe :: Uninterned t -> Description t
    identify :: Id -> Uninterned t -> t
    cache :: Cache t

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
