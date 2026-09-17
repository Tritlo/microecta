-- | Process-global families of caches, separated by their runtime types.
module Data.CacheFamily (CacheFamily, newCacheFamily, selectCache) where

import Control.Applicative ((<|>))
import Data.Dynamic (Dynamic, fromDynamic, toDyn)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (Typeable)

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
    findCache [] = Nothing
    findCache (entry : rest) = fromDynamic entry <|> findCache rest
