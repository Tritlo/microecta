-- | Process-global families of caches, separated by their runtime types.
module Data.CacheFamily (CacheFamily, newCacheFamily, selectCache) where

import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import Data.Type.Equality ((:~~:) (HRefl))
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (TypeRep, Typeable, eqTypeRep, typeRep)

-- | A small set of typed caches. Each family belongs to one operation.
newtype CacheFamily = CacheFamily (IORef [SomeCache])

-- | One cache and the type needed to retrieve it safely.
data SomeCache where
    SomeCache :: TypeRep cache -> cache -> SomeCache

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
                Nothing -> (SomeCache wanted candidate : entries, candidate)
  where
    wanted = typeRep @cache
    findCache [] = Nothing
    findCache (SomeCache actual value : rest) = case eqTypeRep wanted actual of
        Just HRefl -> Just value
        Nothing -> findCache rest
