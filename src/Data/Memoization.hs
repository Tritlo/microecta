{-# LANGUAGE OverloadedStrings #-}

{- | Quick-and-dirty, thread-unsafe, hash-based memoization.

The ECTA core relies on stable global memo tables for interning and recursive
graph operations. This module intentionally keeps that machinery tiny: each
call to 'memo' allocates one process-global hash table through
'unsafePerformIO'.
-}
module Data.Memoization (
    MemoCacheTag (..),
    resetAllCaches,
    memoIO,
    memo,
    memo2,
) where

import qualified Data.HashTable.IO as HT
import Data.Hashable (Hashable)
import Data.Text (Text)
import GHC.Generics (Generic)
import System.IO.Unsafe (unsafePerformIO)

import Data.Text.Extended.Pretty

-- | Human-readable name for a memo table.
data MemoCacheTag
    = -- | Name a table for debugging and nested-table derivation.
      NameTag Text
    deriving (Eq, Ord, Show, Generic)

instance Hashable MemoCacheTag

mkInnerTag :: MemoCacheTag -> MemoCacheTag
mkInnerTag (NameTag t) = NameTag (t <> "-inner")

instance Pretty MemoCacheTag where
    pretty (NameTag t) = t

{- | Reset all global memo tables.

Currently a no-op: the surviving microecta memo tables are owned by each
memoized closure rather than a central registry.
-}
resetAllCaches :: IO ()
resetAllCaches = return ()

-- | Allocate an explicit IO memoizing wrapper around a pure function.
memoIO :: forall a b. (Eq a, Hashable a) => MemoCacheTag -> (a -> b) -> IO (a -> IO b)
memoIO _ f = do
    ht :: HT.CuckooHashTable a b <- HT.new
    let f' x = do
            v <- HT.lookup ht x
            case v of
                Nothing -> do
                    let r = f x
                    HT.insert ht x r
                    return r
                Just r -> return r
    return f'

-- | Memoize a pure unary function in a process-global mutable hash table.
memo :: (Eq a, Hashable a) => MemoCacheTag -> (a -> b) -> (a -> b)
memo tag f =
    let f' = unsafePerformIO (memoIO tag f)
     in \x -> unsafePerformIO (f' x)

-- | Memoize a pure binary function as nested unary memo tables.
memo2 :: (Eq a, Hashable a, Eq b, Hashable b) => MemoCacheTag -> (a -> b -> c) -> a -> b -> c
memo2 tag f = memo tag (memo (mkInnerTag tag) . f)
