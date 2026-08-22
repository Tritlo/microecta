{-# LANGUAGE OverloadedStrings #-}

{- | Quick-and-dirty, thread-unsafe, hash-based memoization.

The ECTA core relies on stable global memo tables for interning and recursive
graph operations. This module intentionally keeps that machinery tiny: each
call to 'memo' allocates one process-global hash table through
'unsafePerformIO'.
-}
module Data.Memoization (
    MemoCacheTag (..),
    memo,
    memo2,
) where

import qualified Data.HashTable.IO as HT
import Data.Hashable (Hashable (..))
import Data.Text (Text)
import System.IO.Unsafe (unsafePerformIO)

{- | Name of a memo table.

The name is not stored anywhere: it labels the call site for a reader, and
being an argument it also keeps two structurally identical 'memo' applications
from being shared into one table.
-}
newtype MemoCacheTag
    = NameTag Text
    deriving (Eq, Ord, Show)

mkInnerTag :: MemoCacheTag -> MemoCacheTag
mkInnerTag (NameTag t) = NameTag (t <> "-inner")

memoIO :: forall a b. (Hashable a) => (a -> b) -> IO (a -> IO b)
memoIO f = do
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
memo :: (Hashable a) => MemoCacheTag -> (a -> b) -> (a -> b)
memo !_tag f =
    let f' = unsafePerformIO (memoIO f)
     in \x -> unsafePerformIO (f' x)

-- | Memoize a pure binary function as nested unary memo tables.
memo2 :: (Hashable a, Hashable b) => MemoCacheTag -> (a -> b -> c) -> a -> b -> c
memo2 tag f = memo tag (memo (mkInnerTag tag) . f)
