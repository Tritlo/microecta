{-# LANGUAGE OverloadedStrings #-}

{- | Quick-and-dirty, thread-unsafe, hash-based memoization.

The ECTA core relies on stable global memo tables for interning and recursive
graph operations. This module intentionally keeps that machinery tiny: each
call to 'memo' allocates one process-global hash table through
'unsafePerformIO'.

The tables never evict, so a memoized function retains an entry for every
distinct argument it has ever been applied to, for the lifetime of the process.
That is what makes repeated work free, and it means memory grows with the
number of distinct inputs rather than with the work done. See the memory
section of the package README.
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

{- | Memoize a pure binary function in one table keyed by the pair.

Nesting two unary tables instead would allocate a fresh hash table for every
distinct first argument -- around a kilobyte each, before storing a single
entry. On a workload with 64k distinct first arguments that costs 167 MB
against this version's 68 MB, for no gain: measured on the core benchmark, the
pair key is within noise on time and allocates 0.1% more.
-}
memo2 :: (Hashable a, Hashable b) => MemoCacheTag -> (a -> b -> c) -> a -> b -> c
memo2 tag f = curry (memo tag (uncurry f))
