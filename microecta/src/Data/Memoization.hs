{-# LANGUAGE OverloadedStrings #-}

{- | Quick-and-dirty hash-based memoization.

The ECTA core relies on stable global memo tables for interning and recursive
graph operations. This module intentionally keeps that machinery tiny: each
call to 'memo' allocates one process-global table through 'unsafePerformIO'.

Safe from any thread. The table is an immutable map in an @IORef@, read
without blocking and updated with 'atomicModifyIORef''. Two racers may install
different thunks and return their own result, but both compute the same answer
because every function memoized here is pure.

The lazy map is important: an atomic update installs the result thunk without
forcing the memoized computation. That computation may itself intern or call
other memoized functions, so it must run outside the update.

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

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Hashable (Hashable (..))
import Data.IORef (atomicModifyIORef', newIORef, readIORef)
import Data.Text (Text)
import System.IO.Unsafe (unsafePerformIO)

{- | Name of a memo table.

The name is not stored in the table. It labels the call site for readers and
makes distinct source uses visibly distinct; table identity still belongs to
the particular 'memo' application, not to the text of the tag.
-}
newtype MemoCacheTag
    = NameTag Text
    deriving (Eq, Ord, Show)

memoIO :: forall a b. (Hashable a) => (a -> b) -> IO (a -> IO b)
memoIO f = do
    ref <- newIORef (HashMap.empty :: HashMap a b)
    let f' x = do
            cached <- HashMap.lookup x <$> readIORef ref
            case cached of
                Just r -> return r
                Nothing -> do
                    -- @r@ is never forced under the update: forcing it runs
                    -- the memoized computation, which interns, which comes
                    -- back through here and would diverge. Two racers may each
                    -- insert their own thunk; both compute the same answer,
                    -- because everything memoized here is pure.
                    let r = f x
                    atomicModifyIORef' ref (\m -> (HashMap.insert x r m, ()))
                    return r
    return f'

-- | Memoize a pure unary function in a process-global mutable hash table.
memo :: (Hashable a) => MemoCacheTag -> (a -> b) -> (a -> b)
{-# NOINLINE memo #-}
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
