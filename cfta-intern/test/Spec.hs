{- | The contract of the interning tables and the memo tables.

The interned automata of cfta rely on these properties: one identity
for each distinct key, also when threads race to intern it; identities in
the order of interning in one thread; one cache for each symbol type; and
memo tables that change no result.
-}
module Main (main) where

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import Control.Monad (forM_, replicateM)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import Data.List (nub, sort)
import System.IO.Unsafe (unsafePerformIO)
import Test.Hspec (describe, hspec, it, shouldBe, shouldReturn, shouldSatisfy)

import Data.CFTA.Interned.Cache
import Data.CFTA.Interned.Memo

main :: IO ()
main = hspec $ do
    describe "intern" $ do
        it "gives equal keys one identity, in the order of interning" $ do
            cache <- newIdSupply >>= freshCacheWith
            let identity key = fst (intern cache (,) key)
            map identity ([1, 2, 1, 3, 2] :: [Int]) `shouldBe` [0, 1, 0, 2, 1]

        it "gives each key one identity when threads race to intern it" $ do
            cache <- newIdSupply >>= freshCacheWith
            done <- newEmptyMVar
            let keys = [0 .. 999 :: Int]
                identities offset = [(key, fst (intern cache (,) key)) | key <- drop offset keys <> take offset keys]
            forM_ [0, 125 .. 875] $ \offset -> forkIO $ do
                let found = sort (identities offset)
                putMVar done $! sum (map snd found) `seq` found
            results <- replicateM 8 (takeMVar done)
            case results of
                first : rest -> do
                    rest `shouldSatisfy` all (== first)
                    length (nub (map snd first)) `shouldBe` length keys
                [] -> pure ()

    describe "insertKeepingFirst" $
        it "keeps the first value of a key" $ do
            table <- newTable 0
            first <- insertKeepingFirst table 'k' "first"
            second <- insertKeepingFirst table 'k' "second"
            (first, second) `shouldBe` ("first", "first")

    describe "selectCache" $
        it "gives each symbol type one cache, the first that it allocates" $ do
            family <- newCacheFamily
            allocations <- newIORef (0 :: Int)
            let allocate = atomicModifyIORef' allocations (\count -> (count + 1, count))
                forInt = selectCache @Int family allocate
                forBool = selectCache @Bool family allocate
            (forInt, forBool, selectCache @Int family allocate) `shouldBe` (0, 1, 0)

    describe "memoWith" $
        it "changes no result and computes each distinct argument once" $ do
            table <- newMemoCache
            calls <- newIORef 0
            map (memoWith table (countedDouble calls)) [1, 2, 1, 2, 3] `shouldBe` [2, 4, 2, 4, 6]
            readIORef calls `shouldReturn` 3

    describe "memo2"
        $ it "changes no result"
        $ memo2 (+) (2 :: Int) 3 `shouldBe` 5

    describe "memoTypeableWith" $
        it "keeps one table for each symbol type" $ do
            family <- newTypeableMemoCache
            let viaInt = memoTypeableWith @Int family (* (2 :: Int))
                viaBool = memoTypeableWith @Bool family (* (3 :: Int))
            (viaInt 5, viaBool 5, viaInt 5) `shouldBe` (10, 15, 10)

-- | Double a number, and count the call, so that a test sees how often a memo table computes.
countedDouble :: IORef Int -> Int -> Int
countedDouble calls x = unsafePerformIO $ do
    atomicModifyIORef' calls (\count -> (count + 1, ()))
    pure (2 * x)
{-# NOINLINE countedDouble #-}
