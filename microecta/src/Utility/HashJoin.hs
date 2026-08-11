-- | Hash-table based grouping and joining helpers for interned structures.
module Utility.HashJoin (
    nubByIdSinglePass,
    clusterByHash,
    hashJoin,
) where

import Control.Monad.ST (ST, runST)
import Data.Foldable (foldrM)

import qualified Data.HashTable.ST.Cuckoo as HT

-------------------------------------
--- Hash join / clustering / nub
--------------------------------

{- | Remove duplicates by a stable identity hash.

Precondition: if @h x == h y@, then @x == y@. This is intended for interned
values where the integer id is already a complete identity. The output order is
reversed relative to first occurrence because callers only need set-like
behavior.
-}
nubByIdSinglePass :: forall a. (a -> Int) -> [a] -> [a]
nubByIdSinglePass _ [x] = [x]
nubByIdSinglePass h ls = runST (go ls [] =<< HT.new)
  where
    go :: [a] -> [a] -> HT.HashTable s Int Bool -> ST s [a]
    go [] acc _ = return acc
    go (x : xs) acc ht = do
        alreadyPresent <-
            HT.mutate
                ht
                (h x)
                ( \case
                    Nothing -> (Just True, False)
                    Just _ -> (Just True, True)
                )
        if alreadyPresent
            then
                go xs acc ht
            else
                go xs (x : acc) ht

maybeAddToHt :: v -> Maybe [v] -> (Maybe [v], ())
maybeAddToHt v = \case
    Nothing -> (Just [v], ())
    Just vs -> (Just (v : vs), ())

-- | Group values by hash.
clusterByHash :: (a -> Int) -> [a] -> [[a]]
clusterByHash h ls = runST $ do
    ht <- HT.new
    mapM_ (\x -> HT.mutate ht (h x) (maybeAddToHt x)) ls
    HT.foldM (\res (_, vs) -> return $ vs : res) [] ht

-- | Join two lists by equal hash and combine matching pairs.
hashJoin :: (a -> Int) -> (a -> a -> b) -> [a] -> [a] -> [b]
hashJoin h j l1 l2 = runST $ do
    ht2 <- HT.new
    mapM_ (\x -> HT.mutate ht2 (h x) (maybeAddToHt x)) l2
    foldrM
        ( \x res -> do
            maybeCluster <- HT.lookup ht2 (h x)
            case maybeCluster of
                Nothing -> return res
                Just vs2 -> return $ foldr (\v2 acc -> j x v2 : acc) res vs2
        )
        []
        l1
