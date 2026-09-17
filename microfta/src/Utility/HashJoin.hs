-- | Group and join interned values by key.
module Utility.HashJoin (
    nubByIdSinglePass,
    clusterByHash,
    hashJoin,
) where

import Data.Containers.ListUtils (nubIntOn)
import Data.Hashable (Hashable)

import qualified Data.HashMap.Lazy as HashMap

-- Hash join / clustering / nub

{- | Remove duplicates by a stable identity.

This is intended for interned values where the integer id is already a complete
identity, so keeping one value per id keeps one per distinct value. The output
order is reversed relative to first occurrence because callers only need
set-like behavior.
-}
nubByIdSinglePass :: forall a. (a -> Int) -> [a] -> [a]
nubByIdSinglePass _ [x] = [x]
nubByIdSinglePass h ls = reverse (nubIntOn h ls)

{- | Group values by a key.

Key equality defines each group. Different keys remain separate even when
their hashes are equal. The order of groups is not specified.
-}
clusterByHash :: (Hashable k) => (a -> k) -> [a] -> [[a]]
clusterByHash key ls =
    HashMap.elems $ HashMap.fromListWith (++) [(key x, [x]) | x <- ls]

{- | Join two lists by equal keys and combine matching pairs.

As for 'clusterByHash', the table is keyed by the key itself, so the combining
function sees exactly the pairs whose keys are equal however the key hashes.
-}
hashJoin :: (Hashable k) => (a -> k) -> (a -> a -> b) -> [a] -> [a] -> [b]
hashJoin key j l1 l2 =
    [j x y | x <- l1, y <- HashMap.findWithDefault [] (key x) right]
  where
    right = HashMap.fromListWith (++) [(key x, [x]) | x <- l2]
