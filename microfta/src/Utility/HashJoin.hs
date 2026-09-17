-- | Group and join interned values by key.
module Utility.HashJoin (
    clusterByHash,
    hashJoin,
) where

import Data.Hashable (Hashable)

import qualified Data.HashMap.Lazy as HashMap

-- Hash join / clustering / nub

{- | Group values by a key.

Key equality defines each group. Different keys remain separate even when
their hashes are equal. Each group keeps its input order; the order of groups
is not specified.
-}
clusterByHash :: (Hashable k) => (a -> k) -> [a] -> [[a]]
clusterByHash key ls =
    map reverse $ HashMap.elems $ HashMap.fromListWith (++) [(key x, [x]) | x <- ls]

{- | Join two lists by equal keys and combine matching pairs.

As for 'clusterByHash', the table is keyed by the key itself, so the combining
function sees exactly the pairs whose keys are equal however the key hashes.
-}
hashJoin :: (Hashable k) => (a -> k) -> (a -> a -> b) -> [a] -> [a] -> [b]
hashJoin key j l1 l2 =
    [j x y | x <- l1, y <- HashMap.findWithDefault [] (key x) right]
  where
    right = HashMap.fromListWith (++) [(key x, [x]) | x <- l2]
