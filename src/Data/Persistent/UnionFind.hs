{- | Lightweight union-find implementation suitable for nondeterministic search.

Mutable union-find, as in @Data.Equivalence.Monad@, should be faster overall,
but enumeration branches in the list monad need a structure that can be copied
and backtracked cheaply. This module stores parent pointers in an 'IntMap' and
returns updated structures from 'find' and 'union'.
-}
module Data.Persistent.UnionFind (
    UVarGen,
    initUVarGen,
    nextUVar,
    UVar,
    uvarToInt,
    intToUVar,
    UnionFind,
    empty,
    withInitialValues,
    union,
    find,
) where

import Control.Monad.State.Strict (State, execState, get, modify', put, runState)
import Data.Coerce (coerce)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

----------------------------------------------------------

---------------------------
-------- UVarGen
---------------------------

-- | Fresh supply for enumeration variables.
newtype UVarGen = UVarGen Int
    deriving (Eq, Ord, Show)

-- | Initial variable supply.
initUVarGen :: UVarGen
initUVarGen = UVarGen 0

-- | Allocate one fresh variable and advance the supply.
nextUVar :: UVarGen -> (UVarGen, UVar)
nextUVar (UVarGen n) = (UVarGen (n + 1), UVar n)

---------------------------
-------- UVar
---------------------------

-- | Union-find variable identifier.
newtype UVar = UVar Int
    deriving (Eq, Ord, Show)

-- | Convert a variable to its dense integer id.
uvarToInt :: UVar -> Int
uvarToInt (UVar i) = i

-- | Reconstruct a variable from its dense integer id.
intToUVar :: Int -> UVar
intToUVar = UVar

---------------------------
-------- Union-find data structure
---------------------------

{- | Persistent union-find forest.

Roots store negative set sizes. Non-roots store their parent id.
-}
newtype UnionFind = UnionFind {getUnionFindMap :: IntMap Int}
    deriving (Eq, Ord, Show)

-- | Empty forest. Variables are inserted lazily by 'find'.
empty :: UnionFind
empty = UnionFind IntMap.empty

-- | Forest containing each supplied variable as a singleton set.
withInitialValues :: [UVar] -> UnionFind
withInitialValues uvs = UnionFind $ IntMap.fromList $ map (,-1) $ coerce uvs

---------------------------
-------- Union-find operations
---------------------------

-- | Merge the two variable classes, preferring the larger class as root.
union :: UVar -> UVar -> UnionFind -> UnionFind
union uv1 uv2 uf = flip execState uf $ do
    (uv1Rep, negativeUv1Size) <- findWithNegSize uv1
    (uv2Rep, negativeUv2Size) <- findWithNegSize uv2
    if uv1Rep == uv2Rep
        then
            return ()
        else
            if negativeUv1Size > negativeUv2Size
                then do
                    modify' (coerce (IntMap.insert @Int) uv1Rep uv2Rep)
                    modify' (coerce (IntMap.insert @Int) uv2Rep (negativeUv1Size + negativeUv2Size))
                else do
                    modify' (coerce (IntMap.insert @Int) uv2Rep uv1Rep)
                    modify' (coerce (IntMap.insert @Int) uv1Rep (negativeUv1Size + negativeUv2Size))

findWithNegSize :: UVar -> State UnionFind (UVar, Int)
findWithNegSize uv = do
    m <- get
    case coerce (IntMap.lookup @Int) uv m of
        Nothing -> put (coerce (IntMap.insert @Int) uv (-1 :: Int) m) >> return (uv, -1)
        Just x
            | x < 0 -> return (uv, x)
            | otherwise -> do
                (rep, size) <- findWithNegSize (UVar x)
                put (coerce (IntMap.insert @Int) uv rep m)
                return (rep, size)

-- | Find a variable's representative and return the path-compressed forest.
find :: UVar -> UnionFind -> (UVar, UnionFind)
find uv uf = coerce runState (fst <$> findWithNegSize uv) uf
