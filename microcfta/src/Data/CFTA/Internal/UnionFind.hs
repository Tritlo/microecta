{- | Lightweight union-find implementation suitable for nondeterministic search.

Mutable union-find, as in @Data.Equivalence.Monad@, should be faster overall,
but enumeration branches in the list monad need a structure that can be copied
and backtracked cheaply. This module stores parent pointers in an 'IntMap' and
returns updated structures from 'find' and 'union'.
-}
module Data.CFTA.Internal.UnionFind (
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

{- | What the forest stores for one variable.

A 'Parent' points to the next variable towards the root. A 'Root' is the
representative of its set and holds the size of the set.
-}
data Entry = Parent !UVar | Root !Int
    deriving (Eq, Ord, Show)

-- | Persistent union-find forest, keyed by the integer id of a variable.
newtype UnionFind = UnionFind {getUnionFindMap :: IntMap Entry}
    deriving (Eq, Ord, Show)

-- | Empty forest. Variables are inserted lazily by 'find'.
empty :: UnionFind
empty = UnionFind IntMap.empty

-- | Forest containing each supplied variable as a singleton set.
withInitialValues :: [UVar] -> UnionFind
withInitialValues uvs = UnionFind $ IntMap.fromList $ map ((,Root 1) . uvarToInt) uvs

---------------------------
-------- Union-find operations
---------------------------

-- | Store the entry of a variable.
setEntry :: UVar -> Entry -> UnionFind -> UnionFind
setEntry uv e (UnionFind m) = UnionFind (IntMap.insert (uvarToInt uv) e m)

-- | Merge the two variable classes, preferring the larger class as root.
union :: UVar -> UVar -> UnionFind -> UnionFind
union uv1 uv2 uf = flip execState uf $ do
    (uv1Rep, uv1Size) <- findRoot uv1
    (uv2Rep, uv2Size) <- findRoot uv2
    if uv1Rep == uv2Rep
        then
            return ()
        else
            if uv1Size < uv2Size
                then do
                    modify' (setEntry uv1Rep (Parent uv2Rep))
                    modify' (setEntry uv2Rep (Root (uv1Size + uv2Size)))
                else do
                    modify' (setEntry uv2Rep (Parent uv1Rep))
                    modify' (setEntry uv1Rep (Root (uv1Size + uv2Size)))

-- | Find the representative of a variable and the size of its set.
findRoot :: UVar -> State UnionFind (UVar, Int)
findRoot uv = do
    m <- get
    case IntMap.lookup (uvarToInt uv) (getUnionFindMap m) of
        Nothing -> put (setEntry uv (Root 1) m) >> return (uv, 1)
        Just (Root size) -> return (uv, size)
        Just (Parent p) -> do
            (rep, size) <- findRoot p
            -- Compress against the state the recursive call left behind,
            -- not against @m@: the rest of the chain was compressed there,
            -- and rebuilding from @m@ would discard it.
            modify' (setEntry uv (Parent rep))
            return (rep, size)

-- | Find a variable's representative and return the path-compressed forest.
find :: UVar -> UnionFind -> (UVar, UnionFind)
find uv = runState (fst <$> findRoot uv)
