{-# LANGUAGE FunctionalDependencies #-}

{- | Child-index paths into terms and graphs.

A 'Path' names a position by the child index taken at each level. 'Pathable'
reads and edits the value at a path. The instances for interned graphs live in
"Data.CFTA.Interned"; they follow every alternative, so reading a path from a
node gives the union of the languages at that position. Constraint theories
build their constraints over these paths.
-}
module Data.CFTA.Path (
    Path (.., EmptyPath, ConsPath),
    unPath,
    path,
    isSubpath,
    isStrictSubpath,
    substSubpath,
    Pathable (..),
) where

import Data.Hashable (Hashable (..))
import Data.List ((!?))
import Data.Maybe (maybeToList)
import qualified Data.Tree as Tree

import Data.CFTA.Internal.Tree (adjustAt)

-- | Path into an edge's children, represented as child indexes.
newtype Path = Path [Int]
    deriving (Eq, Ord, Show)

instance Hashable Path where
    hashWithSalt salt (Path components) = salt `hashWithSalt` components

-- | Extract the raw child-index list from a 'Path'.
unPath :: Path -> [Int]
unPath (Path p) = p

-- | Build a 'Path' from child indexes.
path :: [Int] -> Path
path = Path

{-# COMPLETE EmptyPath, ConsPath #-}

pattern EmptyPath :: Path
pattern EmptyPath = Path []

pattern ConsPath :: Int -> Path -> Path
pattern ConsPath p ps <- Path (p : (Path -> ps))
  where
    ConsPath p (Path ps) = Path (p : ps)

-- | Whether the first path is a prefix of the second path.
isSubpath :: Path -> Path -> Bool
isSubpath EmptyPath _ = True
isSubpath (ConsPath p1 ps1) (ConsPath p2 ps2)
    | p1 == p2 = isSubpath ps1 ps2
isSubpath _ _ = False

-- | Whether the first path is a strict prefix of the second path.
isStrictSubpath :: Path -> Path -> Bool
isStrictSubpath EmptyPath EmptyPath = False
isStrictSubpath EmptyPath _ = True
isStrictSubpath (ConsPath p1 ps1) (ConsPath p2 ps2)
    | p1 == p2 = isStrictSubpath ps1 ps2
isStrictSubpath _ _ = False

{- | Replace a prefix of a path.

@substSubpath replacement toReplace target@ requires @toReplace@ to be a
prefix of @target@, and replaces it by @replacement@.
-}
substSubpath :: Path -> Path -> Path -> Path
substSubpath replacement toReplace target = Path $ unPath replacement ++ drop (length $ unPath toReplace) (unPath target)

-- | Things that can be inspected or edited by child-index paths.
class Pathable t t' | t -> t' where
    -- | Result type used when a path is absent.
    type Emptyable t'

    -- | Read the value at a path, returning the empty value when absent.
    getPath :: Path -> t -> Emptyable t'

    -- | Read all values reachable at a path.
    getAllAtPath :: Path -> t -> [t']

    -- | Apply a local edit at a path.
    modifyAtPath :: (t' -> t') -> Path -> t -> t

instance Pathable (Tree.Tree symbol) (Tree.Tree symbol) where
    type Emptyable (Tree.Tree symbol) = Maybe (Tree.Tree symbol)

    getPath EmptyPath t = Just t
    getPath (ConsPath p ps) (Tree.Node _ ts) = getPath ps =<< ts !? p

    getAllAtPath p t = maybeToList $ getPath p t

    modifyAtPath f EmptyPath t = f t
    modifyAtPath f (ConsPath p ps) (Tree.Node s ts) = Tree.Node s (adjustAt p (modifyAtPath f ps) ts)
