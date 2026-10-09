{-# LANGUAGE DerivingVia #-}
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
    ChildIndex (..),
    unPath,
    path,
    isStrictSubpath,
    Pathable (..),
) where

import Data.Coerce (coerce)
import Data.Hashable (Hashable (..))
import Data.List ((!?))
import Data.Maybe (maybeToList)
import qualified Data.Tree as Tree

import Data.CFTA.Index (ChildIndex (..))
import Data.CFTA.Internal.Tree (adjustAt)

{- | Path into an edge's children, represented as child indexes.

A path compares and hashes as its list of 'Int'. The base library specializes
the list instances for 'Int' but not for 'ChildIndex', and paths are compared
in every set and map of paths.
-}
newtype Path = Path [ChildIndex]
    deriving (Show)
    deriving (Eq, Ord) via [Int]

instance Hashable Path where
    hashWithSalt salt (Path components) = salt `hashWithSalt` (coerce components :: [Int])

-- | Extract the raw child-index list from a 'Path'.
unPath :: Path -> [ChildIndex]
unPath (Path p) = p

-- | Build a 'Path' from child indexes.
path :: [ChildIndex] -> Path
path = Path

{-# COMPLETE EmptyPath, ConsPath #-}

pattern EmptyPath :: Path
pattern EmptyPath = Path []

pattern ConsPath :: ChildIndex -> Path -> Path
pattern ConsPath p ps <- Path (p : (Path -> ps))
  where
    ConsPath p (Path ps) = Path (p : ps)

-- | Whether the first path is a strict prefix of the second path.
isStrictSubpath :: Path -> Path -> Bool
isStrictSubpath EmptyPath EmptyPath = False
isStrictSubpath EmptyPath _ = True
isStrictSubpath (ConsPath p1 ps1) (ConsPath p2 ps2)
    | p1 == p2 = isStrictSubpath ps1 ps2
isStrictSubpath _ _ = False

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
    getPath (ConsPath (ChildIndex p) ps) (Tree.Node _ ts) = getPath ps =<< ts !? p

    getAllAtPath p t = maybeToList $ getPath p t

    modifyAtPath f EmptyPath t = f t
    modifyAtPath f (ConsPath p ps) (Tree.Node s ts) = Tree.Node s (adjustAt p (modifyAtPath f ps) ts)
