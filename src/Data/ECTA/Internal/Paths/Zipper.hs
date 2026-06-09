{- | These were used in an earlier version of the enumeration algorithm, but no longer.

  They are being kept around just in case.
-}
module Data.ECTA.Internal.Paths.Zipper (
    unionPathTrie,
    InvertedPathTrie (..),
    PathTrieZipper (..),
    emptyPathTrieZipper,
    pathTrieToZipper,
    zipperCurPathTrie,
    pathTrieZipperDescend,
    pathTrieZipperAscend,
    unionPathTrieZipper,
) where

import Data.ECTA.Internal.Paths

-----------------------------------------------------------------------

---------------------
------- Path trie union
------- (7/9/21: only used as utility for unionPathTrieZipper)
---------------------

unionPathTrie :: PathTrie -> PathTrie -> Maybe PathTrie
unionPathTrie EmptyPathTrie pt = Just pt
unionPathTrie pt EmptyPathTrie = Just pt
unionPathTrie TerminalPathTrie TerminalPathTrie = Just TerminalPathTrie
unionPathTrie TerminalPathTrie _ = Nothing
unionPathTrie _ TerminalPathTrie = Nothing
unionPathTrie (PathTrieSingleChild i1 pt1) (PathTrieSingleChild i2 pt2) =
    if i1 == i2
        then
            PathTrieSingleChild i1 <$> unionPathTrie pt1 pt2
        else
            Just $
                childrenToPathTrie $
                    if i1 < i2
                        then [(i1, pt1), (i2, pt2)]
                        else [(i2, pt2), (i1, pt1)]
unionPathTrie pt1@(PathTrieSingleChild _ _) pt2@(PathTrie _) =
    childrenToPathTrie <$> unionChildren (trieChildren pt1) (trieChildren pt2)
unionPathTrie pt1@(PathTrie _) pt2@(PathTrieSingleChild _ _) =
    childrenToPathTrie <$> unionChildren (trieChildren pt1) (trieChildren pt2)
unionPathTrie (PathTrie children1) (PathTrie children2) =
    childrenToPathTrie <$> unionChildren children1 children2

-- | View a non-terminal trie node as sorted sparse children.
trieChildren :: PathTrie -> [(Int, PathTrie)]
trieChildren (PathTrieSingleChild i pt) = [(i, pt)]
trieChildren (PathTrie children) = children
trieChildren _ = []

{- | Rebuild the compact trie constructor for a sparse child list.

This is the boundary that restores the `PathTrie` invariant after union.  Zipper
operations can temporarily carry empty children, mirroring the old dense-vector
representation, but canonical tries should keep only non-empty children and
collapse back to the empty or single-child constructors when possible.
-}
childrenToPathTrie :: [(Int, PathTrie)] -> PathTrie
childrenToPathTrie children =
    case filter (not . isEmptyPathTrie . snd) children of
        [] -> EmptyPathTrie
        [(i, pt)] -> PathTrieSingleChild i pt
        nonemptyChildren -> PathTrie nonemptyChildren

-- | Union two sorted sparse child lists, failing if any children contradict.
unionChildren :: [(Int, PathTrie)] -> [(Int, PathTrie)] -> Maybe [(Int, PathTrie)]
unionChildren [] children = Just children
unionChildren children [] = Just children
unionChildren left@((i1, pt1) : rest1) right@((i2, pt2) : rest2) =
    case compare i1 i2 of
        LT -> ((i1, pt1) :) <$> unionChildren rest1 right
        GT -> ((i2, pt2) :) <$> unionChildren left rest2
        EQ -> do
            pt <- unionPathTrie pt1 pt2
            ((i1, pt) :) <$> unionChildren rest1 rest2

---------------------
------- Zippers
---------------------

data InvertedPathTrie
    = PathZipperRoot
    | PathTrieAt {-# UNPACK #-} !Int !PathTrie !InvertedPathTrie
    deriving (Eq, Ord, Show)

data PathTrieZipper = PathTrieZipper !PathTrie !InvertedPathTrie
    deriving (Eq, Ord, Show)

emptyPathTrieZipper :: PathTrieZipper
emptyPathTrieZipper = PathTrieZipper EmptyPathTrie PathZipperRoot

pathTrieToZipper :: PathTrie -> PathTrieZipper
pathTrieToZipper pt = PathTrieZipper pt PathZipperRoot

zipperCurPathTrie :: PathTrieZipper -> PathTrie
zipperCurPathTrie (PathTrieZipper pt _) = pt

unionInvertedPathTrie :: InvertedPathTrie -> InvertedPathTrie -> Maybe InvertedPathTrie
unionInvertedPathTrie PathZipperRoot ipt = Just ipt
unionInvertedPathTrie ipt PathZipperRoot = Just ipt
unionInvertedPathTrie (PathTrieAt i1 pt1 ipt1) (PathTrieAt i2 pt2 ipt2) =
    if i1 /= i2
        then
            Nothing
        else
            PathTrieAt i1 <$> unionPathTrie pt1 pt2 <*> unionInvertedPathTrie ipt1 ipt2

unionPathTrieZipper :: PathTrieZipper -> PathTrieZipper -> Maybe PathTrieZipper
unionPathTrieZipper (PathTrieZipper pt1 ipt1) (PathTrieZipper pt2 ipt2) =
    PathTrieZipper <$> unionPathTrie pt1 pt2 <*> unionInvertedPathTrie ipt1 ipt2

pathTrieZipperDescend :: PathTrieZipper -> Int -> PathTrieZipper
pathTrieZipperDescend (PathTrieZipper pt z) i = PathTrieZipper (pathTrieDescend pt i) (PathTrieAt i pt z)

{- | The semantics of this may not be what you expect: Path trie zippers do not support editing currently, only traversing.
  The value at the cursor (as well as the index) is ignored except when traversing above the root, where it uses those
  values to extend the path trie upwards.
-}
pathTrieZipperAscend :: PathTrieZipper -> Int -> PathTrieZipper
pathTrieZipperAscend (PathTrieZipper pt PathZipperRoot) i = PathTrieZipper (PathTrieSingleChild i pt) PathZipperRoot
pathTrieZipperAscend (PathTrieZipper _ (PathTrieAt _ pt' ipt)) _ = PathTrieZipper pt' ipt
