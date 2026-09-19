{-# LANGUAGE OverloadedStrings #-}

{- | Representations of paths in an FTA, data structures for equality
constraints over paths, and algorithms for saturating these constraints.

The 'Data.CFTA.Constraint.Constraint' instance lives with the class.
-}
module Data.CFTA.Constraint.Equality (
    getMaxNonemptyIndex,
    PathTrie (..),
    isEmptyPathTrie,
    isTerminalPathTrie,
    toPathTrie,
    fromPathTrie,
    pathTrieDescend,
    PathEClass (PathEClass, ..),
    unPathEClass,
    hasSubsumingMember,
    completedSubsumptionOrdering,
    EqConstraints (.., EmptyConstraints),
    rawMkEqConstraints,
    unsafeGetEclasses,
    hasSubsumingMemberListBased,
    isContradicting,
    mkEqConstraints,
    combineEqConstraints,
    eqConstraintsDescend,
    constraintsAreContradictory,
    constraintsImply,
    subsumptionOrderedEclasses,
    unsafeSubsumptionOrderedEclasses,
) where

import Prelude hiding (round)

import Control.Monad (forM, forM_, when)
import Control.Monad.ST (ST, runST)
import Data.Array.ST (STUArray, newListArray, readArray, writeArray)
import Data.Containers.ListUtils (nubOrd)
import Data.Function (on)
import Data.Hashable (Hashable (..))
import qualified Data.IntMap.Lazy as IntMap
import Data.List (compareLength, groupBy, isSubsequenceOf, nub, sort, sortBy)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import qualified Data.Text as Text

import Data.CFTA.Internal.Pretty
import Data.CFTA.Interned.Memo (memo2)
import Data.CFTA.Path (Path (..), isStrictSubpath, substSubpath)

-------------------------------------------------------

-----------------------------------------------------------------------
--------------------------- Misc / general ----------------------------
-----------------------------------------------------------------------

-----------------------------------------------------------------------
-------------------------------- Paths --------------------------------
-----------------------------------------------------------------------

-- | Largest child index present in a trie node, if any.
getMaxNonemptyIndex :: PathTrie -> Maybe Int
getMaxNonemptyIndex EmptyPathTrie = Nothing
getMaxNonemptyIndex TerminalPathTrie = Nothing
getMaxNonemptyIndex (PathTrie children) = fst <$> IntMap.lookupMax children

---------------------
------- Path tries
---------------------

{- | Trie of paths used to index equality constraints.

Each child map is non-empty. Empty children are not permitted. Child values
are lazy, so traversal can stop before it evaluates an unrelated branch.
-}
data PathTrie
    = EmptyPathTrie
    | TerminalPathTrie
    | PathTrie !(IntMap.IntMap PathTrie)
    deriving (Eq, Show)

instance Hashable PathTrie where
    hashWithSalt salt EmptyPathTrie = salt `hashWithSalt` (0 :: Int)
    hashWithSalt salt TerminalPathTrie = salt `hashWithSalt` (1 :: Int)
    hashWithSalt salt (PathTrie children) =
        IntMap.foldlWithKey'
            (\acc index child -> acc `hashWithSalt` index `hashWithSalt` child)
            (salt `hashWithSalt` (3 :: Int))
            children

-- | Check for the trie containing no paths.
isEmptyPathTrie :: PathTrie -> Bool
isEmptyPathTrie EmptyPathTrie = True
isEmptyPathTrie _ = False

-- | Check for the trie containing exactly the empty path.
isTerminalPathTrie :: PathTrie -> Bool
isTerminalPathTrie TerminalPathTrie = True
isTerminalPathTrie _ = False

-- | Whether a trie contains at least two distinct paths.
pathTrieHasAtLeastTwoPaths :: PathTrie -> Bool
pathTrieHasAtLeastTwoPaths = go False
  where
    go :: Bool -> PathTrie -> Bool
    go _ EmptyPathTrie = False
    go seenOne TerminalPathTrie = seenOne
    go seenOne (PathTrie children) = goChildren seenOne (IntMap.toAscList children)

    goChildren :: Bool -> [(Int, PathTrie)] -> Bool
    goChildren _ [] = False
    goChildren seenOne ((_, pt) : rest)
        | go seenOne pt = True
        | pathTrieHasAnyPath pt =
            seenOne || goChildren True rest
        | otherwise = goChildren seenOne rest

    pathTrieHasAnyPath :: PathTrie -> Bool
    pathTrieHasAnyPath EmptyPathTrie = False
    pathTrieHasAnyPath TerminalPathTrie = True
    pathTrieHasAnyPath (PathTrie children) = any pathTrieHasAnyPath children

-- | A pending sibling branch and the path depth at which it diverges.
data PathTrieChoice = PathTrieChoice !Int ![(Int, PathTrie)]

-- | Order tries by the lexicographic list of paths they represent.
instance Ord PathTrie where
    compare = comparePathTries

-- | Compare two tries without materialising their path lists.
comparePathTries :: PathTrie -> PathTrie -> Ordering
comparePathTries EmptyPathTrie EmptyPathTrie = EQ
comparePathTries EmptyPathTrie _ = LT
comparePathTries _ EmptyPathTrie = GT
comparePathTries left right = comparePathTrieBranches 0 [] left [] right

-- | Compare the suffixes of two paths whose prefixes are equal.
comparePathTrieBranches :: Int -> [PathTrieChoice] -> PathTrie -> [PathTrieChoice] -> PathTrie -> Ordering
comparePathTrieBranches _ _ EmptyPathTrie _ _ =
    error "comparePathTries: invalid empty child"
comparePathTrieBranches _ _ _ _ EmptyPathTrie =
    error "comparePathTries: invalid empty child"
comparePathTrieBranches _ choices1 TerminalPathTrie choices2 TerminalPathTrie =
    comparePathTrieChoices choices1 choices2
comparePathTrieBranches _ _ TerminalPathTrie _ _ = LT
comparePathTrieBranches _ _ _ _ TerminalPathTrie = GT
comparePathTrieBranches depth choices1 (PathTrie children1) choices2 (PathTrie children2) =
    case (IntMap.toAscList children1, IntMap.toAscList children2) of
        ((i1, pt1) : rest1, (i2, pt2) : rest2) ->
            case compare i1 i2 of
                EQ ->
                    comparePathTrieBranches
                        (depth + 1)
                        (rememberPathTrieChoice depth rest1 choices1)
                        pt1
                        (rememberPathTrieChoice depth rest2 choices2)
                        pt2
                result -> result
        _ -> error "comparePathTries: invalid empty child list"

{- | Compare the next paths after two equal paths have ended.

A choice at greater depth keeps more of the common path, so it sorts before a
choice that changes an earlier component. This is the case the legacy
structural comparator handled incorrectly.
-}
comparePathTrieChoices :: [PathTrieChoice] -> [PathTrieChoice] -> Ordering
comparePathTrieChoices [] [] = EQ
comparePathTrieChoices [] _ = LT
comparePathTrieChoices _ [] = GT
comparePathTrieChoices (PathTrieChoice _ [] : _) _ =
    error "comparePathTries: invalid empty choice"
comparePathTrieChoices _ (PathTrieChoice _ [] : _) =
    error "comparePathTries: invalid empty choice"
comparePathTrieChoices (PathTrieChoice depth1 ((i1, pt1) : rest1) : outer1) (PathTrieChoice depth2 ((i2, pt2) : rest2) : outer2) =
    case compare depth2 depth1 of
        EQ -> case compare i1 i2 of
            EQ ->
                comparePathTrieBranches
                    (depth1 + 1)
                    (rememberPathTrieChoice depth1 rest1 outer1)
                    pt1
                    (rememberPathTrieChoice depth2 rest2 outer2)
                    pt2
            result -> result
        result -> result

-- | Retain a non-empty sibling list as a future traversal choice.
rememberPathTrieChoice :: Int -> [(Int, PathTrie)] -> [PathTrieChoice] -> [PathTrieChoice]
rememberPathTrieChoice _ [] choices = choices
rememberPathTrieChoice depth siblings choices = PathTrieChoice depth siblings : choices

{- | Build a trie from a set of paths.

Precondition: the paths are distinct and none is a prefix of another. Either
would put a path and the empty path in one group, which a trie has no way to
represent, so it is reported rather than silently mis-built.
-}
toPathTrie :: [Path] -> PathTrie
toPathTrie [] = EmptyPathTrie
toPathTrie [EmptyPath] = TerminalPathTrie
toPathTrie ps@(firstPath : _) =
    if all (\p -> headOf p == headOf firstPath) ps
        then
            let child = toPathTrie $ map tailOf ps
             in child `seq` PathTrie (IntMap.singleton (headOf firstPath) child)
        else
            PathTrie (IntMap.fromDistinctAscList children)
  where
    groups =
        groupBy ((==) `on` headOf) $
            sortBy (compare `on` headOf) ps

    children =
        [ (headOf groupHead, toPathTrie $ map tailOf group)
        | group@(groupHead : _) <- groups
        ]

    headOf (ConsPath i _) = i
    headOf EmptyPath = malformed

    tailOf (ConsPath _ rest) = rest
    tailOf EmptyPath = malformed

    malformed =
        error
            "toPathTrie: input paths must be distinct, with none a prefix of another"

-- | Convert a trie back to its sorted path list.
fromPathTrie :: PathTrie -> [Path]
fromPathTrie EmptyPathTrie = []
fromPathTrie TerminalPathTrie = [EmptyPath]
fromPathTrie (PathTrie children) =
    concatMap (\(i, pt) -> map (ConsPath i) $ fromPathTrie pt) (IntMap.toAscList children)

-- | Descend through one child index, returning 'EmptyPathTrie' if absent.
pathTrieDescend :: PathTrie -> Int -> PathTrie
pathTrieDescend EmptyPathTrie _ = EmptyPathTrie
pathTrieDescend TerminalPathTrie _ = EmptyPathTrie
pathTrieDescend (PathTrie children) i =
    IntMap.findWithDefault EmptyPathTrie i children

--------------------------------------------------------------------------
---------------------- Equality constraints over paths -------------------
--------------------------------------------------------------------------

---------------------------
---------- Path E-classes
---------------------------

{- | Equality class of paths.

The trie drives subsumption and descent; the path list keeps the older public
API and reduction code cheap to read; the hash is computed at most once,
because every edge that carries the class hashes it when it is interned.
Values built by @PathEClass@ and @mkPathEClassFromPathTrie@ keep the views
consistent.
-}
data PathEClass = PathEClass'
    { getPathTrie :: !PathTrie
    , getOrigPaths :: [Path]
    , getPathHash :: Int
    -- ^ Lazy: a class that is only descended or compared never pays for it.
    }

instance Show PathEClass where
    showsPrec precedence pec = showParen (precedence > 10) $ showString "PathEClass " . showsPrec 11 (getOrigPaths pec)

instance Eq PathEClass where
    (==) = (==) `on` getPathTrie

-- | Compare the cached sorted path lists instead of rebuilding them from tries.
instance Ord PathEClass where
    compare = compare `on` getOrigPaths

-- | Build or match an equality class from its sorted path list view.
pattern PathEClass :: [Path] -> PathEClass
pattern PathEClass ps <- PathEClass' _ ps _
  where
    PathEClass ps =
        let paths = Set.toAscList $ Set.fromList ps
            trie = toPathTrie paths
         in PathEClass' trie paths (hash trie)

-- | Extract the paths in an equality class.
unPathEClass :: PathEClass -> [Path]
unPathEClass (PathEClass' _ paths _) = paths

instance Pretty PathEClass where
    pretty pec = "{" <> Text.intercalate "=" (map pretty $ unPathEClass pec) <> "}"

instance Hashable PathEClass where
    hashWithSalt salt = hashWithSalt salt . getPathHash

-- | Build an equality class from a trie, deriving the path list lazily.
mkPathEClassFromPathTrie :: PathTrie -> PathEClass
mkPathEClassFromPathTrie pt = PathEClass' pt (fromPathTrie pt) (hash pt)

-- | Whether one path in the first class strictly subsumes one path in the second.
hasSubsumingMember :: PathEClass -> PathEClass -> Bool
hasSubsumingMember pec1 pec2 = go (getPathTrie pec1) (getPathTrie pec2)
  where
    go :: PathTrie -> PathTrie -> Bool
    go EmptyPathTrie _ = False
    go _ EmptyPathTrie = False
    go TerminalPathTrie TerminalPathTrie = False
    go TerminalPathTrie _ = True
    go _ TerminalPathTrie = False
    go (PathTrie children1) (PathTrie children2) =
        or $ IntMap.intersectionWith go children1 children2

{- | Total ordering used when choosing constraint-propagation order.

Strict subsumption comes first: if one equality class contains a path that is a
strict prefix of a path in another class, the shorter one must be processed
before the longer one. Incomparable classes use the reversed trie ordering.
That tie-break keeps term-search-shaped workloads in the old left-to-right
propagation order, which avoids extra reduction work in practice.
-}
completedSubsumptionOrdering :: PathEClass -> PathEClass -> Ordering
completedSubsumptionOrdering pec1 pec2
    | hasSubsumingMember pec1 pec2 = LT
    | hasSubsumingMember pec2 pec1 = GT
    | otherwise = compare pec2 pec1

--------------------------------
---------- Equality constraints
--------------------------------

-- | Equality constraints attached to an ECTA edge.
data EqConstraints
    = -- | Equality classes over paths into the edge's children. Sorted.
      EqConstraints [PathEClass]
    | -- | The classes forced a path to equal one of its strict subpaths.
      EqContradiction
    deriving (Eq, Ord, Show)

instance Hashable EqConstraints where
    hashWithSalt salt (EqConstraints eclasses) =
        salt `hashWithSalt` (0 :: Int) `hashWithSalt` eclasses
    hashWithSalt salt EqContradiction =
        salt `hashWithSalt` (1 :: Int)

instance Pretty EqConstraints where
    pretty EqContradiction = "{contradiction}"
    pretty (EqConstraints eclasses) =
        "{" <> Text.intercalate "," (map pretty eclasses) <> "}"

--------- Destructors and patterns

-- | Unsafe. Internal use only
ecsGetPaths :: EqConstraints -> [[Path]]
ecsGetPaths EqContradiction = error "ecsGetPaths: Illegal argument 'EqContradiction'"
ecsGetPaths (EqConstraints eclasses) = map unPathEClass eclasses

pattern EmptyConstraints :: EqConstraints
pattern EmptyConstraints = EqConstraints []

-- | Extract equality classes, failing on 'EqContradiction'.
unsafeGetEclasses :: EqConstraints -> [PathEClass]
unsafeGetEclasses EqContradiction = error "unsafeGetEclasses: Illegal argument 'EqContradiction'"
unsafeGetEclasses (EqConstraints eclasses) = eclasses

-- | Construct constraints without congruence closure or contradiction checks.
rawMkEqConstraints :: [[Path]] -> EqConstraints
rawMkEqConstraints = EqConstraints . map PathEClass

-- | Check whether a constraint set is already contradictory.
constraintsAreContradictory :: EqConstraints -> Bool
constraintsAreContradictory = (== EqContradiction)

--------- Construction

{- | 'hasSubsumingMember' over raw path lists.

Used by 'isContradicting', which works on un-classed path lists, and by the
tests as the reference the trie-based 'hasSubsumingMember' is checked against.
-}
hasSubsumingMemberListBased :: [Path] -> [Path] -> Bool
hasSubsumingMemberListBased ps1 ps2 =
    any (\p1 -> any (isStrictSubpath p1) ps2) ps1

{- | Check whether a normalized path class forces a path equal to its subpath.

After congruence closure, every subsumption cycle appears as an equality class
containing both a path and one of its strict prefixes. Such a class is
unsatisfiable for finite trees: it would require a subterm to be equal to a
proper descendant of itself.
-}
isContradicting :: [[Path]] -> Bool
isContradicting cs = any (\pec -> hasSubsumingMemberListBased pec pec) cs

{- | Build normalized equality constraints.

This performs equality-class completion, adds path congruences, and detects
contradictions caused by a path being forced equal to one of its strict
subpaths. The implementation is intentionally direct rather than clever because
constraint construction is not the main API boundary; class completion is a
small union-find and the congruence step is the quadratic part.
-}
mkEqConstraints :: [[Path]] -> EqConstraints
mkEqConstraints initialConstraints = case completedConstraints of
    Nothing -> EqContradiction
    Just cs -> EqConstraints $ sort $ map PathEClass cs
  where
    removeTrivial :: (Eq a) => [[a]] -> [[a]]
    removeTrivial = filter (\x -> compareLength x 1 == GT) . map nub

    -- Reason for the extra "complete" in this line:
    -- The first simplification done to the constraints is eclass-completion,
    -- to remove redundancy and shrink things before the very inefficient
    -- addCongruences step (important in tests; less so in realistic input).
    -- The last simplification must also be completion, to give a valid value.
    completedConstraints = fixMaybe round $ complete $ removeTrivial initialConstraints

    round :: [[Path]] -> Maybe [[Path]]
    round cs =
        let cs' = addCongruences cs
            cs'' = complete cs'
         in if isContradicting cs''
                then
                    Nothing
                else
                    Just cs''

    addCongruences :: [[Path]] -> [[Path]]
    addCongruences cs = cs ++ [map (\z -> substSubpath z x y) left | left <- cs, right <- cs, x <- left, y <- right, isStrictSubpath x y]

    -- Merge overlapping classes with a union-find over the distinct paths.
    -- Members and classes come out sorted, so a stable input gives a stable output.
    complete :: (Ord a) => [[a]] -> [[a]]
    complete initialClasses = runST $ do
        let members = Map.fromList (zip (nubOrd (concat initialClasses)) [0 :: Int ..])
        parent <- newListArray (0, Map.size members - 1) [0 .. Map.size members - 1] :: ST s (STUArray s Int Int)
        let find index = do
                above <- readArray parent index
                if above == index
                    then pure index
                    else do
                        root <- find above
                        writeArray parent index root
                        pure root
            union left right = do
                leftRoot <- find left
                rightRoot <- find right
                when (leftRoot /= rightRoot) $ writeArray parent leftRoot rightRoot
        forM_ initialClasses $ \cls -> case map (members Map.!) cls of
            [] -> pure ()
            (first : rest) -> mapM_ (union first) rest
        grouped <- forM (Map.toList members) $ \(member, index) -> (,[member]) <$> find index
        pure $ sort $ map sort $ Map.elems $ Map.fromListWith (++) grouped

---------- Operations

-- | Combine two constraint sets and normalize the result.
combineEqConstraints :: EqConstraints -> EqConstraints -> EqConstraints
combineEqConstraints EqContradiction _ = EqContradiction
combineEqConstraints _ EqContradiction = EqContradiction
combineEqConstraints EmptyConstraints EmptyConstraints = EmptyConstraints
combineEqConstraints ec1 ec2 = combineEqConstraintsMemo ec1 ec2
{-# NOINLINE combineEqConstraints #-}

combineEqConstraintsMemo :: EqConstraints -> EqConstraints -> EqConstraints
combineEqConstraintsMemo = memo2 go
  where
    go ec1 ec2 = mkEqConstraints $ ecsGetPaths ec1 ++ ecsGetPaths ec2
{-# NOINLINE combineEqConstraintsMemo #-}

{- | Descend every path in a constraint set through one child index.

Equality classes with fewer than two remaining paths are dropped immediately:
they no longer constrain anything after the descent.
-}
eqConstraintsDescend :: EqConstraints -> Int -> EqConstraints
eqConstraintsDescend EqContradiction _ = EqContradiction
eqConstraintsDescend EmptyConstraints _ = EmptyConstraints
eqConstraintsDescend (EqConstraints sourceEclasses) i = case mapMaybe (`pathEClassDescendNontrivial` i) sourceEclasses of
    [] -> EmptyConstraints
    [eclass] -> EqConstraints [eclass]
    eclasses -> EqConstraints $ sort eclasses
  where
    pathEClassDescendNontrivial (PathEClass' pt _ _) childIndex =
        let pt' = pathTrieDescend pt childIndex
         in if pathTrieHasAtLeastTwoPaths pt'
                then Just (mkPathEClassFromPathTrie pt')
                else Nothing

{- | Conservative implication check between two constraint sets.

This is intentionally cheaper than rebuilding the combined closure: every
class required by the second set must occur as a subsequence of some class in
the first set. That is sufficient for redundant-edge pruning, but it is not a
complete theorem prover for arbitrary constraint implication.
-}
constraintsImply :: EqConstraints -> EqConstraints -> Bool
constraintsImply EqContradiction _ = True
constraintsImply _ EqContradiction = False
constraintsImply ecs1 ecs2 = all (\cs -> any (isSubsequenceOf cs) (ecsGetPaths ecs1)) (ecsGetPaths ecs2)

-- | Equality classes sorted for constraint propagation, if not contradictory.
subsumptionOrderedEclasses :: EqConstraints -> Maybe [PathEClass]
subsumptionOrderedEclasses EqContradiction = Nothing
subsumptionOrderedEclasses (EqConstraints pecs) = Just $ sortBy completedSubsumptionOrdering pecs

{- | Equality classes sorted for constraint propagation.

Fails on 'EqContradiction': reduction only reaches this after checking that the
combined constraints are satisfiable.
-}
unsafeSubsumptionOrderedEclasses :: EqConstraints -> [PathEClass]
unsafeSubsumptionOrderedEclasses (EqConstraints pecs) = sortBy completedSubsumptionOrdering pecs
unsafeSubsumptionOrderedEclasses EqContradiction = error "unsafeSubsumptionOrderedEclasses: unexpected EqContradiction"

-- | Iterate a partial step function until stable or failed.
fixMaybe :: (Eq a) => (a -> Maybe a) -> a -> Maybe a
fixMaybe f x = case f x of
    Nothing -> Nothing
    Just x'
        | x' == x -> Just x
        | otherwise -> fixMaybe f x'
