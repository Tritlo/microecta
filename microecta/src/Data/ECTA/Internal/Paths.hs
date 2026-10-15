{-# LANGUAGE OverloadedStrings #-}

{- | Representations of paths in an FTA, data structures for
  equality constraints over paths, algorithms for saturating these constraints
-}
module Data.ECTA.Internal.Paths (
    Path (.., EmptyPath, ConsPath),
    unPath,
    path,
    Pathable (..),
    isSubpath,
    isStrictSubpath,
    substSubpath,
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
    fitsArity,
    constraintsImply,
    subsumptionOrderedEclasses,
    unsafeSubsumptionOrderedEclasses,
) where

import Control.Monad (forM, forM_, when)
import Control.Monad.ST (ST, runST)
import Data.Array.ST (STUArray, newListArray, readArray, writeArray)
import Data.Function (on)
import Data.Hashable (Hashable (..))
import Data.List (groupBy, isSubsequenceOf, sort, sortBy, tails)
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text

import Data.Memoization (MemoCacheTag (..), memo2)
import Data.Text.Extended.Pretty
import Utility.Fixpoint

-------------------------------------------------------

-----------------------------------------------------------------------
--------------------------- Misc / general ----------------------------
-----------------------------------------------------------------------

-----------------------------------------------------------------------
-------------------------------- Paths --------------------------------
-----------------------------------------------------------------------

-- | Path into an edge's children, represented as child indexes.
data Path = Path ![Int]
    deriving (Eq, Ord, Show)

-- | Extract the raw child-index list from a @Path@.
unPath :: Path -> [Int]
unPath (Path p) = p

instance Hashable Path where
    hashWithSalt salt (Path components) = salt `hashWithSalt` components

-- | Build a @Path@ from child indexes.
path :: [Int] -> Path
path = Path

{-# COMPLETE EmptyPath, ConsPath #-}

pattern EmptyPath :: Path
pattern EmptyPath = Path []

pattern ConsPath :: Int -> Path -> Path
pattern ConsPath p ps <- Path (p : (Path -> ps))
    where
        ConsPath p (Path ps) = Path (p : ps)

instance Pretty Path where
    pretty (Path ps) = Text.intercalate "." (map (Text.pack . show) ps)

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

{- | Read `substSubpath p1 p2 p3` as `[p1/p2]p3`

@substSubpath replacement toReplace target@ takes @toReplace@, a prefix of
@target@, and returns a new path in which @toReplace@ has been replaced by
@replacement@.

 Undefined if toReplace is not a prefix of target
-}
substSubpath :: Path -> Path -> Path -> Path
substSubpath replacement toReplace target = Path $ (unPath replacement) ++ drop (length $ unPath toReplace) (unPath target)

--------------------------------------------------------------------------
---------------------------- Using paths ---------------------------------
--------------------------------------------------------------------------

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

-----------------------------------------------------------------------
---------------------------- Path tries -------------------------------
-----------------------------------------------------------------------

-- | Largest child index present in a trie node, if any.
getMaxNonemptyIndex :: PathTrie -> Maybe Int
getMaxNonemptyIndex EmptyPathTrie = Nothing
getMaxNonemptyIndex TerminalPathTrie = Nothing
getMaxNonemptyIndex (PathTrieSingleChild i _) = Just i
getMaxNonemptyIndex (PathTrie children) = Just $ fst (last children)

---------------------
------- Path tries
---------------------

{- | Trie of paths used to index equality constraints.

Most constraint tries in the original workloads are either empty, terminal, or
one path component wide for many levels.  `PathTrieSingleChild` keeps that hot
case compact. The multi-child case used to be a dense child table, which made
lookup cheap but forced GHC to optimise large recursive structure code. The
sparse representation keeps only non-empty children in sorted order. That
keeps union, ordering, and subsumption as linear merges over present children,
while avoiding the `-O2` compile-time memory blow-up from the dense code.

Invariant for @PathTrie@: children are sorted by component, contain no
@EmptyPathTrie@ entries, and contain at least two children.  Constructors are
exported for tests and compatibility, so functions that rebuild multi-child
tries should restore that invariant before returning.
-}
data PathTrie
    = -- | No paths.
      EmptyPathTrie
    | -- | Exactly the empty path.
      TerminalPathTrie
    | -- | A compact node with exactly one child at the given path component.
      PathTrieSingleChild {-# UNPACK #-} !Int !PathTrie
    | -- | Sparse multi-child node. See the invariant on @PathTrie@.
      PathTrie ![(Int, PathTrie)]
    deriving (Eq, Show)

instance Hashable PathTrie where
    hashWithSalt salt EmptyPathTrie = salt `hashWithSalt` (0 :: Int)
    hashWithSalt salt TerminalPathTrie = salt `hashWithSalt` (1 :: Int)
    hashWithSalt salt (PathTrieSingleChild i pt) =
        salt `hashWithSalt` (2 :: Int) `hashWithSalt` i `hashWithSalt` pt
    hashWithSalt salt (PathTrie children) =
        List.foldl' hashWithSalt (salt `hashWithSalt` (3 :: Int)) children

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
    go seenOne (PathTrieSingleChild _ pt) = go seenOne pt
    go seenOne (PathTrie children) = goChildren seenOne children

    goChildren :: Bool -> [(Int, PathTrie)] -> Bool
    goChildren _ [] = False
    goChildren seenOne ((_, pt) : rest)
        | go seenOne pt = True
        | pathTrieHasAnyPath pt =
            if seenOne
                then True
                else goChildren True rest
        | otherwise = goChildren seenOne rest

    pathTrieHasAnyPath :: PathTrie -> Bool
    pathTrieHasAnyPath EmptyPathTrie = False
    pathTrieHasAnyPath TerminalPathTrie = True
    pathTrieHasAnyPath (PathTrieSingleChild _ pt) = pathTrieHasAnyPath pt
    pathTrieHasAnyPath (PathTrie children) = any (pathTrieHasAnyPath . snd) children

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
comparePathTrieBranches depth choices1 (PathTrieSingleChild i1 pt1) choices2 (PathTrieSingleChild i2 pt2) =
    case compare i1 i2 of
        EQ -> comparePathTrieBranches (depth + 1) choices1 pt1 choices2 pt2
        result -> result
comparePathTrieBranches _ _ (PathTrieSingleChild _ _) _ (PathTrie []) =
    error "comparePathTries: invalid empty child list"
comparePathTrieBranches depth choices1 (PathTrieSingleChild i1 pt1) choices2 (PathTrie ((i2, pt2) : rest2)) =
    case compare i1 i2 of
        EQ ->
            comparePathTrieBranches
                (depth + 1)
                choices1
                pt1
                (rememberPathTrieChoice depth rest2 choices2)
                pt2
        result -> result
comparePathTrieBranches _ _ (PathTrie []) _ _ =
    error "comparePathTries: invalid empty child list"
comparePathTrieBranches depth choices1 (PathTrie ((i1, pt1) : rest1)) choices2 (PathTrieSingleChild i2 pt2) =
    case compare i1 i2 of
        EQ ->
            comparePathTrieBranches
                (depth + 1)
                (rememberPathTrieChoice depth rest1 choices1)
                pt1
                choices2
                pt2
        result -> result
comparePathTrieBranches _ _ _ _ (PathTrie []) =
    error "comparePathTries: invalid empty child list"
comparePathTrieBranches depth choices1 (PathTrie ((i1, pt1) : rest1)) choices2 (PathTrie ((i2, pt2) : rest2)) =
    case compare i1 i2 of
        EQ ->
            comparePathTrieBranches
                (depth + 1)
                (rememberPathTrieChoice depth rest1 choices1)
                pt1
                (rememberPathTrieChoice depth rest2 choices2)
                pt2
        result -> result

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
            PathTrieSingleChild (headOf firstPath) (toPathTrie $ map tailOf ps)
        else
            PathTrie children
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
fromPathTrie (PathTrieSingleChild i pt) = map (ConsPath i) $ fromPathTrie pt
fromPathTrie (PathTrie children) =
    concatMap (\(i, pt) -> map (ConsPath i) $ fromPathTrie pt) children

-- | Descend through one child index, returning 'EmptyPathTrie' if absent.
pathTrieDescend :: PathTrie -> Int -> PathTrie
pathTrieDescend EmptyPathTrie _ = EmptyPathTrie
pathTrieDescend TerminalPathTrie _ = EmptyPathTrie
pathTrieDescend (PathTrie children) i =
    case lookup i children of
        Nothing -> EmptyPathTrie
        Just pt -> pt
pathTrieDescend (PathTrieSingleChild j pt') i
    | i == j = pt'
    | otherwise = EmptyPathTrie

--------------------------------------------------------------------------
---------------------- Equality constraints over paths -------------------
--------------------------------------------------------------------------

---------------------------
---------- Path E-classes
---------------------------

{- | Equality class of paths.

The trie drives subsumption and descent; the path list keeps the older public
API and reduction code cheap to read. Values built by @PathEClass@ and
@mkPathEClassFromPathTrie@ keep the two views consistent.
-}
data PathEClass = PathEClass'
    { getPathTrie :: !PathTrie
    , getOrigPaths :: [Path]
    }
    deriving (Show)

instance Eq PathEClass where
    (==) = (==) `on` getPathTrie

-- | Compare the cached sorted path lists instead of rebuilding them from tries.
instance Ord PathEClass where
    compare = compare `on` getOrigPaths

-- | Build or match an equality class from its sorted path list view.
pattern PathEClass :: [Path] -> PathEClass
pattern PathEClass ps <- PathEClass' _ ps
    where
        PathEClass ps =
            let paths = Set.toAscList $ Set.fromList ps
             in PathEClass' (toPathTrie paths) paths

-- | Extract the paths in an equality class.
unPathEClass :: PathEClass -> [Path]
unPathEClass (PathEClass' _ paths) = paths

instance Pretty PathEClass where
    pretty pec = "{" <> (Text.intercalate "=" $ map pretty $ unPathEClass pec) <> "}"

instance Hashable PathEClass where
    hashWithSalt salt = hashWithSalt salt . getPathTrie

-- | Build an equality class from a trie, deriving the path list lazily.
mkPathEClassFromPathTrie :: PathTrie -> PathEClass
mkPathEClassFromPathTrie pt = PathEClass' pt (fromPathTrie pt)

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
    go (PathTrieSingleChild i1 pt1) (PathTrieSingleChild i2 pt2) =
        if i1 == i2
            then
                go pt1 pt2
            else
                False
    go (PathTrieSingleChild i1 pt1) (PathTrie children2) = case lookup i1 children2 of
        Nothing -> False
        Just pt2 -> go pt1 pt2
    go (PathTrie children1) (PathTrieSingleChild i2 pt2) = case lookup i2 children1 of
        Nothing -> False
        Just pt1 -> go pt1 pt2
    go (PathTrie children1) (PathTrie children2) = anyMatchingChild children1 children2

    -- Both child lists are sorted, so this keeps the old dense-table behaviour
    -- without scanning absent indexes or doing repeated linear lookups.
    anyMatchingChild [] _ = False
    anyMatchingChild _ [] = False
    anyMatchingChild left@((i1, pt1) : rest1) right@((i2, pt2) : rest2) =
        case compare i1 i2 of
            LT -> anyMatchingChild rest1 right
            GT -> anyMatchingChild left rest2
            EQ -> go pt1 pt2 || anyMatchingChild rest1 rest2

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
        "{" <> (Text.intercalate "," $ map pretty eclasses) <> "}"

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

{- | Whether an edge with this many children can meet the classes. The
classes must not be contradictory, no path can have a negative index, and
every path must start at an existing child. A deeper index is checked where
the path meets the edges of the child.
-}
fitsArity :: Int -> EqConstraints -> Bool
fitsArity _ EqContradiction = False
fitsArity count constraints = all (all fits . unPathEClass) (unsafeGetEclasses constraints)
  where
    fits (Path []) = True
    fits (Path indices@(first : _)) = first < count && all (>= 0) indices

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

Merge the overlapping classes, add the path congruences, and find the
contradictions. A class that holds a path and one of its strict subpaths is a
contradiction. A small union-find merges the classes. The congruence step
costs the most, and it repeats until the classes do not change.

One congruence step is polynomial in the number of paths of the current
classes. The closure itself can be exponentially larger than the input: the
classes @[0^j, 0^(j-1) ++ [1]]@ for @j@ from 1 to @n@ have @2n@ paths, and
their closure has @2^(n+1) - 2@ paths. So the cost is polynomial in the size of
the closure, not in the size of the input. A set in which no path is a strict
prefix of another is already closed, and the congruence step then adds
nothing.
-}
mkEqConstraints :: [[Path]] -> EqConstraints
mkEqConstraints initialConstraints = case completedConstraints of
    Nothing -> EqContradiction
    Just cs -> EqConstraints $ sort $ map (PathEClass . Set.toAscList) cs
  where
    removeTrivial :: [Set Path] -> [Set Path]
    removeTrivial = filter ((> 1) . Set.size)

    -- Reason for the extra "complete" in this line:
    -- The first simplification done to the constraints is eclass-completion,
    -- to remove redundancy and shrink the constraints before the very inefficient
    -- addCongruences step (important in tests; less so in realistic input).
    -- The last simplification must also be completion, to give a valid value.
    completedConstraints = fixMaybe congruenceStep $ complete $ removeTrivial $ map Set.fromList initialConstraints

    -- One step of congruence closure. It fails when a class forces a path to be
    -- equal to one of its strict subpaths.
    congruenceStep :: [Set Path] -> Maybe [Set Path]
    congruenceStep classes = do
        let closed = complete $ addCongruences classes
        when (any contradicting closed) Nothing
        pure closed

    contradicting :: Set Path -> Bool
    contradicting paths = any (\p -> any (isStrictSubpath p) paths) paths

    -- Merge overlapping classes with a union-find over the distinct paths.
    -- Classes come out sorted, so a stable input gives a stable output.
    complete :: [Set Path] -> [Set Path]
    complete initialClasses = runST $ do
        let members = Map.fromDistinctAscList (zip (Set.toAscList (Set.unions initialClasses)) [0 :: Int ..])
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
        forM_ initialClasses $ \cls -> case map (members Map.!) (Set.toList cls) of
            [] -> pure ()
            (first : rest) -> mapM_ (union first) rest
        -- Members are visited in ascending order, so each group collects them in descending order.
        grouped <- forM (Map.toList members) $ \(member, index) -> (,[member]) <$> find index
        pure $ sort $ map Set.fromDistinctDescList $ Map.elems $ Map.fromListWith (++) grouped

    -- If x is in a class and x ++ s is a recorded path, then z ++ s equals
    -- x ++ s for every z in that class. Every x with the same suffix s forces
    -- the same class, so one class for each distinct suffix is enough. In
    -- ascending order, the strict extensions of a path follow it directly.
    addCongruences :: [Set Path] -> [Set Path]
    addCongruences cs
        | Map.null suffixes = cs
        | otherwise = cs ++ [Set.map (`extend` suffix) left | left <- cs, suffix <- Set.toList (foldMap suffixesOf left)]
      where
        suffixes =
            Map.fromList
                [ (Path x, Set.fromList [Path (drop (length x) y) | Path y <- extensions])
                | Path x : rest <- tails (Set.toAscList (Set.unions cs))
                , let extensions = takeWhile (isStrictSubpath (Path x)) rest
                , not (null extensions)
                ]
        suffixesOf x = Map.findWithDefault Set.empty x suffixes
        extend (Path prefix) (Path suffix) = Path (prefix ++ suffix)

---------- Operations

-- | Combine two constraint sets and normalize the result.
combineEqConstraints :: EqConstraints -> EqConstraints -> EqConstraints
combineEqConstraints EqContradiction _ = EqContradiction
combineEqConstraints _ EqContradiction = EqContradiction
combineEqConstraints EmptyConstraints EmptyConstraints = EmptyConstraints
combineEqConstraints ec1 ec2 = combineEqConstraintsMemo ec1 ec2
{-# NOINLINE combineEqConstraints #-}

combineEqConstraintsMemo :: EqConstraints -> EqConstraints -> EqConstraints
combineEqConstraintsMemo = memo2 (NameTag "combineEqConstraints") go
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
    pathEClassDescendNontrivial (PathEClass' pt _) childIndex =
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
unsafeSubsumptionOrderedEclasses EqContradiction = error $ "unsafeSubsumptionOrderedEclasses: unexpected EqContradiction"
