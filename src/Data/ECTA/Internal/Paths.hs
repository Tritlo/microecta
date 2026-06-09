{-# LANGUAGE OverloadedStrings #-}

{- | Representations of paths in an FTA, data structures for
  equality constraints over paths, algorithms for saturating these constraints
-}
module Data.ECTA.Internal.Paths (
    Path (.., EmptyPath, ConsPath),
    unPath,
    path,
    Pathable (..),
    pathHeadUnsafe,
    pathTailUnsafe,
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
    constraintsImply,
    subsumptionOrderedEclasses,
    unsafeSubsumptionOrderedEclasses,
) where

import Prelude hiding (round)

import Data.Function (on)
import Data.Hashable (Hashable (..))
import Data.List (groupBy, isSubsequenceOf, nub, sort, sortBy)
import qualified Data.List as List
import Data.Maybe (mapMaybe)
import Data.Monoid (Any (..))
import qualified Data.Text as Text
import GHC.Generics (Generic)

import Data.Equivalence.Monad (classes, desc, equate, runEquivM)

import Data.Memoization (MemoCacheTag (..), memo2)
import Data.Text.Extended.Pretty
import Utility.Fixpoint

-------------------------------------------------------

-----------------------------------------------------------------------
--------------------------- Misc / general ----------------------------
-----------------------------------------------------------------------

flipOrdering :: Ordering -> Ordering
flipOrdering GT = LT
flipOrdering LT = GT
flipOrdering EQ = EQ

-----------------------------------------------------------------------
-------------------------------- Paths --------------------------------
-----------------------------------------------------------------------

-- | Path into an edge's children, represented as child indexes.
data Path = Path ![Int]
    deriving (Eq, Ord, Show, Generic)

-- | Extract the raw child-index list from a @Path@.
unPath :: Path -> [Int]
unPath (Path p) = p

instance Hashable Path

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

-- | First path component. Unsafe on 'EmptyPath'.
pathHeadUnsafe :: Path -> Int
pathHeadUnsafe EmptyPath = error "pathHeadUnsafe: empty path"
pathHeadUnsafe (ConsPath p _) = p

-- | Path without its first component. Unsafe on 'EmptyPath'.
pathTailUnsafe :: Path -> Path
pathTailUnsafe EmptyPath = error "pathTailUnsafe: empty path"
pathTailUnsafe (ConsPath _ ps) = ps

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
    deriving (Eq, Show, Generic)

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

-- | Compare sparse child lists as if they were dense vectors with empty cells.
comparePathTrieChildren :: [(Int, PathTrie)] -> [(Int, PathTrie)] -> Ordering
comparePathTrieChildren [] [] = EQ
comparePathTrieChildren [] _ = LT
comparePathTrieChildren _ [] = GT
comparePathTrieChildren ((i1, pt1) : rest1) ((i2, pt2) : rest2) =
    case compare i1 i2 of
        LT -> LT
        GT -> GT
        EQ -> case compare pt1 pt2 of
            EQ -> comparePathTrieChildren rest1 rest2
            res -> res

instance Ord PathTrie where
    compare EmptyPathTrie EmptyPathTrie = EQ
    compare EmptyPathTrie _ = LT
    compare _ EmptyPathTrie = GT
    compare TerminalPathTrie TerminalPathTrie = EQ
    compare TerminalPathTrie _ = LT
    compare _ TerminalPathTrie = GT
    compare (PathTrieSingleChild i1 pt1) (PathTrieSingleChild i2 pt2)
        | i1 < i2 = LT
        | i1 > i2 = GT
        | otherwise = compare pt1 pt2
    compare (PathTrieSingleChild i1 pt1) (PathTrie ((i2, pt2) : _)) =
        case compare i1 i2 of
            LT -> LT
            GT -> GT
            EQ -> case compare pt1 pt2 of
                LT -> LT
                GT -> GT
                EQ -> LT -- children2 must have a second nonempty
    compare (PathTrieSingleChild _ _) (PathTrie []) =
        error "compare: invalid empty PathTrie children"
    compare a@(PathTrie _) b@(PathTrieSingleChild _ _) = flipOrdering $ compare b a
    compare (PathTrie children1) (PathTrie children2) = comparePathTrieChildren children1 children2

-- | Precondition: No path in the input is a subpath of another
toPathTrie :: [Path] -> PathTrie
toPathTrie [] = EmptyPathTrie
toPathTrie [EmptyPath] = TerminalPathTrie
toPathTrie ps@(firstPath : _) =
    if all (\p -> pathHeadUnsafe p == pathHeadUnsafe firstPath) ps
        then
            PathTrieSingleChild (pathHeadUnsafe firstPath) (toPathTrie $ map pathTailUnsafe ps)
        else
            PathTrie children
  where
    groups =
        groupBy ((==) `on` pathHeadUnsafe) $
            sortBy (compare `on` pathHeadUnsafe) ps

    children =
        [ (pathHeadUnsafe groupHead, toPathTrie $ map pathTailUnsafe group)
        | group@(groupHead : _) <- groups
        ]

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
    deriving (Show, Generic)

instance Eq PathEClass where
    (==) = (==) `on` getPathTrie

instance Ord PathEClass where
    compare = compare `on` getPathTrie

-- | Build or match an equality class from its sorted path list view.
pattern PathEClass :: [Path] -> PathEClass
pattern PathEClass ps <- PathEClass' _ ps
    where
        PathEClass ps = PathEClass' (toPathTrie $ nub ps) (sort $ nub ps)

-- | Extract the paths in an equality class.
unPathEClass :: PathEClass -> [Path]
unPathEClass (PathEClass' _ paths) = paths

instance Pretty PathEClass where
    pretty pec = "{" <> (Text.intercalate "=" $ map pretty $ unPathEClass pec) <> "}"

instance Hashable PathEClass

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

{- | Extends the subsumption ordering to a total ordering by using the default lexicographic
  comparison for incomparable elements.
| TODO: Optimization opportunity: Redundant work in the hasSubsumingMember calls
-}
completedSubsumptionOrdering :: PathEClass -> PathEClass -> Ordering
completedSubsumptionOrdering pec1 pec2
    | hasSubsumingMember pec1 pec2 = LT
    | hasSubsumingMember pec2 pec1 = GT
    --   This next line is some hacky magic. Basically, it means that for the
    --   Hoogle+/TermSearch workload, where there is no subsumption,
    --   constraints will be evaluated in left-to-right order (instead of the default
    --   right-to-left), which for that particular workload produces better
    --   constraint-propagation
    | otherwise = compare pec2 pec1

--------------------------------
---------- Equality constraints
--------------------------------

-- | Equality constraints attached to an ECTA edge.
data EqConstraints
    = EqConstraints
        { getEclasses :: [PathEClass]
        -- ^ Must be sorted
        }
    | EqContradiction
    deriving (Eq, Ord, Show, Generic)

instance Hashable EqConstraints

instance Pretty EqConstraints where
    pretty ecs = "{" <> (Text.intercalate "," $ map pretty (getEclasses ecs)) <> "}"

--------- Destructors and patterns

-- | Unsafe. Internal use only
ecsGetPaths :: EqConstraints -> [[Path]]
ecsGetPaths = map unPathEClass . getEclasses

pattern EmptyConstraints :: EqConstraints
pattern EmptyConstraints = EqConstraints []

-- | Extract equality classes, failing on 'EqContradiction'.
unsafeGetEclasses :: EqConstraints -> [PathEClass]
unsafeGetEclasses EqContradiction = error "unsafeGetEclasses: Illegal argument 'EqContradiction'"
unsafeGetEclasses ecs = getEclasses ecs

-- | Construct constraints without congruence closure or contradiction checks.
rawMkEqConstraints :: [[Path]] -> EqConstraints
rawMkEqConstraints = EqConstraints . map PathEClass

-- | Check whether a constraint set is already contradictory.
constraintsAreContradictory :: EqConstraints -> Bool
constraintsAreContradictory = (== EqContradiction)

--------- Construction

-- | List-based reference implementation for 'hasSubsumingMember'.
hasSubsumingMemberListBased :: [Path] -> [Path] -> Bool
hasSubsumingMemberListBased ps1 ps2 =
    getAny $
        mconcat
            [ Any (isStrictSubpath p1 p2)
            | p1 <- ps1
            , p2 <- ps2
            ]

{- | The real contradiction condition is a cycle in the subsumption ordering.
  But, after congruence closure, this will reduce into a self-cycle in the subsumption ordering.

  TODO; Prove this.
-}
isContradicting :: [[Path]] -> Bool
isContradicting cs = any (\pec -> hasSubsumingMemberListBased pec pec) cs

{- | Build normalized equality constraints.

This performs equality-class completion, adds path congruences, and detects
contradictions caused by a path being forced equal to one of its strict
subpaths. The implementation is intentionally direct rather than clever because
constraint construction is not the main @microecta@ API boundary, and the
@equivalence@ package keeps this path fast enough for current workloads.
-}
mkEqConstraints :: [[Path]] -> EqConstraints
mkEqConstraints initialConstraints = case completedConstraints of
    Nothing -> EqContradiction
    Just cs -> EqConstraints $ sort $ map PathEClass cs
  where
    removeTrivial :: (Eq a) => [[a]] -> [[a]]
    removeTrivial = filter (\x -> length x > 1) . map nub

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

    assertEquivs [] = return []
    assertEquivs (x : xs) = mapM (equate x) xs

    complete :: (Ord a) => [[a]] -> [[a]]
    complete initialClasses = runEquivM (: []) (++) $ do
        mapM_ assertEquivs initialClasses
        mapM desc =<< classes

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
eqConstraintsDescend ecs i = case mapMaybe (`pathEClassDescendNontrivial` i) (getEclasses ecs) of
    [] -> EmptyConstraints
    eclasses -> EqConstraints $ sort eclasses
  where
    pathEClassDescendNontrivial (PathEClass' pt _) childIndex =
        let pt' = pathTrieDescend pt childIndex
         in if pathTrieHasAtLeastTwoPaths pt'
                then Just (mkPathEClassFromPathTrie pt')
                else Nothing

-- A faster implementation would be: Merge the eclasses of both, run mkEqConstraints (or at least do eclass completion),
-- check result equal to ecs2

-- | Conservative implication check between two constraint sets.
constraintsImply :: EqConstraints -> EqConstraints -> Bool
constraintsImply EqContradiction _ = True
constraintsImply _ EqContradiction = False
constraintsImply ecs1 ecs2 = all (\cs -> any (isSubsequenceOf cs) (ecsGetPaths ecs1)) (ecsGetPaths ecs2)

-- | Equality classes sorted for constraint propagation, if not contradictory.
subsumptionOrderedEclasses :: EqConstraints -> Maybe [PathEClass]
subsumptionOrderedEclasses ecs = case ecs of
    EqContradiction -> Nothing
    EqConstraints pecs -> Just $ sortBy completedSubsumptionOrdering pecs

-- | Variant of 'subsumptionOrderedEclasses' that fails on contradiction.
unsafeSubsumptionOrderedEclasses :: EqConstraints -> [PathEClass]
unsafeSubsumptionOrderedEclasses (EqConstraints pecs) = sortBy completedSubsumptionOrdering pecs
unsafeSubsumptionOrderedEclasses EqContradiction = error $ "unsafeSubsumptionOrderedEclasses: unexpected EqContradiction"
