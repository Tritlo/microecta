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
    smallestNonempty,
    largestNonempty,
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
import Data.Monoid (Any (..))
import qualified Data.Text as Text
import Data.Vector (Vector)
import qualified Data.Vector as Vector
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

data Path = Path ![Int]
    deriving (Eq, Ord, Show, Generic)

unPath :: Path -> [Int]
unPath (Path p) = p

instance Hashable Path

path :: [Int] -> Path
path = Path

{-# COMPLETE EmptyPath, ConsPath #-}

pattern EmptyPath :: Path
pattern EmptyPath = Path []

pattern ConsPath :: Int -> Path -> Path
pattern ConsPath p ps <- Path (p : (Path -> ps))
    where
        ConsPath p (Path ps) = Path (p : ps)

pathHeadUnsafe :: Path -> Int
pathHeadUnsafe (Path ps) = head ps

pathTailUnsafe :: Path -> Path
pathTailUnsafe (Path ps) = Path (tail ps)

instance Pretty Path where
    pretty (Path ps) = Text.intercalate "." (map (Text.pack . show) ps)

isSubpath :: Path -> Path -> Bool
isSubpath EmptyPath _ = True
isSubpath (ConsPath p1 ps1) (ConsPath p2 ps2)
    | p1 == p2 = isSubpath ps1 ps2
isSubpath _ _ = False

isStrictSubpath :: Path -> Path -> Bool
isStrictSubpath EmptyPath EmptyPath = False
isStrictSubpath EmptyPath _ = True
isStrictSubpath (ConsPath p1 ps1) (ConsPath p2 ps2)
    | p1 == p2 = isStrictSubpath ps1 ps2
isStrictSubpath _ _ = False

{- | Read `substSubpath p1 p2 p3` as `[p1/p2]p3`

`substSubpath replacement toReplace target` takes `toReplace`, a prefix of target,
 and returns a new path in which `toReplace` has been replaced by `replacement`.

 Undefined if toReplace is not a prefix of target
-}
substSubpath :: Path -> Path -> Path -> Path
substSubpath replacement toReplace target = Path $ (unPath replacement) ++ drop (length $ unPath toReplace) (unPath target)

--------------------------------------------------------------------------
---------------------------- Using paths ---------------------------------
--------------------------------------------------------------------------

{- | TODO: Should this be redone as a lens-library traversal?
| TODO: I am unhappy about this Emptyable design; makes one question whether
        this should be a typeclass at all. (Terms/ECTAs differ in that
        there is always an ECTA Node that represents the value at a path)
-}
class Pathable t t' | t -> t' where
    type Emptyable t'
    getPath :: Path -> t -> Emptyable t'
    getAllAtPath :: Path -> t -> [t']
    modifyAtPath :: (t' -> t') -> Path -> t -> t

-----------------------------------------------------------------------
---------------------------- Path tries -------------------------------
-----------------------------------------------------------------------

---------------------
------- Generic-ish utility functions
---------------------

-- | Precondition: A nonempty cell exists
smallestNonempty :: Vector PathTrie -> Int
smallestNonempty v =
    Vector.ifoldr
        ( \i pt oldMin -> case pt of
            EmptyPathTrie -> oldMin
            _ -> i
        )
        maxBound
        v

-- | Precondition: A nonempty cell exists
largestNonempty :: Vector PathTrie -> Int
largestNonempty v =
    Vector.ifoldl
        ( \oldMin i pt -> case pt of
            EmptyPathTrie -> oldMin
            _ -> i
        )
        minBound
        v

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
case compact.  The multi-child case used to be a dense `Vector PathTrie`, which
made lookup cheap but forced GHC to optimise large vector-heavy recursive code.
The sparse representation keeps only non-empty children in sorted order.  That
keeps union, ordering, and subsumption as linear merges over present children,
while avoiding the `-O2` compile-time memory blow-up from the dense vector code.

Invariant for `PathTrie`: children are sorted by component, contain no
`EmptyPathTrie` entries, and contain at least two children.  Constructors are
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
    | -- | Sparse multi-child node. See the invariant on `PathTrie`.
      PathTrie ![(Int, PathTrie)]
    deriving (Eq, Show, Generic)

instance Hashable PathTrie where
    hashWithSalt salt EmptyPathTrie = salt `hashWithSalt` (0 :: Int)
    hashWithSalt salt TerminalPathTrie = salt `hashWithSalt` (1 :: Int)
    hashWithSalt salt (PathTrieSingleChild i pt) =
        salt `hashWithSalt` (2 :: Int) `hashWithSalt` i `hashWithSalt` pt
    hashWithSalt salt (PathTrie children) =
        List.foldl' hashWithSalt (salt `hashWithSalt` (3 :: Int)) children

isEmptyPathTrie :: PathTrie -> Bool
isEmptyPathTrie EmptyPathTrie = True
isEmptyPathTrie _ = False

isTerminalPathTrie :: PathTrie -> Bool
isTerminalPathTrie TerminalPathTrie = True
isTerminalPathTrie _ = False

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

fromPathTrie :: PathTrie -> [Path]
fromPathTrie EmptyPathTrie = []
fromPathTrie TerminalPathTrie = [EmptyPath]
fromPathTrie (PathTrieSingleChild i pt) = map (ConsPath i) $ fromPathTrie pt
fromPathTrie (PathTrie children) =
    concatMap (\(i, pt) -> map (ConsPath i) $ fromPathTrie pt) children

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

data PathEClass = PathEClass'
    { getPathTrie :: !PathTrie
    , getOrigPaths :: [Path] -- Intentionally lazy because
    -- not available when calling `mkPathEClassFromPathTrie`
    }
    deriving (Show, Generic)

instance Eq PathEClass where
    (==) = (==) `on` getPathTrie

instance Ord PathEClass where
    compare = compare `on` getPathTrie

{- | TODO: This pattern (and the caching of the original path list) is a temporary affair
        until we convert all clients of PathEclass to fully be based on tries
-}
pattern PathEClass :: [Path] -> PathEClass
pattern PathEClass ps <- PathEClass' _ ps
    where
        PathEClass ps = PathEClass' (toPathTrie $ nub ps) (sort $ nub ps)

unPathEClass :: PathEClass -> [Path]
unPathEClass (PathEClass' _ paths) = paths

instance Pretty PathEClass where
    pretty pec = "{" <> (Text.intercalate "=" $ map pretty $ unPathEClass pec) <> "}"

instance Hashable PathEClass

mkPathEClassFromPathTrie :: PathTrie -> PathEClass
mkPathEClassFromPathTrie pt = PathEClass' pt (fromPathTrie pt)

pathEClassDescend :: PathEClass -> Int -> PathEClass
pathEClassDescend (PathEClass' pt _) i = mkPathEClassFromPathTrie $ pathTrieDescend pt i

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

    -- Both child lists are sorted, so this keeps the dense-vector behaviour
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

unsafeGetEclasses :: EqConstraints -> [PathEClass]
unsafeGetEclasses EqContradiction = error "unsafeGetEclasses: Illegal argument 'EqContradiction'"
unsafeGetEclasses ecs = getEclasses ecs

rawMkEqConstraints :: [[Path]] -> EqConstraints
rawMkEqConstraints = EqConstraints . map PathEClass

constraintsAreContradictory :: EqConstraints -> Bool
constraintsAreContradictory = (== EqContradiction)

--------- Construction

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

-- Contains an inefficient implementation of the congruence closure algorithm
mkEqConstraints :: [[Path]] -> EqConstraints
mkEqConstraints initialConstraints = case completedConstraints of
    Nothing -> EqContradiction
    Just cs -> EqConstraints $ sort $ map PathEClass cs
  where
    removeTrivial :: (Eq a) => [[a]] -> [[a]]
    removeTrivial = filter (\x -> length x > 1) . map nub

    -- Reason for the extra "complete" in this line:
    -- The first simplification done to the constraints is eclass-completion,
    -- to remove redundancy and shrink things before the very inefficienc
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

combineEqConstraints :: EqConstraints -> EqConstraints -> EqConstraints
combineEqConstraints = memo2 (NameTag "combineEqConstraints") go
  where
    go EqContradiction _ = EqContradiction
    go _ EqContradiction = EqContradiction
    go ec1 ec2 = mkEqConstraints $ ecsGetPaths ec1 ++ ecsGetPaths ec2
{-# NOINLINE combineEqConstraints #-}

eqConstraintsDescend :: EqConstraints -> Int -> EqConstraints
eqConstraintsDescend EqContradiction _ = EqContradiction
eqConstraintsDescend ecs i = EqConstraints $ sort $ map (`pathEClassDescend` i) (getEclasses ecs)

-- A faster implementation would be: Merge the eclasses of both, run mkEqConstraints (or at least do eclass completion),
-- check result equal to ecs2
constraintsImply :: EqConstraints -> EqConstraints -> Bool
constraintsImply EqContradiction _ = True
constraintsImply _ EqContradiction = False
constraintsImply ecs1 ecs2 = all (\cs -> any (isSubsequenceOf cs) (ecsGetPaths ecs1)) (ecsGetPaths ecs2)

subsumptionOrderedEclasses :: EqConstraints -> Maybe [PathEClass]
subsumptionOrderedEclasses ecs = case ecs of
    EqContradiction -> Nothing
    EqConstraints pecs -> Just $ sortBy completedSubsumptionOrdering pecs

unsafeSubsumptionOrderedEclasses :: EqConstraints -> [PathEClass]
unsafeSubsumptionOrderedEclasses (EqConstraints pecs) = sortBy completedSubsumptionOrdering pecs
unsafeSubsumptionOrderedEclasses EqContradiction = error $ "unsafeSubsumptionOrderedEclasses: unexpected EqContradiction"
