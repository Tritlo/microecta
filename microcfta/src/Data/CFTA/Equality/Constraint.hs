{-# LANGUAGE OverloadedStrings #-}

{- | Representations of paths in an FTA, data structures for equality
constraints over paths, and algorithms for saturating these constraints.

The 'Data.CFTA.Constraint.Constraint' instance lives with the class.
-}
module Data.CFTA.Equality.Constraint (
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
    EqConstraints (.., EmptyConstraints),
    unsafeGetEclasses,
    isContradicting,
    mkEqConstraints,
    combineEqConstraints,
    eqConstraintsDescend,
    constraintsAreContradictory,
    fitsArity,
    subsumptionOrderedEclasses,
    unsafeSubsumptionOrderedEclasses,
) where

import Control.Monad (forM, forM_, when)
import Control.Monad.ST (ST, runST)
import Data.Array.ST (STUArray, newListArray, readArray, writeArray)
import Data.Foldable (toList)
import Data.Function (on)
import Data.Hashable (Hashable (..))
import qualified Data.IntMap.Lazy as IntMap
import Data.List (sort, sortBy, tails)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Sequence as Sequence
import Data.Set (Set)
import qualified Data.Set as Set

import Data.CFTA.Index (Arity (..))
import Data.CFTA.Interned.Memo (memo2)
import Data.CFTA.Path (ChildIndex (..), Path (..), isStrictSubpath)

-------------------------------------------------------

-----------------------------------------------------------------------
--------------------------- Misc / general ----------------------------
-----------------------------------------------------------------------

-----------------------------------------------------------------------
-------------------------------- Paths --------------------------------
-----------------------------------------------------------------------

-- | Largest child index present in a trie node, if any.
getMaxNonemptyIndex :: PathTrie -> Maybe ChildIndex
getMaxNonemptyIndex EmptyPathTrie = Nothing
getMaxNonemptyIndex TerminalPathTrie = Nothing
getMaxNonemptyIndex (PathTrie children) = ChildIndex . fst <$> IntMap.lookupMax children

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
            PathTrie
                $ IntMap.map (toPathTrie . toList)
                $ IntMap.fromListWith (flip (<>)) [(headOf p, Sequence.singleton $ tailOf p) | p <- ps]
  where
    headOf (ConsPath (ChildIndex i) _) = i
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
    concatMap (\(i, pt) -> map (ConsPath (ChildIndex i)) $ fromPathTrie pt) (IntMap.toAscList children)

-- | Descend through one child index, returning 'EmptyPathTrie' if absent.
pathTrieDescend :: PathTrie -> ChildIndex -> PathTrie
pathTrieDescend EmptyPathTrie _ = EmptyPathTrie
pathTrieDescend TerminalPathTrie _ = EmptyPathTrie
pathTrieDescend (PathTrie children) (ChildIndex i) =
    IntMap.findWithDefault EmptyPathTrie i children

--------------------------------------------------------------------------
---------------------- Equality constraints over paths -------------------
--------------------------------------------------------------------------

---------------------------
---------- Path E-classes
---------------------------

-- TODO: Use set for clearer representation, consider sorted lists for
-- performance. Ordering classes compares two sets, which is slower than
-- comparing two sorted lists (the sort/path-eclasses rows of micro-bench).

{- | An equality class: a set of paths whose subterms must be equal.

The set is the class. The trie holds the same paths for subsumption and
descent, and the hash is computed at most once, because every edge that
carries the class hashes it when it is interned. In values built by
@PathEClass@ and @mkPathEClassFromPathTrie@, the set and the trie hold the
same paths.
-}
data PathEClass = PathEClass'
    { getPathTrie :: !PathTrie
    , getPathSet :: Set Path
    -- ^ Lazy: a class that descent makes builds its set only when it is read.
    , getPathHash :: Int
    -- ^ Lazy: a class that is only descended or compared never pays for it.
    }

instance Show PathEClass where
    showsPrec precedence pec = showParen (precedence > 10) $ showString "PathEClass " . showsPrec 11 (getPathSet pec)

instance Eq PathEClass where
    (==) = (==) `on` getPathTrie

-- | Order classes by their sets, which compare as their ascending path lists.
instance Ord PathEClass where
    compare = compare `on` getPathSet

-- | Build or match an equality class from its set of paths.
pattern PathEClass :: Set Path -> PathEClass
pattern PathEClass paths <- PathEClass' _ paths _
  where
    PathEClass paths =
        let trie = toPathTrie $ Set.toAscList paths
         in PathEClass' trie paths (hash trie)

-- | The paths of an equality class.
unPathEClass :: PathEClass -> Set Path
unPathEClass = getPathSet

instance Hashable PathEClass where
    hashWithSalt salt = hashWithSalt salt . getPathHash

-- | Build an equality class from a trie, deriving the set lazily.
mkPathEClassFromPathTrie :: PathTrie -> PathEClass
mkPathEClassFromPathTrie pt = PathEClass' pt (Set.fromDistinctAscList $ fromPathTrie pt) (hash pt)

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

{- | Ordering used when choosing constraint-propagation order.

Strict subsumption comes first: if one equality class contains a path that is a
strict prefix of a path in another class, the shorter one must be processed
before the longer one. Incomparable classes use the reversed order of their
sorted path lists. That tie-break keeps term-search-shaped workloads in
left-to-right propagation order. With the forward order, the term-search
benchmark @micro-bench@ runs 0.6% more instructions, and the other benchmarks
do not change.

'hasSubsumingMember' is transitive on every class list that 'mkEqConstraints',
'combineEqConstraints', or 'eqConstraintsDescend' returns. If a path @a@ of @A@
has the extension @a ++ s@ in @B@, and a path @b@ of @B@ has the extension
@b ++ t@ in @C@, the congruence closure puts @(a ++ s) ++ t@ in @C@. The check
for contradictions makes the relation irreflexive, so it has no cycle, and
'sortBy' puts a class before every class that it subsumes. A class list built
with the 'EqConstraints' constructor has no such guarantee.
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
    = {- | Equality classes over paths into the edge's children. Sorted by
      'mkEqConstraints'; the constructor itself does not sort.
      -}
      EqConstraints [PathEClass]
    | -- | The classes forced a path to equal one of its strict subpaths.
      EqContradiction
    deriving (Eq, Ord, Show)

instance Hashable EqConstraints where
    hashWithSalt salt (EqConstraints eclasses) =
        salt `hashWithSalt` (0 :: Int) `hashWithSalt` eclasses
    hashWithSalt salt EqContradiction =
        salt `hashWithSalt` (1 :: Int)

--------- Destructors and patterns

pattern EmptyConstraints :: EqConstraints
pattern EmptyConstraints = EqConstraints []

-- | Extract equality classes, failing on 'EqContradiction'.
unsafeGetEclasses :: EqConstraints -> [PathEClass]
unsafeGetEclasses EqContradiction = error "unsafeGetEclasses: Illegal argument 'EqContradiction'"
unsafeGetEclasses (EqConstraints eclasses) = eclasses

{- | Whether an edge with this many children can meet the classes. The
classes must not be contradictory, no path can have a negative index, and
every path must start at an existing child. A deeper index is checked where
the path meets the edges of the child.
-}
fitsArity :: Arity -> EqConstraints -> Bool
fitsArity _ EqContradiction = False
fitsArity (Arity count) constraints = all (all fits . unPathEClass) (unsafeGetEclasses constraints)
  where
    fits (Path []) = True
    fits (Path indices@(ChildIndex first : _)) = first < count && all (>= 0) indices

-- | Check whether a constraint set is already contradictory.
constraintsAreContradictory :: EqConstraints -> Bool
constraintsAreContradictory = (== EqContradiction)

--------- Construction

{- | Check whether a normalized path class forces a path equal to its subpath.

After congruence closure, every subsumption cycle appears as an equality class
containing both a path and one of its strict prefixes: subsumption is transitive
on a closed class list (see 'completedSubsumptionOrdering'), so a cycle through
a class @A@ gives @A@ a path and one of its strict extensions. Such a class is
unsatisfiable for finite trees: it would require a subterm to be equal to a
proper descendant of itself. The congruence step checks the closed classes of
every step, so the last check sees the fixed point.
-}
isContradicting :: [Set Path] -> Bool
isContradicting = any (\paths -> any (\p -> any (isStrictSubpath p) paths) paths)

{- | Build normalized equality constraints.

This performs equality-class completion, adds path congruences, and detects
contradictions caused by a path being forced equal to one of its strict
subpaths. The implementation is intentionally direct rather than clever because
constraint construction is not the main API boundary. Class completion is a
small union-find. The congruence step is the most expensive part, and it
repeats until it reaches a fixed point.

One congruence step is polynomial in the number of paths of the current
classes. The closure itself can be exponentially larger than the input: the
classes @[0^j, 0^(j-1) ++ [1]]@ for @j@ from 1 to @n@ have @2n@ paths, and
their closure has @2^(n+1) - 2@ paths (measured for @n@ up to 9). So the cost is
polynomial in the size of the closure, not in the size of the input. A set
in which no path is a strict prefix of another is already closed, and the
congruence step then adds nothing.
-}
mkEqConstraints :: [[Path]] -> EqConstraints
mkEqConstraints = normalize . map Set.fromList

-- | 'mkEqConstraints' over classes that are already sets.
normalize :: [Set Path] -> EqConstraints
normalize initialConstraints = case completedConstraints of
    Nothing -> EqContradiction
    Just cs -> EqConstraints $ sort $ map PathEClass cs
  where
    -- Reason for the extra "complete" in this line:
    -- The first simplification done to the constraints is eclass-completion,
    -- to remove redundancy and shrink the constraints before the very inefficient
    -- addCongruences step (important in tests; less so in realistic input).
    -- The last simplification must also be completion, to give a valid value.
    completedConstraints = fixMaybe congruenceStep $ complete $ removeTrivial initialConstraints
      where
        removeTrivial :: [Set Path] -> [Set Path]
        removeTrivial = filter ((> 1) . Set.size)

        -- One step of congruence closure. It fails when a class forces a path to be
        -- equal to one of its strict subpaths.
        congruenceStep :: [Set Path] -> Maybe [Set Path]
        congruenceStep classes = do
            let closed = complete $ addCongruences classes
            when (isContradicting closed) Nothing
            pure closed

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

        -- Iterate a partial step function until stable or failed.
        fixMaybe :: (Eq a) => (a -> Maybe a) -> a -> Maybe a
        fixMaybe f x = case f x of
            Nothing -> Nothing
            Just x'
                | x' == x -> Just x
                | otherwise -> fixMaybe f x'

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
combineEqConstraintsMemo = memo2 go
  where
    go ec1 ec2 = normalize $ map unPathEClass $ unsafeGetEclasses ec1 ++ unsafeGetEclasses ec2
{-# NOINLINE combineEqConstraintsMemo #-}

{- | Descend every path in a constraint set through one child index.

Equality classes with fewer than two remaining paths are dropped immediately:
they no longer constrain anything after the descent.
-}
eqConstraintsDescend :: EqConstraints -> ChildIndex -> EqConstraints
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
