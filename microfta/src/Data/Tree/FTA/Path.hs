{-# LANGUAGE FunctionalDependencies #-}

{- | Child-index paths into terms and graphs.

A 'Path' names a position by the child index taken at each level. 'Pathable'
reads and edits the value at a path. The graph instances follow every
alternative, so reading a path from a node gives the union of the languages
at that position. Constraint theories build their constraints over these
paths.
-}
module Data.Tree.FTA.Path (
    Path (.., EmptyPath, ConsPath),
    unPath,
    path,
    isSubpath,
    isStrictSubpath,
    substSubpath,
    Pathable (..),
    pathsMatching,
    requirePath,
    requirePathList,
    statesAt,
) where

import Data.Hashable (Hashable (..))
import Data.List (compareLength, (!?))
import Data.Maybe (mapMaybe, maybeToList)
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import Data.Tree.FTA (Transition (..))
import Data.Tree.FTA.Constraint (Constraint)
import Data.Tree.FTA.Interned.Operations (unfoldOuterRec, union)
import Data.Tree.FTA.Interned.Type

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

instance (Hashable symbol, Typeable symbol, Constraint constraint) => Pathable (Node symbol constraint) (Node symbol constraint) where
    type Emptyable (Node symbol constraint) = Node symbol constraint

    getPath _ EmptyNode = EmptyNode
    getPath EmptyPath n = n
    getPath p n@(Mu _) = getPath p (unfoldOuterRec n)
    getPath (ConsPath p ps) (Node es) = union (mapMaybe (\e -> getPath ps <$> edgeChildren e !? p) es)
    getPath p _ = error $ "getPath: unexpected path " <> show p <> " for unresolved node"

    getAllAtPath _ EmptyNode = []
    getAllAtPath EmptyPath n = [n]
    getAllAtPath p n@(Mu _) = getAllAtPath p (unfoldOuterRec n)
    getAllAtPath (ConsPath p ps) (Node es) = concatMap (getAllAtPath ps) (mapMaybe (\e -> edgeChildren e !? p) es)
    getAllAtPath p _ = error $ "getAllAtPath: unexpected path " <> show p <> " for unresolved node"

    modifyAtPath f EmptyPath n = f n
    modifyAtPath _ _ EmptyNode = EmptyNode
    modifyAtPath f p n@(Mu _) = modifyAtPath f p (unfoldOuterRec n)
    modifyAtPath f (ConsPath p ps) (Node es) = Node (map goEdge es)
      where
        goEdge e = setChildren e (adjustAt p (modifyAtPath f ps) (edgeChildren e))
    modifyAtPath _ p _ = error $ "modifyAtPath: unexpected path " <> show p <> " for unresolved node"

instance (Hashable symbol, Typeable symbol, Constraint constraint) => Pathable [Node symbol constraint] (Node symbol constraint) where
    type Emptyable (Node symbol constraint) = Node symbol constraint

    getPath EmptyPath ns = union ns
    getPath (ConsPath p ps) ns = maybe EmptyNode (getPath ps) (ns !? p)

    getAllAtPath EmptyPath _ = []
    getAllAtPath (ConsPath p ps) ns = maybe [] (getAllAtPath ps) (ns !? p)

    modifyAtPath _ EmptyPath ns = ns
    modifyAtPath f (ConsPath p ps) ns = adjustAt p (modifyAtPath f ps) ns

{- | Paths to every reachable node that satisfies a predicate.

Linear in the number of paths and exponential in the size of the graph, so
use it on very small graphs only. A recursive node contributes no paths: the
search does not unfold recursion, so a match below a 'Mu' is not reported.
-}
pathsMatching :: (Node symbol constraint -> Bool) -> Node symbol constraint -> [Path]
pathsMatching _ EmptyNode = []
pathsMatching _ (InternedMu _) = []
pathsMatching f n@(InternedNode node) = concatMap pathsMatchingEdge (internedNodeEdges node) ++ [EmptyPath | f n]
  where
    pathsMatchingEdge e = concat $ zipWith (\i x -> map (ConsPath i) $ pathsMatching f x) [0 ..] (edgeChildren e)
pathsMatching _ (Rec _) = error "pathsMatching: unexpected Rec"

-- | Restrict a graph to the terms that contain the given path.
requirePath ::
    (Hashable symbol, Typeable symbol, Constraint constraint) => Path -> Node symbol constraint -> Node symbol constraint
requirePath EmptyPath n = n
requirePath _ EmptyNode = EmptyNode
requirePath p n@(Mu _) = requirePath p (unfoldOuterRec n)
requirePath (ConsPath p ps) (Node es) =
    Node
        [ setChildren e (requirePathList (ConsPath p ps) (edgeChildren e))
        | e <- es
        , compareLength (edgeChildren e) p == GT
        ]
requirePath _ (Rec _) = error "requirePath: unexpected Rec"

-- | Variant of 'requirePath' for a child list.
requirePathList ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Path -> [Node symbol constraint] -> [Node symbol constraint]
requirePathList EmptyPath ns = ns
requirePathList (ConsPath p ps) ns = adjustAt p (requirePath ps) ns

-- | Apply a function to the element at an index, if it exists.
adjustAt :: Int -> (a -> a) -> [a] -> [a]
adjustAt i f xs
    | i < 0 = xs
    | otherwise = case splitAt i xs of
        (prefix, x : suffix) -> prefix ++ f x : suffix
        _ -> xs

{- | The states at a child-index path below a transition of an explicit-state automaton.

The function gives the alternatives of a state: pass @'FTA.transitionsFrom'
automaton@ for an automaton, or a lookup in a bare transition table. The
first index selects a child state of the transition; each further index
selects that child of every alternative of the states reached so far. A
state is listed once per alternative that reaches it. An empty path gives
no states.
-}
statesAt :: (state -> [Transition state symbol guard]) -> Transition state symbol guard -> Path -> [state]
statesAt _ _ EmptyPath = []
statesAt alternatives transition (ConsPath index rest) = descend rest (maybeToList $ transitionChildren transition !? index)
  where
    descend EmptyPath current = current
    descend (ConsPath next further) current =
        descend
            further
            [ child
            | state <- current
            , outgoing <- alternatives state
            , Just child <- [transitionChildren outgoing !? next]
            ]
