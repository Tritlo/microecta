-- | Count finite equality languages without constructing their members.
module Data.CFTA.Gen.Internal.Symbolic (symbolicRanked) where

import qualified Control.Monad.State.Lazy as State
import Data.Hashable (Hashable)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)
import System.IO.Unsafe (unsafePerformIO)

import Data.CFTA.Constraint (
    Constraint (..),
    indicators,
 )
import qualified Data.CFTA.Equality as ECTA
import Data.CFTA.Index (Arity (..), Cardinality (..), Rank (..), VarIndex (..), childIndexes)
import Data.CFTA.Interned (Node (Node))
import Data.CFTA.Interned.Operations (intersect, intersectEdge, nodeEdges)
import Data.CFTA.Interned.Type (Edge, NodeId (..), edgeChildren, edgeConstraint, edgeSymbol, nodeIdentity, setChildren)
import Data.CFTA.Path (ChildIndex (..), Path, unPath)
import qualified Data.CFTA.Ranked.Internal as Ranked

-- | A constructor context whose variables denote whole subtree languages.
data Fragment symbol = Variable VarIndex | Constructor symbol [Fragment symbol]
    deriving (Eq, Ord)

-- | A position in a constructor context.
data Target symbol = Target (Fragment symbol) [Int]
    deriving (Eq, Ord)

-- | A required position or an equality between two positions.
data Obligation symbol = Exists (Target symbol) | Equal (Target symbol) (Target symbol)
    deriving (Eq, Ord)

-- | Independent variable domains, substitutions, and pending equalities.
data Problem symbol = Problem
    { domains :: Map.Map Int (Node symbol)
    , bindings :: Map.Map Int (Fragment symbol)
    , nextVariable :: VarIndex
    , obligations :: [Obligation symbol]
    }

-- | A resolved position, an absent position, or a variable to expand.
data Resolution symbol = Resolved (Fragment symbol) | Absent | Expand VarIndex

-- | A normalized equality context and its independent domain identities.
type ProblemKey symbol = ([(VarIndex, NodeId)], [Obligation symbol])

-- | Counts shared by graph identity and normalized equality context.
data Counts symbol = Counts
    { graphCounts :: IntMap.IntMap Cardinality
    , contextCounts :: Map.Map (ProblemKey symbol) Cardinality
    }

-- | Empty caches scoped to one compiled language.
emptyCounts :: Counts symbol
emptyCounts = Counts IntMap.empty Map.empty

{- | The counts of one compiled language, shared by all its selections.

Every count is a function of interned graphs and normalized contexts, so
sharing the cache changes no result. Two concurrent selections can each
replace the cache; the loser's new counts are only computed again later.
-}
newCountCache :: Counts symbol -> IORef (Counts symbol)
newCountCache counts = unsafePerformIO $ newIORef counts
{-# NOINLINE newCountCache #-}

-- | Run a selection from the shared counts, and keep the counts it adds.
selectCached :: IORef (Counts symbol) -> State.State (Counts symbol) a -> a
selectCached cache selection = unsafePerformIO $ do
    counts <- readIORef cache
    let (result, grown) = State.runState selection counts
    atomicModifyIORef' cache $ const (grown, ())
    pure result
{-# NOINLINE selectCached #-}

-- | Requirements of the shared graph and its equality interpretation.
type Theory symbol = (Ord symbol, Hashable symbol, Typeable symbol)

{- | A sum of equality indicators. Each term's sum must be zero or one.

'indicators' keeps to this. It gives the path equalities of a constraint as
one summand, or none for a contradiction, and writes its Boolean guard as a
polynomial in the indicators of path equality. Such a polynomial has the value
zero or one on every term.

For example, the negation of equality is the unconstrained indicator minus
the equality indicator. This representation permits Boolean constraints without
enumerating the terms that fail an equality.
-}
type Interpretation = Constraint -> [(Integer, [[Path]])]

-- | A count times a signed coefficient of inclusion and exclusion.
scaled :: Integer -> Cardinality -> Cardinality
scaled coefficient (Cardinality count) = Cardinality $ coefficient * count

{- | Build one exact rank per term in a finite equality language.

Counting expands constructor contexts only along constrained paths. Equal
variables share an intersected domain. Inclusion-exclusion removes overlapping
alternatives. Rank selection conditions the graph on one constructor at a time.
Only the selected term is constructed. No accepted-term table is retained.

Ranks follow the order of the constructors at each position, and the
constructors are ordered by arity, then by the given key. Pass a key with a
stable order, such as the text of an interned symbol, so that ranks do not
depend on interning order.
-}
symbolicRanked ::
    (Theory symbol, Ord key) =>
    (symbol -> key) -> ECTA.Node symbol -> Either Ranked.RankedError (Ranked.Ranked (Tree.Tree symbol))
symbolicRanked order = symbolicRankedWith order interpret
  where
    interpret constraint = case indicators constraint of
        Just summands -> summands
        Nothing ->
            error
                "microcfta-generator bug in Data.CFTA.Gen.Internal.Symbolic.symbolicRanked: \
                \a constraint without indicators reached symbolic counting"

{- | Compile a finite graph with an exact sum of equality indicators per guard.

Each path class requires all its positions to exist and denote equal subtrees.
A singleton class requires only existence. The interpretation must preserve
conjunction: interpreting conjoined guards
must give the pointwise product of their indicators. 'indicators' preserves
it, because conjunction merges the equality classes and conjoins the guards.
Checking this by enumerating the language would defeat the compiler.
-}
symbolicRankedWith ::
    (Theory symbol, Ord key) =>
    (symbol -> key) ->
    Interpretation ->
    Node symbol ->
    Either Ranked.RankedError (Ranked.Ranked (Tree.Tree symbol))
symbolicRankedWith order interpret root =
    Ranked.fromIndexedOnDemand $ Ranked.Indexed total select
  where
    (total, counts) = State.runState (countNode interpret root) emptyCounts
    cache = newCountCache counts
    select rank = selectCached cache $ selectTerm order interpret root [] rank

-- | Count a shared graph once per interned identity.
countNode ::
    (Theory symbol) => Interpretation -> Node symbol -> State.State (Counts symbol) Cardinality
countNode interpret node
    | null (nodeEdges node) = pure 0
    | otherwise = do
        counts <- State.get
        case IntMap.lookup ident $ graphCounts counts of
            Just count -> pure count
            Nothing -> do
                count <- countUnion (countEdge interpret) $ nodeEdges node
                State.modify' $ \cache -> cache{graphCounts = IntMap.insert ident count $ graphCounts cache}
                pure count
  where
    NodeId ident = nodeIdentity node

-- | Count a union through distinct intersections of its alternatives.
countUnion ::
    (Theory symbol) =>
    (Edge symbol -> State.State (Counts symbol) Cardinality) ->
    [Edge symbol] ->
    State.State (Counts symbol) Cardinality
countUnion count edges =
    sum <$> traverse contribution (Map.toList $ foldl' add Map.empty edges)
  where
    contribution (edge, coefficient) = scaled coefficient <$> count edge
    add terms edge =
        Map.filter (/= 0)
            $ Map.insertWith (+) edge 1
            $ Map.unionWith (+) terms
            $ Map.fromListWith
                (+)
                [ (common, negate coefficient)
                | (previous, coefficient) <- Map.toList terms
                , Just common <- [intersectEdge edge previous]
                , not $ null $ nodeEdges $ Node [common]
                ]

-- | Convert an edge into independent child domains and path obligations.
countEdge ::
    (Theory symbol) => Interpretation -> Edge symbol -> State.State (Counts symbol) Cardinality
countEdge interpret edge =
    sum
        <$> traverse (\(coefficient, constraint) -> scaled coefficient <$> count constraint) (interpret $ edgeConstraint edge)
  where
    count constraint =
        solve interpret $
            Problem
                (Map.fromList $ zip [0 ..] children)
                Map.empty
                (VarIndex (length children))
                (edgeObligations context constraint)
    children = edgeChildren edge
    context = Constructor (edgeSymbol edge) $ map Variable [0 .. VarIndex (length children) - 1]

-- | Preserve path existence, including classes that contain only one path.
edgeObligations :: Fragment symbol -> [[Path]] -> [Obligation symbol]
edgeObligations context = concatMap obligationsFor
  where
    obligationsFor paths = case map (Target context . map (\(ChildIndex index) -> index) . unPath) paths of
        [] -> []
        first : rest -> Exists first : map (Equal first) rest

-- | Follow substitutions without expanding a variable's language.
resolve :: Problem symbol -> Target symbol -> Resolution symbol
resolve problem (Target (Variable variable) position) =
    case Map.lookup (fromEnum variable) $ bindings problem of
        Just fragment -> resolve problem $ Target fragment position
        Nothing -> case position of
            [] -> Resolved $ Variable variable
            _ -> Expand variable
resolve _ (Target fragment []) = Resolved fragment
resolve problem (Target (Constructor _ children) (index : rest)) =
    case drop index children of
        child : _ | index >= 0 -> resolve problem $ Target child rest
        _ -> Absent

{- | Remove resolved path prefixes and renumber the remaining variables.

Constructor choices outside the remaining obligations cannot affect equality.
Removing those contexts lets different choices reuse the same count. Free
domains remain present because each still contributes independent choices.
-}
normalize :: (Ord symbol) => Problem symbol -> Maybe (Problem symbol)
normalize problem = do
    pending <- concat <$> traverse normalizeObligation (obligations problem)
    pure
        $ Problem renamedDomains Map.empty (VarIndex (Map.size renamedDomains))
        $ Set.toAscList
        $ Set.fromList pending
  where
    names = Map.fromList $ zip (Map.keys $ domains problem) [0 ..]
    renamedDomains = Map.mapKeysMonotonic (fromEnum . (names Map.!)) $ domains problem
    inline (Variable variable) = maybe (Variable variable) inline $ Map.lookup (fromEnum variable) $ bindings problem
    inline (Constructor symbol children) = Constructor symbol $ map inline children

    follow (Variable variable) position = case Map.lookup (fromEnum variable) $ bindings problem of
        Nothing -> Just $ Target (Variable variable) position
        Just fragment -> follow fragment position
    follow fragment [] = Just $ Target (inline fragment) []
    follow (Constructor _ children) (index : rest) = case drop index children of
        child : _ | index >= 0 -> follow child rest
        _ -> Nothing

    target (Target fragment position) = do
        Target resolved rest <- follow fragment position
        pure $ Target (rename resolved) rest
      where
        rename (Variable variable) = Variable $ names Map.! fromEnum variable
        rename (Constructor symbol children) = Constructor symbol $ map rename children
    required (Target _ []) = []
    required remaining = [Exists remaining]
    normalizeObligation (Exists position) = required <$> target position
    normalizeObligation (Equal left right) = do
        first <- target left
        second <- target right
        pure $ if first == second then required first else [Equal (min first second) (max first second)]

-- | Share counts of equivalent contexts before expanding constrained variables.
solve ::
    (Theory symbol) =>
    Interpretation -> Problem symbol -> State.State (Counts symbol) Cardinality
solve interpret problem
    | any (null . nodeEdges) $ Map.elems $ domains problem = pure 0
    | otherwise = case normalize problem of
        Nothing -> pure 0
        Just normalized -> do
            cache <- State.get
            let key =
                    ( [(VarIndex variable, nodeIdentity node) | (variable, node) <- Map.toList $ domains normalized]
                    , obligations normalized
                    )
            case Map.lookup key $ contextCounts cache of
                Just count -> pure count
                Nothing -> do
                    count <- solveStep interpret normalized
                    State.modify' $ \current -> current{contextCounts = Map.insert key count $ contextCounts current}
                    pure count

-- | Solve one normalized obligation, then multiply independent domain counts.
solveStep ::
    (Theory symbol) =>
    Interpretation -> Problem symbol -> State.State (Counts symbol) Cardinality
solveStep interpret problem = case obligations problem of
    [] -> product <$> traverse (countNode interpret) (Map.elems $ domains problem)
    Exists target : rest -> case resolve problem target of
        Absent -> pure 0
        Expand variable -> expandVariable interpret problem variable
        Resolved _ -> solve interpret problem{obligations = rest}
    Equal left right : rest -> case (resolve problem left, resolve problem right) of
        (Absent, _) -> pure 0
        (_, Absent) -> pure 0
        (Expand variable, _) -> expandVariable interpret problem variable
        (_, Expand variable) -> expandVariable interpret problem variable
        (Resolved first, Resolved second) -> unify interpret problem{obligations = rest} first second

-- | Merge whole subtree variables or compare constructor contexts.
unify ::
    (Theory symbol) =>
    Interpretation ->
    Problem symbol ->
    Fragment symbol ->
    Fragment symbol ->
    State.State (Counts symbol) Cardinality
unify interpret problem (Variable left) (Variable right)
    | left == right = solve interpret problem
    | otherwise =
        solve
            interpret
            problem
                { domains = Map.insert (fromEnum right) common $ Map.delete (fromEnum left) $ domains problem
                , bindings = Map.insert (fromEnum left) (Variable right) $ bindings problem
                }
  where
    common =
        (domains problem Map.! fromEnum left)
            `intersect` (domains problem Map.! fromEnum right)
unify interpret problem (Variable variable) fragment
    | occurs problem variable fragment = pure 0
    | otherwise =
        expandVariable
            interpret
            problem{obligations = Equal (Target (Variable variable) []) (Target fragment []) : obligations problem}
            variable
unify interpret problem fragment (Variable variable) = unify interpret problem (Variable variable) fragment
unify interpret problem (Constructor left children) (Constructor right others)
    | left /= right || length children /= length others = pure 0
    | otherwise =
        solve
            interpret
            problem{obligations = zipWith (\a b -> Equal (Target a []) (Target b [])) children others <> obligations problem}

-- | Reject an equality between a finite tree and its proper subtree.
occurs :: Problem symbol -> VarIndex -> Fragment symbol -> Bool
occurs problem variable fragment = case resolve problem $ Target fragment [] of
    Resolved (Variable other) -> variable == other
    Resolved (Constructor _ children) -> any (occurs problem variable) children
    _ -> False

-- | Expose one constrained variable's root, preserving overlaps symbolically.
expandVariable ::
    (Theory symbol) =>
    Interpretation -> Problem symbol -> VarIndex -> State.State (Counts symbol) Cardinality
expandVariable interpret problem variable =
    countUnion expand $ nodeEdges $ domains problem Map.! fromEnum variable
  where
    expand edge =
        sum
            <$> traverse
                (\(coefficient, constraint) -> scaled coefficient <$> expandWith edge constraint)
                (interpret $ edgeConstraint edge)
    expandWith edge constraint =
        solve
            interpret
            problem
                { domains = Map.union fresh $ Map.delete (fromEnum variable) $ domains problem
                , bindings = Map.insert (fromEnum variable) context $ bindings problem
                , nextVariable = nextVariable problem + VarIndex (length children)
                , obligations = edgeObligations context constraint <> obligations problem
                }
      where
        children = edgeChildren edge
        variables = take (length children) [nextVariable problem ..]
        fresh = Map.fromList $ zip (map fromEnum variables) children
        context = Constructor (edgeSymbol edge) $ map Variable variables

-- | Keep one constructor at a selected position in the graph.
condition :: (Theory symbol) => [Int] -> (symbol, Arity) -> Node symbol -> Node symbol
condition [] (symbol, arity) node =
    Node [edge | edge <- nodeEdges node, edgeSymbol edge == symbol, Arity (length (edgeChildren edge)) == arity]
condition (index : rest) constructor node =
    Node
        [ setChildren edge $ take index children <> [condition rest constructor child] <> drop (index + 1) children
        | edge <- nodeEdges node
        , let children = edgeChildren edge
        , child : _ <- [drop index children]
        ]

{- | Read possible constructors at a path without enumerating subterms, by
arity, then in key order. Two symbols with one key stay apart, in symbol
order, so a key that does not tell symbols apart loses no constructor.
-}
constructorsAt ::
    (Theory symbol, Ord key) => (symbol -> key) -> [Int] -> Node symbol -> [(symbol, Arity)]
constructorsAt order position root =
    map snd
        $ Map.toAscList
        $ Map.fromList
            [ ((arity, order symbol, symbol), (symbol, arity))
            | edge <- nodeEdges $ project position root
            , let symbol = edgeSymbol edge
                  arity = Arity $ length $ edgeChildren edge
            ]

-- | An upper bound on the subtree language at one position.
project :: (Theory symbol) => [Int] -> Node symbol -> Node symbol
project position root = Node $ concatMap nodeEdges $ Set.toList $ go position $ Set.singleton root
  where
    go [] nodes = nodes
    go (index : rest) nodes =
        go rest
            $ Set.fromList
            $ mapMaybe
                (\edge -> case drop index $ edgeChildren edge of child : _ -> Just child; [] -> Nothing)
                [edge | node <- Set.toList nodes, edge <- nodeEdges node]

-- | Select one term in constructor order, carrying counts for the remaining suffix.
selectTerm ::
    (Theory symbol, Ord key) =>
    (symbol -> key) ->
    Interpretation ->
    Node symbol ->
    [Int] ->
    Rank ->
    State.State (Counts symbol) (Tree.Tree symbol)
selectTerm order interpret root position (Rank rank) = do
    ~(term, _, _) <- selectAt order interpret root position rank
    pure term

-- | Restrict the selected prefix and decode only its selected descendants.
selectAt ::
    (Theory symbol, Ord key) =>
    (symbol -> key) ->
    Interpretation ->
    Node symbol ->
    [Int] ->
    Integer ->
    State.State (Counts symbol) (Tree.Tree symbol, Node symbol, Integer)
selectAt order interpret root position rank = do
    let local = project position root
    count <- countNode interpret local
    if count == 1
        then do
            counts <- State.get
            pure (State.evalState (selectUniqueAt order interpret local []) counts, root, rank)
        else choose rank $ constructorsAt order position root
  where
    choose _ [] = error "symbolicRanked: rank outside the retained language"
    choose remaining (constructor@(symbol, arity) : rest) = do
        let restricted = condition position constructor root
        Cardinality count <- countNode interpret restricted
        if remaining >= count
            then choose (remaining - count) rest
            else do
                ~(children, final, suffixRank) <- selectChildren restricted remaining (map fromEnum (childIndexes arity))
                pure (Tree.Node symbol children, final, suffixRank)
    selectChildren graph remaining [] = pure ([], graph, remaining)
    selectChildren graph remaining (index : rest) = do
        ~(term, restricted, suffixRank) <- selectAt order interpret graph (position <> [index]) remaining
        ~(children, final, finalRank) <- selectChildren restricted suffixRank rest
        pure (term : children, final, finalRank)

-- | Decode a singleton language without traversing unobserved sibling trees.
selectUniqueAt ::
    (Theory symbol, Ord key) =>
    (symbol -> key) ->
    Interpretation ->
    Node symbol ->
    [Int] ->
    State.State (Counts symbol) (Tree.Tree symbol)
selectUniqueAt order interpret root position = choose $ constructorsAt order position root
  where
    choose [] = error "symbolicRanked: empty singleton language"
    choose (constructor@(symbol, arity) : rest) = do
        count <- countNode interpret $ condition position constructor root
        if count == 0
            then choose rest
            else do
                counts <- State.get
                pure $
                    Tree.Node
                        symbol
                        [ State.evalState (selectUniqueAt order interpret root $ position <> [index]) counts
                        | index <- map fromEnum (childIndexes arity)
                        ]
