-- | Count finite equality languages without constructing their members.
module Data.ECTA.Gen.Internal.Symbolic (symbolicRanked, symbolicRankedWith, symbolicGroupsWith) where

import qualified Control.Monad.State.Lazy as State
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import qualified Data.ECTA as ECTA
import Data.ECTA.Paths (Path, subsumptionOrderedEclasses, unPath, unPathEClass)
import Data.Tree.FTA.Constraint (Constraint)
import Data.Tree.FTA.Interned (Node (Node))
import Data.Tree.FTA.Interned.Operations (intersect, intersectEdge, nodeEdges)
import Data.Tree.FTA.Interned.Type (Edge, edgeChildren, edgeConstraint, edgeSymbol, nodeIdentity, setChildren)
import qualified Data.Tree.Gen.Internal as Ranked

-- | A constructor context whose variables denote whole subtree languages.
data Fragment symbol = Variable Int | Constructor symbol [Fragment symbol]
    deriving (Eq, Ord)

-- | A position in a constructor context.
data Target symbol = Target (Fragment symbol) [Int]
    deriving (Eq, Ord)

-- | A required position or an equality between two positions.
data Obligation symbol = Exists (Target symbol) | Equal (Target symbol) (Target symbol)
    deriving (Eq, Ord)

-- | Independent variable domains, substitutions, and pending equalities.
data Problem symbol constraint = Problem
    { domains :: Map.Map Int (Node symbol constraint)
    , bindings :: Map.Map Int (Fragment symbol)
    , nextVariable :: Int
    , obligations :: [Obligation symbol]
    }

-- | A resolved position, an absent position, or a variable to expand.
data Resolution symbol = Resolved (Fragment symbol) | Absent | Expand Int

-- | A normalized equality context and its independent domain identities.
type ProblemKey symbol = ([(Int, Int)], [Obligation symbol])

-- | Counts shared by graph identity and normalized equality context.
data Counts symbol = Counts
    { graphCounts :: Map.Map Int Integer
    , contextCounts :: Map.Map (ProblemKey symbol) Integer
    }

-- | Empty caches scoped to one compiled language.
emptyCounts :: Counts symbol
emptyCounts = Counts Map.empty Map.empty

-- | Requirements of the shared graph and its equality interpretation.
type Theory symbol constraint = (Ord symbol, Hashable symbol, Typeable symbol, Constraint constraint)

{- | A sum of equality indicators. Each term's sum must be zero or one.

For example, the negation of equality is the unconstrained indicator minus
the equality indicator. This representation permits Boolean constraints without
enumerating the terms that fail an equality.
-}
type Interpretation constraint = constraint -> [(Integer, [[Path]])]

{- | Build one exact rank per term in a finite equality language.

Counting expands constructor contexts only along constrained paths. Equal
variables share an intersected domain. Inclusion-exclusion removes overlapping
alternatives. Rank selection conditions the graph on one constructor at a time.
Only the selected term is constructed. No accepted-term table is retained.
-}
symbolicRanked ::
    (Ord symbol, Hashable symbol, Typeable symbol) =>
    ECTA.Node symbol -> Either Ranked.RankedError (Ranked.Ranked (Tree.Tree symbol))
symbolicRanked = symbolicRankedWith interpret . ECTA.toInterned
  where
    interpret = maybe [] (\classes -> [(1, map unPathEClass classes)]) . subsumptionOrderedEclasses

{- | Compile a finite graph with an exact sum of equality indicators per guard.

Each path class requires all its positions to exist and denote equal subtrees.
A singleton class requires only existence. The interpretation must preserve
conjunction: interpreting conjoined guards
must give the pointwise product of their indicators. These are integration
invariants. Checking them by enumerating the language would defeat the compiler.
-}
symbolicRankedWith ::
    (Theory symbol constraint) =>
    Interpretation constraint -> Node symbol constraint -> Either Ranked.RankedError (Ranked.Ranked (Tree.Tree symbol))
symbolicRankedWith interpret root =
    Ranked.fromIndexedOnDemand $ Ranked.Indexed total select
  where
    (total, counts) = State.runState (countNode interpret root) emptyCounts
    select rank = State.evalState (selectTerm interpret root [] rank) counts

{- | Partition constructor-order ranks by finite path observations.

Each group contains its count and a prefix counter over the original rank
domain. The prefix counter counts group ranks strictly below its argument.
Missing positions are absent from the observation map. Neither partitioning
nor prefix counting constructs a term.
-}
symbolicGroupsWith ::
    (Theory symbol constraint) =>
    Interpretation constraint ->
    [Path] ->
    Node symbol constraint ->
    Map.Map (Map.Map Path (symbol, Bool)) (Integer, Integer -> Integer)
symbolicGroupsWith interpret requested root =
    Map.map (\(count, graph) -> (count, \rank -> State.evalState (prefixAt interpret root graph [[]] rank) counts)) groups
  where
    (groups, counts) = State.runState (partitionAt (Set.toAscList $ Set.fromList requested) Map.empty root) emptyCounts
    partitionAt [] observations graph = do
        count <- countNode interpret graph
        pure $ if count == 0 then Map.empty else Map.singleton observations (count, graph)
    partitionAt (target : rest) observations graph = do
        let position = unPath target
            present =
                [ (Map.insert target (symbol, arity == 0) observations, condition position constructor graph)
                | constructor@(symbol, arity) <- constructorsAt position graph
                ]
            absent = (observations, conditionMissing position graph)
        variants <-
            traverse
                ( \(observed, restricted) -> do
                    count <- countNode interpret restricted
                    if count == 0 then pure Map.empty else partitionAt rest observed restricted
                )
                (absent : present)
        pure $ Map.unions variants

-- | Count one observed group's members before a source-rank boundary.
prefixAt ::
    (Theory symbol constraint) =>
    Interpretation constraint ->
    Node symbol constraint ->
    Node symbol constraint ->
    [[Int]] ->
    Integer ->
    State.State (Counts symbol) Integer
prefixAt _ _ _ _ rank | rank <= 0 = pure 0
prefixAt interpret root subset pending rank = do
    total <- countNode interpret root
    retained <- countNode interpret subset
    if rank >= total
        then pure retained
        else
            if retained == 0 || retained == total
                then pure $ if retained == 0 then 0 else rank
                else case pending of
                    [] -> pure 0
                    position : rest -> do
                        local <- countNode interpret $ project position root
                        if local == 1
                            then prefixAt interpret root subset rest rank
                            else alternatives position rest rank $ constructorsAt position root
  where
    alternatives _ _ _ [] = pure 0
    alternatives position rest remaining (constructor@(_, arity) : others) = do
        let selected = condition position constructor root
            restricted = condition position constructor subset
        count <- countNode interpret selected
        if remaining >= count
            then do
                before <- countNode interpret restricted
                after <- alternatives position rest (remaining - count) others
                pure $ before + after
            else prefixAt interpret selected restricted ([position <> [index] | index <- [0 .. arity - 1]] <> rest) remaining

-- | Count a shared graph once per interned identity.
countNode ::
    (Theory symbol constraint) => Interpretation constraint -> Node symbol constraint -> State.State (Counts symbol) Integer
countNode interpret node
    | null (nodeEdges node) = pure 0
    | otherwise = do
        counts <- State.get
        case Map.lookup (nodeIdentity node) $ graphCounts counts of
            Just count -> pure count
            Nothing -> do
                count <- countUnion (countEdge interpret) $ nodeEdges node
                State.modify' $ \cache -> cache{graphCounts = Map.insert (nodeIdentity node) count $ graphCounts cache}
                pure count

-- | Count a union through distinct intersections of its alternatives.
countUnion ::
    (Theory symbol constraint) =>
    (Edge symbol constraint -> State.State (Counts symbol) Integer) ->
    [Edge symbol constraint] ->
    State.State (Counts symbol) Integer
countUnion count edges =
    sum <$> traverse contribution (Map.toList $ foldl' add Map.empty edges)
  where
    contribution (edge, coefficient) = (coefficient *) <$> count edge
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
    (Theory symbol constraint) => Interpretation constraint -> Edge symbol constraint -> State.State (Counts symbol) Integer
countEdge interpret edge =
    sum <$> traverse (\(coefficient, constraint) -> (coefficient *) <$> count constraint) (interpret $ edgeConstraint edge)
  where
    count constraint =
        solve interpret $
            Problem (Map.fromList $ zip [0 ..] children) Map.empty (length children) (edgeObligations context constraint)
    children = edgeChildren edge
    context = Constructor (edgeSymbol edge) $ map Variable [0 .. length children - 1]

-- | Preserve path existence, including classes that contain only one path.
edgeObligations :: Fragment symbol -> [[Path]] -> [Obligation symbol]
edgeObligations context = concatMap obligationsFor
  where
    obligationsFor paths = case map (Target context . unPath) paths of
        [] -> []
        first : rest -> Exists first : map (Equal first) rest

-- | Follow substitutions without expanding a variable's language.
resolve :: Problem symbol constraint -> Target symbol -> Resolution symbol
resolve problem (Target (Variable variable) position) =
    case Map.lookup variable $ bindings problem of
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
normalize :: (Ord symbol) => Problem symbol constraint -> Maybe (Problem symbol constraint)
normalize problem = do
    pending <- concat <$> traverse normalizeObligation (obligations problem)
    pure $ Problem renamedDomains Map.empty (Map.size renamedDomains) $ Set.toAscList $ Set.fromList pending
  where
    names = Map.fromList $ zip (Map.keys $ domains problem) [0 ..]
    renamedDomains = Map.mapKeysMonotonic (names Map.!) $ domains problem
    rename (Variable variable) = Variable $ names Map.! variable
    rename (Constructor symbol children) = Constructor symbol $ map rename children

    inline (Variable variable) = maybe (Variable variable) inline $ Map.lookup variable $ bindings problem
    inline (Constructor symbol children) = Constructor symbol $ map inline children

    follow (Variable variable) position = case Map.lookup variable $ bindings problem of
        Nothing -> Just $ Target (Variable variable) position
        Just fragment -> follow fragment position
    follow fragment [] = Just $ Target (inline fragment) []
    follow (Constructor _ children) (index : rest) = case drop index children of
        child : _ | index >= 0 -> follow child rest
        _ -> Nothing

    target (Target fragment position) = do
        Target resolved rest <- follow fragment position
        pure $ Target (rename resolved) rest
    required (Target _ []) = []
    required remaining = [Exists remaining]
    normalizeObligation (Exists position) = required <$> target position
    normalizeObligation (Equal left right) = do
        first <- target left
        second <- target right
        pure $ if first == second then required first else [Equal (min first second) (max first second)]

-- | Share counts of equivalent contexts before expanding constrained variables.
solve ::
    (Theory symbol constraint) =>
    Interpretation constraint -> Problem symbol constraint -> State.State (Counts symbol) Integer
solve interpret problem
    | any (null . nodeEdges) $ Map.elems $ domains problem = pure 0
    | otherwise = case normalize problem of
        Nothing -> pure 0
        Just normalized -> do
            cache <- State.get
            let key = ([(variable, nodeIdentity node) | (variable, node) <- Map.toList $ domains normalized], obligations normalized)
            case Map.lookup key $ contextCounts cache of
                Just count -> pure count
                Nothing -> do
                    count <- solveStep interpret normalized
                    State.modify' $ \current -> current{contextCounts = Map.insert key count $ contextCounts current}
                    pure count

-- | Solve one normalized obligation, then multiply independent domain counts.
solveStep ::
    (Theory symbol constraint) =>
    Interpretation constraint -> Problem symbol constraint -> State.State (Counts symbol) Integer
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
    (Theory symbol constraint) =>
    Interpretation constraint ->
    Problem symbol constraint ->
    Fragment symbol ->
    Fragment symbol ->
    State.State (Counts symbol) Integer
unify interpret problem (Variable left) (Variable right)
    | left == right = solve interpret problem
    | otherwise =
        solve
            interpret
            problem
                { domains = Map.insert right common $ Map.delete left $ domains problem
                , bindings = Map.insert left (Variable right) $ bindings problem
                }
  where
    common =
        (domains problem Map.! left)
            `intersect` (domains problem Map.! right)
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
occurs :: Problem symbol constraint -> Int -> Fragment symbol -> Bool
occurs problem variable fragment = case resolve problem $ Target fragment [] of
    Resolved (Variable other) -> variable == other
    Resolved (Constructor _ children) -> any (occurs problem variable) children
    _ -> False

-- | Expose one constrained variable's root, preserving overlaps symbolically.
expandVariable ::
    (Theory symbol constraint) =>
    Interpretation constraint -> Problem symbol constraint -> Int -> State.State (Counts symbol) Integer
expandVariable interpret problem variable =
    countUnion expand $ nodeEdges $ domains problem Map.! variable
  where
    expand edge =
        sum
            <$> traverse
                (\(coefficient, constraint) -> (coefficient *) <$> expandWith edge constraint)
                (interpret $ edgeConstraint edge)
    expandWith edge constraint =
        solve
            interpret
            problem
                { domains = Map.union fresh $ Map.delete variable $ domains problem
                , bindings = Map.insert variable context $ bindings problem
                , nextVariable = nextVariable problem + length children
                , obligations = edgeObligations context constraint <> obligations problem
                }
      where
        children = edgeChildren edge
        variables = take (length children) [nextVariable problem ..]
        fresh = Map.fromList $ zip variables children
        context = Constructor (edgeSymbol edge) $ map Variable variables

-- | Keep one constructor at a selected position in the graph.
condition :: (Theory symbol constraint) => [Int] -> (symbol, Int) -> Node symbol constraint -> Node symbol constraint
condition [] (symbol, arity) node =
    Node [edge | edge <- nodeEdges node, edgeSymbol edge == symbol, length (edgeChildren edge) == arity]
condition (index : rest) constructor node =
    Node
        [ setChildren edge $ take index children <> [condition rest constructor child] <> drop (index + 1) children
        | edge <- nodeEdges node
        , let children = edgeChildren edge
        , child : _ <- [drop index children]
        ]

-- | Retain terms for which a requested position does not exist.
conditionMissing :: (Theory symbol constraint) => [Int] -> Node symbol constraint -> Node symbol constraint
conditionMissing [] _ = Node []
conditionMissing (index : rest) node = Node $ map restrict $ nodeEdges node
  where
    restrict edge = case drop index $ edgeChildren edge of
        child : _
            | index >= 0 ->
                setChildren edge $
                    take index (edgeChildren edge) <> [conditionMissing rest child] <> drop (index + 1) (edgeChildren edge)
        _ -> edge

-- | Read possible constructors at a path without enumerating subterms.
constructorsAt :: (Theory symbol constraint) => [Int] -> Node symbol constraint -> [(symbol, Int)]
constructorsAt position root =
    Set.toAscList $ Set.fromList [(edgeSymbol edge, length $ edgeChildren edge) | edge <- nodeEdges $ project position root]

-- | An upper bound on the subtree language at one position.
project :: (Theory symbol constraint) => [Int] -> Node symbol constraint -> Node symbol constraint
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
    (Theory symbol constraint) =>
    Interpretation constraint ->
    Node symbol constraint ->
    [Int] ->
    Integer ->
    State.State (Counts symbol) (Tree.Tree symbol)
selectTerm interpret root position rank = do
    ~(term, _, _) <- selectAt interpret root position rank
    pure term

-- | Restrict the selected prefix and decode only its selected descendants.
selectAt ::
    (Theory symbol constraint) =>
    Interpretation constraint ->
    Node symbol constraint ->
    [Int] ->
    Integer ->
    State.State (Counts symbol) (Tree.Tree symbol, Node symbol constraint, Integer)
selectAt interpret root position rank = do
    let local = project position root
    count <- countNode interpret local
    if count == 1
        then do
            counts <- State.get
            pure (State.evalState (selectUniqueAt interpret local []) counts, root, rank)
        else choose rank $ constructorsAt position root
  where
    choose _ [] = error "symbolicRanked: rank outside the retained language"
    choose remaining (constructor@(symbol, arity) : rest) = do
        let restricted = condition position constructor root
        count <- countNode interpret restricted
        if remaining >= count
            then choose (remaining - count) rest
            else do
                ~(children, final, suffixRank) <- selectChildren restricted remaining [0 .. arity - 1]
                pure (Tree.Node symbol children, final, suffixRank)
    selectChildren graph remaining [] = pure ([], graph, remaining)
    selectChildren graph remaining (index : rest) = do
        ~(term, restricted, suffixRank) <- selectAt interpret graph (position <> [index]) remaining
        ~(children, final, finalRank) <- selectChildren restricted suffixRank rest
        pure (term : children, final, finalRank)

-- | Decode a singleton language without traversing unobserved sibling trees.
selectUniqueAt ::
    (Theory symbol constraint) =>
    Interpretation constraint -> Node symbol constraint -> [Int] -> State.State (Counts symbol) (Tree.Tree symbol)
selectUniqueAt interpret root position = choose $ constructorsAt position root
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
                        [State.evalState (selectUniqueAt interpret root $ position <> [index]) counts | index <- [0 .. arity - 1]]
