{- | Counting and indexing the terms an ECTA accepts.

A node's language is the union over its edges, and an edge's language is the
product of its children under its symbol. That is the same shape the
generator combinators build, so an automaton becomes a size index by
translation: @choiceIndex@ per node, @productIndex@ per edge child, and a
size-one @constantIndex@ for the symbol itself, which makes a member's size
its number of term nodes.

Recursion needs no special case. Nodes are interned, so a @Mu@ and the
occurrences inside its own unfolding share one identity: building one lazy
entry per reachable identity ties exactly the knots the automaton has.

Equality constraints are not counted. They correlate an edge's children, so
the edge's count stops being the product of theirs and becomes the size of
an intersection; an automaton carrying them is rejected rather than
miscounted.

Ambiguity is not counted either. The union over a node's edges counts
accepting runs, so a node with two edges that accept a common term counts that
term twice; such an automaton is rejected rather than miscounted.

The inverse of each index gives the rank, or the size and the position, of an
accepted term. It follows the same plans as the index.

The module also holds the rank key and the codec check that the ordinary and
the refinement datatype imports share.
-}
module Data.CFTA.Gen.Internal.Automaton (
    automatonIndex,
    automatonTermPosition,
    finiteAutomaton,
    finiteAutomatonRank,
    declarationOrder,
    undecodableConstructor,
) where

import Control.Monad (foldM)
import qualified Control.Monad.State.Strict as State
import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (
    equalities,
    indicators,
    residual,
 )
import Data.Hashable (Hashable)
import qualified Data.IntMap.Strict as IntMap
import Data.List (compareLength, partition, sort, sortOn, tails)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, isNothing, listToMaybe)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import Data.CFTA.Equality (
    Edge,
    Node (EmptyNode),
    NodeId (..),
    edgeChildren,
    edgeConstraint,
    edgeSymbol,
    freeVars,
    intersect,
    nodeEdges,
    nodeIdentity,
    reachable,
 )
import Data.CFTA.Equality.Constraint (EqConstraints, subsumptionOrderedEclasses, unPathEClass)
import Data.CFTA.Index (Arity (..), Rank, childIndexes, offsetRank, pairRank)
import Data.CFTA.Path (ChildIndex (..), adjustAt, unPath)

import Data.CFTA.Gen.Error (GenError (..))
import Data.CFTA.Gen.Internal.Static (Static, termStatic)
import Data.CFTA.Gen.Internal.Support (unconstrainedEdge)
import Data.CFTA.Gen.Internal.Symbolic (symbolicRanked)
import qualified Data.CFTA.Gen.Internal.Table as Ordinary
import Data.CFTA.Generic (TypedFTA, constructorLabel, datatypeFTA)
import qualified Data.CFTA.Ranked.Internal as Ranked
import Data.CFTA.Ranked.Internal.Size (SizeIndex, SizedRank)
import Data.CFTA.Refinement (AutomatonError (OpenAutomaton))

{- | Count and index the terms an automaton accepts, by size.

Within one size, ranks order the edges of a node by arity, then by the given
key of their symbol, as symbolic counts do, then by the canonical classes of
their children ('canonicalClasses').

Fails on an automaton with free recursive variables, which is not a closed
language, on one whose edges carry equality constraints, and on an ambiguous
one, whose runs outnumber its terms.
-}
automatonIndex ::
    (Hashable symbol, Typeable symbol, Ord key) =>
    (symbol -> key) -> Node symbol -> Either GenError (SizeIndex (Tree.Tree symbol))
automatonIndex order root = uncurry Ordinary.tableIndex <$> automatonRows order root

{- | Find the size class and the position in it of a term that an automaton
accepts.

The size is the number of term nodes. For the same key and automaton,
'automatonIndex' selects the term at this size and position. The result is
'TermNotInLanguage' when the automaton does not accept the term, and the error
of 'automatonIndex' when that function fails. Apply the function to the key
and the automaton once: each term then uses the same counts.
-}
automatonTermPosition ::
    (Ord symbol, Hashable symbol, Typeable symbol, Ord key) =>
    (symbol -> key) -> Node symbol -> Tree.Tree symbol -> Either GenError SizedRank
automatonTermPosition order root = case automatonRows order root of
    Left err -> const $ Left err
    Right (initial, rows) -> maybe (Left TermNotInLanguage) Right . Ordinary.tablePosition initial rows

{- | The identity of the root and the rows of an automaton, with the edges of
each row in rank order.

Fails as 'automatonIndex' does.
-}
automatonRows ::
    (Hashable symbol, Typeable symbol, Ord key) =>
    (symbol -> key) -> Node symbol -> Either GenError (NodeId, Map.Map NodeId [FTA.Transition NodeId symbol ()])
automatonRows _ EmptyNode = Right (NodeId 0, Map.empty)
automatonRows order root
    | not $ Set.null $ freeVars root = Left $ InvalidSupport OpenAutomaton
    | any (any constrained) alternatives = Left CannotCountConstrainedEdges
    | any (ambiguous productiveRows) alternatives = Left AmbiguousAutomaton
    | otherwise = Right (nodeIdentity root, sortOn transitionKey <$> rows)
  where
    alternatives = IntMap.elems (reachable root)
    rows = Ordinary.rowsOf root
    classes = canonicalClasses $ IntMap.fromDistinctAscList [(ident, map edgeKey row) | (NodeId ident, row) <- Map.toAscList rows]
      where
        edgeKey transition =
            ( (length $ FTA.transitionChildren transition, order $ FTA.transitionSymbol transition)
            , FTA.transitionChildren transition
            )
    -- Transitions with one arity and key are ordered by the classes of their
    -- children, so the order does not depend on interning order.
    transitionKey transition =
        ( length $ FTA.transitionChildren transition
        , order $ FTA.transitionSymbol transition
        , [classes IntMap.! child | NodeId child <- FTA.transitionChildren transition]
        )

{- | Whether a node has two edges that accept a common term, given a test of
whether a node accepts a term.

Without equality constraints, two edges with the same symbol and arity share
a term exactly when every child position does, and a child position shares
one exactly when the intersection of the two children accepts a term. With
constraints, the answer can be yes where no term is shared.
-}
ambiguous ::
    (Hashable symbol, Typeable symbol) =>
    (Node symbol -> Bool) -> [Edge symbol] -> Bool
ambiguous productive alternatives =
    or
        [ overlapping left right
        | left : rest <- tails alternatives
        , right <- rest
        ]
  where
    overlapping left right =
        edgeSymbol left == edgeSymbol right
            && length (edgeChildren left) == length (edgeChildren right)
            && and
                ( zipWith
                    (\l r -> productive $ intersect l r)
                    (edgeChildren left)
                    (edgeChildren right)
                )

{- | Whether a node of a graph that can have cycles accepts a term. A cycle can
leave a node with edges and no finite term.
-}
productiveRows :: (Hashable symbol, Typeable symbol) => Node symbol -> Bool
productiveRows node
    | null (nodeEdges node) = False
    | otherwise = Map.member (nodeIdentity node) $ Ordinary.minimumSizes $ Ordinary.rowsOf node

-- | Whether an edge carries equality constraints.
constrained :: Edge symbol -> Bool
constrained = not . unconstrainedEdge

{- | Compile a finite equality graph with shared ordinary rank plans.

Alternatives that accept no common term and direct-child equalities have
compact plans. Equal child positions select one term from the intersection of
their languages. Nested equality paths, residual Boolean equalities, and
alternatives that share a symbol and accept a common term use symbolic
equality contexts and intersection counts. Both forms of plan order the
constructors by arity, then by the given key. In a compact plan, alternatives
that share a symbol are then ordered by the canonical classes of their
children ('canonicalClasses'), so their order does not depend on the order in
which the edges were interned. If two of them have equal classes, the node
uses the symbolic plan. Alternatives with distinct symbols and equal keys keep
the order in which their edges were interned. 'Symbol' orders by text, so the
symbol is a stable key. Nullary constructors come first, so rank shrinking
moves toward leaves. Only a selected term is constructed. The static ranks an
accepted term by the same plans: a compact node adds the offset of the
matching edge to the mixed-radix rank of its equality groups, and a symbolic
node counts the accepted terms before the term.
-}
finiteAutomaton ::
    (Ord symbol, Hashable symbol, Typeable symbol, Ord key) =>
    (symbol -> key) -> Node symbol -> Either GenError (Static symbol (Tree.Tree symbol))
finiteAutomaton order root =
    (\(ranked, rankOf) -> termStatic root (maybe (Left TermNotInLanguage) Right . rankOf) ranked)
        <$> compileFiniteAutomaton order root

{- | Find the rank of a term that a finite equality graph accepts.

For the same key and graph, the static of 'finiteAutomaton' decodes this rank
to the term. The result is 'TermNotInLanguage' when the graph does not accept
the term, and the error of 'finiteAutomaton' when that function fails. The
rank follows the plans of 'finiteAutomaton'. A compact node adds the offset of
the matching edge to the mixed-radix rank of the equality groups of the edge.
A symbolic node counts the accepted terms before the term. Apply the function
to the key and the graph once: each term then uses the same plans and counts.
-}
finiteAutomatonRank ::
    (Ord symbol, Hashable symbol, Typeable symbol, Ord key) =>
    (symbol -> key) -> Node symbol -> Tree.Tree symbol -> Either GenError Rank
finiteAutomatonRank order root = case compileFiniteAutomaton order root of
    Left err -> const $ Left err
    Right (_, rankOf) -> maybe (Left TermNotInLanguage) Right . rankOf

{- | Compile a finite equality graph to its ranked terms and to the inverse of
their ranks.

One pass builds both, so the ranks and their inverse follow the same plans.
The inverse gives 'Nothing' for a term that the graph does not accept.
-}
compileFiniteAutomaton ::
    (Ord symbol, Hashable symbol, Typeable symbol, Ord key) =>
    (symbol -> key) ->
    Node symbol ->
    Either GenError (Ranked.Ranked (Tree.Tree symbol), Tree.Tree symbol -> Maybe Rank)
compileFiniteAutomaton order root
    | null (nodeEdges root) = Left EmptyGenerator
    | any (any (isNothing . indicators . edgeConstraint)) (reachable root) = Left CannotCountConstrainedEdges
    | otherwise = case State.evalState (buildNode root) Map.empty of
        Nothing -> Left EmptyGenerator
        Just compiled -> Right compiled
  where
    buildNode node
        | null (nodeEdges node) = pure Nothing
        | otherwise = do
            cache <- State.get
            case Map.lookup (nodeIdentity node) cache of
                Just compiled -> pure compiled
                Nothing -> do
                    compiled <- buildAlternatives node
                    State.modify' $ Map.insert (nodeIdentity node) compiled
                    pure compiled

    buildAlternatives node
        -- In an acyclic graph, interning drops an edge with an empty child, so
        -- every node other than the empty one accepts a term.
        | sharedSymbols && (ambiguous (/= EmptyNode) (nodeEdges node) || tied) = pure $ symbolic node
        | any (residual . edgeConstraint) edges = pure $ symbolic node
        | any (needsPathExpansion . equalities . edgeConstraint) edges = pure $ symbolic node
        | otherwise = do
            alternatives <- catMaybes <$> traverse buildEdge edges
            pure $ case Ranked.oneof (map fst alternatives) of
                Left _ -> Nothing
                Right ranked -> Just (Ranked.share ranked, rankAlternatives alternatives)
      where
        sharedSymbols = Set.size (Set.fromList $ map edgeSymbol $ nodeEdges node) /= length (nodeEdges node)
        -- Alternatives that share an arity and a key are ordered by the
        -- canonical classes of their children, so the order does not depend
        -- on the order in which the edges were interned.
        edges
            | sharedSymbols = map snd keyed
            | otherwise = sortOn (\edge -> (length $ edgeChildren edge, order $ edgeSymbol edge)) $ nodeEdges node
        keyed = sortOn fst [(canonicalKey edge, edge) | edge <- nodeEdges node]
        canonicalKey edge =
            ( length $ edgeChildren edge
            , order $ edgeSymbol edge
            , [classes IntMap.! child | NodeId child <- map nodeIdentity $ edgeChildren edge]
            )
        -- A node that compilation builds, such as the intersection of equal
        -- children, is not in the graph of the root.
        classes
            | IntMap.member ident rootClasses = rootClasses
            | otherwise = classesOf node
          where
            NodeId ident = nodeIdentity node
        tied = or $ zipWith (\(left, _) (right, _) -> left == right) keyed (drop 1 keyed)
    -- The ranks of an alternative follow the ranks of the alternatives before it.
    rankAlternatives alternatives term =
        listToMaybe
            [ offsetRank offset rank
            | (offset, (_, rankOf)) <- Ranked.withOffsets (Ranked.cardinality . fst) alternatives
            , Just rank <- [rankOf term]
            ]

    buildEdge edge = case childGroups (Arity (length children)) (equalities $ edgeConstraint edge) of
        Nothing -> pure Nothing
        Just groups -> do
            selected <- traverse (buildGroup children) groups
            pure $ do
                compiledGroups <- sequence selected
                let slots = foldl' addGroup (pure Map.empty) (zip groups $ map fst compiledGroups)
                pure
                    ( (\values -> Tree.Node (edgeSymbol edge) [values Map.! index | index <- childIndexes (Arity (length children))])
                        <$> slots
                    , rankEdge edge $ zip groups compiledGroups
                    )
      where
        children = edgeChildren edge
    buildGroup children positions =
        case [child | (index, child) <- zip [0 ..] children, index `elem` positions] of
            [] -> pure Nothing
            first : rest -> buildNode $ foldl' intersect first rest
    addGroup prefix (positions, ranked) =
        (\values term -> foldr (`Map.insert` term) values positions) <$> prefix <*> ranked
    -- The groups are the digits of a mixed-radix rank, and the first group is
    -- the most significant digit. The terms of one group must be equal.
    rankEdge edge groups (Tree.Node symbol terms)
        | symbol /= edgeSymbol edge || length terms /= length (edgeChildren edge) = Nothing
        | otherwise = foldM addGroupRank 0 groups
      where
        addGroupRank rank (positions, (ranked, rankOf)) =
            case [term | (index, term) <- zip [0 ..] terms, index `elem` positions] of
                first : rest
                    | all (== first) rest ->
                        pairRank (Ranked.cardinality ranked) rank <$> rankOf first
                _ -> Nothing

    symbolic = either (const Nothing) Just . symbolicRanked order

    -- The canonical classes of the graph of the root, computed once.
    rootClasses = classesOf root
    classesOf node =
        canonicalClasses $
            IntMap.map
                (map $ \edge -> ((length $ edgeChildren edge, order $ edgeSymbol edge), map nodeIdentity $ edgeChildren edge))
                (reachable node)

{- | Canonical classes for the nodes of a graph, which can have cycles.

A node is a list of edges, and an edge is a key and the identities of its
children. The graph and the result use the 'Int' of a 'NodeId' as the key.
Every node starts in one class. Each round keys a node by its class
and the sorted keys of its edges with the classes of their children, and
numbers the classes in the order of those keys. The rounds stop when no class
splits (ordered partition refinement). The classes depend on the content of
the graph only, not on the identities of its nodes. A node keeps its class
first in its key, so two nodes keep their order once a round separates them,
and the order of two nodes does not depend on the rest of the graph. Two
nodes share a class when their edges are the same up to the classes of their
children.
-}
canonicalClasses :: (Ord key) => IntMap.IntMap [(key, [NodeId])] -> IntMap.IntMap Int
canonicalClasses graph = refine (IntMap.map (const 0) graph) (min 1 $ IntMap.size graph)
  where
    refine classes count
        | count' == count = classes'
        | otherwise = refine classes' count'
      where
        keys =
            IntMap.mapWithKey
                ( \nodeId edges ->
                    (classes IntMap.! nodeId, sort [(key, [classes IntMap.! child | NodeId child <- children]) | (key, children) <- edges])
                )
                graph
        numbers = Map.fromList $ zip (Set.toAscList $ Set.fromList $ IntMap.elems keys) [0 ..]
        classes' = IntMap.map (numbers Map.!) keys
        count' = Map.size numbers

-- | Whether a non-contradictory equality inspects below direct child roots.
needsPathExpansion :: EqConstraints -> Bool
needsPathExpansion constraints = case subsumptionOrderedEclasses constraints of
    Nothing -> False
    Just classes -> any (any ((/= EQ) . (`compareLength` 1) . unPath) . unPathEClass) classes

-- | Partition direct child positions into equality classes in child order.
childGroups :: Arity -> EqConstraints -> Maybe [[ChildIndex]]
childGroups arity constraints = do
    classes <- subsumptionOrderedEclasses constraints
    positions <- traverse (traverse childIndex . Set.toAscList . unPathEClass) classes
    pure $ foldl' merge (map pure (childIndexes arity)) positions
  where
    childIndex target = case unPath target of
        [index] | index >= 0 && index < ChildIndex (fromEnum arity) -> Just index
        _ -> Nothing
    merge groups [] = groups
    merge groups positions =
        let (equal, other) = partition (any (`elem` positions)) groups
         in sortOn (take 1) (concat equal : other)

{- | Order the constructor labels of a datatype by their position in the row
of their type.

The position is declaration order for constructors and domain order for
atomic literals: the derived grammar builds a constructor row from the generic
sum in order, and an atomic row from its domain without repeated values. A
label holds the type of its row, so it is in one row. The label text breaks
ties between rows. An unknown label has position zero. The positions are
computed once for each application to a datatype.
-}
declarationOrder :: TypedFTA annotation a -> Text -> (Int, Text)
declarationOrder datatype = \label -> (Map.findWithDefault 0 label positions, label)
  where
    positions =
        Map.fromList
            [ (Text.pack $ constructorLabel $ FTA.transitionSymbol transition, position)
            | row <- Map.elems $ FTA.transitionTable $ datatypeFTA datatype
            , (position, transition) <- zip [0 ..] row
            ]

{- | Find a constructor that is in a term the codec rejects.

Each transition of a reachable state gets one term of the initial state that
contains it. The other positions of that term hold one fixed term of their
state. So the check decodes one term per transition and does not enumerate
the language. An atomic literal whose 'Show' text 'Read' does not accept makes
its term fail.
-}
undecodableConstructor :: (Ord state) => (Tree.Tree symbol -> Bool) -> FTA.FTA state symbol annotation -> Maybe symbol
undecodableConstructor rejects automaton =
    listToMaybe
        [ symbol
        | (state, context) <- Map.toList contexts
        , FTA.Transition symbol children _ <- FTA.transitionsFrom automaton state
        , Just arguments <- [traverse (`Map.lookup` witnesses) children]
        , rejects $ context $ Tree.Node symbol arguments
        ]
  where
    -- One term for each productive state, as a least fixed point.
    witnesses = converge Map.empty
    converge known =
        let next = Map.foldrWithKey addWitness known $ FTA.transitionTable automaton
         in if Map.size next == Map.size known then known else converge next
    addWitness state transitions known
        | Map.member state known = known
        | otherwise =
            case [ Tree.Node symbol arguments
                 | FTA.Transition symbol children _ <- transitions
                 , Just arguments <- [traverse (`Map.lookup` known) children]
                 ] of
                term : _ -> Map.insert state term known
                [] -> known
    -- One context for each state that a term of the initial state reaches.
    contexts = reach (Map.singleton (FTA.initialState automaton) id) [FTA.initialState automaton]
    reach found [] = found
    reach found (state : pending) =
        let added =
                Map.fromList
                    [ ( child
                      , \hole -> (found Map.! state) $ Tree.Node symbol $ adjustAt position (const hole) arguments
                      )
                    | FTA.Transition symbol children _ <- FTA.transitionsFrom automaton state
                    , Just arguments <- [traverse (`Map.lookup` witnesses) children]
                    , (position, child) <- zip [0 ..] children
                    ]
                    `Map.difference` found
         in reach (Map.union found added) (pending <> Map.keys added)
