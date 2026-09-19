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
-}
module Data.CFTA.Gen.Equality.Internal.Automaton (automatonIndex, finiteAutomaton) where

import qualified Control.Monad.State.Strict as State
import qualified Data.IntMap.Strict as IntMap
import Data.List (compareLength, partition, sortOn, tails)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import qualified Data.Set as Set
import qualified Data.Tree as Tree

import Data.CFTA.Equality (
    Edge,
    Node (EmptyNode),
    edgeChildren,
    edgeConstraint,
    edgeSymbol,
    freeVars,
    intersect,
    nodeEdges,
    nodeIdentity,
    reachable,
 )
import Data.CFTA.Equality.Constraint (EqConstraints (EmptyConstraints), subsumptionOrderedEclasses, unPathEClass)
import Data.CFTA.Path (unPath)
import Data.CFTA.Symbol (Symbol (Symbol))

import qualified Data.CFTA as FTA
import Data.CFTA.Gen.Equality.Internal.Static (Static, termStatic)
import Data.CFTA.Gen.Equality.Internal.Symbolic (symbolicRanked)
import Data.CFTA.Gen.Error (GenError (..))
import qualified Data.CFTA.Gen.Internal.Automaton as Ordinary
import qualified Data.CFTA.Interned as Interned
import qualified Data.CFTA.Ranked.Internal as Ranked
import Data.CFTA.Ranked.Internal.Size (SizeIndex)
import Data.CFTA.Refinement (AutomatonError (OpenAutomaton))

{- | Count and index the terms an automaton accepts, by size.

Fails on an automaton with free recursive variables, which is not a closed
language, on one whose edges carry equality constraints, and on an ambiguous
one, whose runs outnumber its terms.
-}
automatonIndex :: Node Symbol EqConstraints -> Either GenError (SizeIndex (Tree.Tree Symbol))
automatonIndex EmptyNode = Right $ Ordinary.tableIndex (0 :: Int) Map.empty
automatonIndex root
    | not $ Set.null $ freeVars root = Left $ InvalidSupport OpenAutomaton
    | any (any constrained) alternatives = Left CannotCountConstrainedEdges
    | any ambiguous alternatives = Left AmbiguousAutomaton
    | otherwise = Right $ Ordinary.tableIndex (nodeIdentity root) (Ordinary.rowsOf root)
  where
    alternatives = IntMap.elems (reachable root)

-- | Whether a node accepts any term at all.
productive :: Node Symbol EqConstraints -> Bool
productive node
    | null (nodeEdges node) = False
    | otherwise = Map.member (nodeIdentity node) $ Ordinary.minimumSizes $ Ordinary.rowsOf node

{- | Whether a node has two edges that accept a common term.

The edges here carry no equality constraints, so two edges with the same
symbol and arity share a term exactly when every child position does, and a
child position shares one exactly when the intersection of the two children
is productive.
-}
ambiguous :: [Edge Symbol EqConstraints] -> Bool
ambiguous alternatives =
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

-- | Whether an edge carries equality constraints.
constrained :: Edge Symbol EqConstraints -> Bool
constrained edge = case edgeConstraint edge of
    EmptyConstraints -> False
    _ -> True

{- | Compile a finite equality graph with shared ordinary rank plans.

Distinct constructor alternatives and direct-child equalities have compact
plans. Equal child positions select one term from the intersection of their
languages. Nested equality paths and overlapping alternatives use symbolic
equality contexts and intersection counts. Only a selected term is constructed.
-}
finiteAutomaton :: Node Symbol EqConstraints -> Either GenError (Static (Tree.Tree Symbol))
finiteAutomaton root =
    case State.evalState (buildNode root) Map.empty of
        Nothing -> Left EmptyGenerator
        Just ranked -> Right $ termStatic root ranked
  where
    buildNode node
        | null (nodeEdges node) = pure Nothing
        | otherwise = do
            cache <- State.get
            case Map.lookup (nodeIdentity node) cache of
                Just ranked -> pure ranked
                Nothing -> do
                    ranked <- buildAlternatives node
                    State.modify' $ Map.insert (nodeIdentity node) ranked
                    pure ranked

    buildAlternatives node
        | Set.size (Set.fromList $ map edgeSymbol edges) /= length edges = pure $ symbolic node
        | any (needsPathExpansion . edgeConstraint) edges = pure $ symbolic node
        | otherwise = do
            alternatives <- traverse buildEdge edges
            pure $ either (const Nothing) (Just . Ranked.share) $ Ranked.oneof (catMaybes alternatives)
      where
        edges = nodeEdges node

    buildEdge edge = case childGroups (length children) (edgeConstraint edge) of
        Nothing -> pure Nothing
        Just groups -> do
            selected <- traverse (buildGroup children) groups
            pure $ do
                rankedGroups <- sequence selected
                let slots = foldl' addGroup (pure Map.empty) (zip groups rankedGroups)
                pure $ (\values -> Tree.Node (edgeSymbol edge) [values Map.! index | index <- [0 .. length children - 1]]) <$> slots
      where
        children = edgeChildren edge
    buildGroup children positions =
        case [child | (index, child) <- zip [0 ..] children, index `elem` positions] of
            [] -> pure Nothing
            first : rest -> buildNode $ foldl' intersect first rest
    addGroup prefix (positions, ranked) =
        (\values term -> foldr (`Map.insert` term) values positions) <$> prefix <*> ranked

    symbolic node = do
        graph <- either (const Nothing) Just $ Interned.toFTA node
        named <- either (const Nothing) Just $ FTA.mapSymbols (\(Symbol name) -> name) graph
        let namedRoot = Interned.fromFTA named
        ranked <- either (const Nothing) Just $ symbolicRanked namedRoot
        pure $ fmap (fmap Symbol) ranked

-- | Whether a non-contradictory equality inspects below direct child roots.
needsPathExpansion :: EqConstraints -> Bool
needsPathExpansion constraints = case subsumptionOrderedEclasses constraints of
    Nothing -> False
    Just classes -> any (any ((/= EQ) . (`compareLength` 1) . unPath) . unPathEClass) classes

-- | Partition direct child positions into equality classes in child order.
childGroups :: Int -> EqConstraints -> Maybe [[Int]]
childGroups arity constraints = do
    classes <- subsumptionOrderedEclasses constraints
    equalities <- traverse (traverse childIndex . unPathEClass) classes
    pure $ foldl' merge (map pure [0 .. arity - 1]) equalities
  where
    childIndex target = case unPath target of
        [index] | index >= 0 && index < arity -> Just index
        _ -> Nothing
    merge groups [] = groups
    merge groups positions =
        let (equal, other) = partition (any (`elem` positions)) groups
         in sortOn (take 1) (concat equal : other)
