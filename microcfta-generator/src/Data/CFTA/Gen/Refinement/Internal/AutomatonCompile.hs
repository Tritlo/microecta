{- | Compile a core LTA directly into a ranked generator.

The core 'prune' pass runs first. A result without constraints uses the
ordinary FTA ranker on the explicit view of the graph. Other languages use
shared symbolic counts over the pruned constraints. Unsupported semantic
guards produce an error before any member is constructed.
-}
module Data.CFTA.Gen.Refinement.Internal.AutomatonCompile (
    compileAutomaton,
    compileAutomatonWith,
    compileAutomatonUpToDepth,
    compileAutomatonUpToDepthWith,
    compileBoundedAutomaton,
    View,
    automatonView,
    countAutomaton,
    distinctCounts,
    constraintTerms,
    symbolicGraph,
) where

import Data.Bifunctor (first)
import qualified Data.CFTA as FTA
import Data.CFTA.Constraint.Equality (subsumptionOrderedEclasses, unPathEClass)
import Data.CFTA.Enumeration (unconstrained)
import Data.CFTA.Gen.Equality.Internal.Symbolic (symbolicRankedWith)
import qualified Data.CFTA.Gen.Internal.Automaton as Ordinary
import Data.CFTA.Gen.Internal.Shrink (automatonShrinkRanks)
import Data.CFTA.Gen.Refinement.Internal.Error (GeneratorError (..), fromRankedError)
import Data.CFTA.Gen.Refinement.Internal.Types
import Data.CFTA.Gen.Refinement.Internal.Witness (cacheEntailment)
import qualified Data.CFTA.Ranked as Ranked
import Data.CFTA.Refinement
import qualified Data.IntMap.Strict as IntMap
import Data.List (sortOn)
import qualified Data.Map.Strict as Map
import qualified Data.Tree as Tree

{- | Prune and rank a finite acyclic LTA.

The core's authoritative 'prune' pass runs first. If no constraint remains,
the adapter counts accepting runs by dynamic programming and only 'unrank'
materializes the chosen 'Tree.Tree' 'LiquidSymbol'. Residual equalities are
compiled through the shared symbolic equality ranker. Use
'compileAutomatonUpToDepth' for recursive automata or general constraints.
Shrinks reduce the tree node count and remain in the accepted language.
-}
compileAutomaton :: Entailment -> Automaton -> IO (Either GeneratorError (Compiled (Tree.Tree LiquidSymbol)))
compileAutomaton entailment =
    compileAutomatonWith entailment (\symbol refinement -> Tree.Node (LiquidSymbol symbol refinement))

{- | Compile an LTA while folding each selected transition directly into a value.

The annotated witness remains available through 'generatedTerm', but is lazy.
QuickCheck sampling that only demands 'generatedValue' therefore avoids
constructing and immediately decoding an intermediate 'Tree.Tree' 'LiquidSymbol'.
-}
compileAutomatonWith ::
    Entailment ->
    (Symbol -> Refinement -> [a] -> a) ->
    Automaton ->
    IO (Either GeneratorError (Compiled a))
compileAutomatonWith uncachedEntailment buildValue automaton = do
    entailment <- cacheEntailment uncachedEntailment
    compilePrunedAutomaton entailment buildValue automaton

{- | Compile every accepted term up to the given tree height.

A leaf has height zero. A negative bound or empty language gives 'EmptyGenerator'.
The compiler bounds the graph, then counts it symbolically. Unsupported guards
give 'ResidualGuard'; undecidable solver obligations give 'SolverUnknown'.
Each distinct 'Tree.Tree' 'LiquidSymbol' has one rank, even when
multiple runs accept it. Ranks are deterministic for a fixed automaton and bound.
Shrinks stay in the accepted language and strictly reduce the tree node count.
-}
compileAutomatonUpToDepth ::
    Entailment -> Int -> Automaton -> IO (Either GeneratorError (Compiled (Tree.Tree LiquidSymbol)))
compileAutomatonUpToDepth entailment =
    compileAutomatonUpToDepthWith entailment (\symbol refinement -> Tree.Node (LiquidSymbol symbol refinement))

{- | Compile a bounded LTA with a lazy fold for each selected domain value.

The fold does not change term ranks or shrinking. Distinct accepted terms keep
separate ranks even when the fold returns equal values.
-}
compileAutomatonUpToDepthWith ::
    Entailment ->
    (Symbol -> Refinement -> [a] -> a) ->
    Int ->
    Automaton ->
    IO (Either GeneratorError (Compiled a))
compileAutomatonUpToDepthWith uncachedEntailment buildValue maximumHeight automaton =
    do
        entailment <- cacheEntailment uncachedEntailment
        compileBoundedAutomaton entailment buildValue maximumHeight automaton

-- | Compile an imported automaton without enumerating its language.
compileBoundedAutomaton ::
    Entailment ->
    (Symbol -> Refinement -> [a] -> a) ->
    Int ->
    Automaton ->
    IO (Either GeneratorError (Compiled a))
compileBoundedAutomaton entailment buildValue maximumHeight automaton
    | maximumHeight < 0 = pure $ Left EmptyGenerator
    | otherwise = compilePrunedAutomaton entailment buildValue (boundDepth maximumHeight automaton)

-- | Compile pruned support with the caller's scoped entailment cache.
compilePrunedAutomaton ::
    Entailment ->
    (Symbol -> Refinement -> [a] -> a) ->
    Automaton ->
    IO (Either GeneratorError (Compiled a))
compilePrunedAutomaton entailment buildValue automaton = do
    reduced <- prune entailment automaton
    pure $ do
        pruned <- first pruningError reduced
        view <- automatonView pruned
        counted <- if unconstrained pruned then distinctCounts view else pure Nothing
        case counted of
            Just counts -> do
                (ranked, shrinks) <- compileUnconstrainedAutomaton buildValue view counts
                pure $ Compiled (AutomatonSupport pruned) ranked shrinks
            Nothing -> compileSymbolicAutomaton buildValue pruned view
  where
    pruningError (PruneUnknown _) = SolverUnknown
    pruningError err = InvalidPruning err

-- | The explicit-state view of an LTA, with one state per reachable node.
type View = FTA.FTA InternedState LiquidSymbol LiquidConstraint

-- | Expose an LTA as an explicit-state automaton, or report why it is not one.
automatonView :: Automaton -> Either GeneratorError View
automatonView = first InvalidSupport . explicitView

-- | Count and unrank a constraint-free, unambiguous pruned LTA as an ordinary FTA.
compileUnconstrainedAutomaton ::
    (Symbol -> Refinement -> [a] -> a) ->
    View ->
    Map.Map InternedState Integer ->
    Either GeneratorError (Ranked.Ranked (Generated a), Integer -> [Integer])
compileUnconstrainedAutomaton buildValue view counts = do
    let total = Map.findWithDefault 0 (FTA.initialState view) counts
    ranked <-
        first fromRankedError
            $ Ranked.fromIndexedOnDemand
            $ Ranked.Indexed
                total
                (generatedAtWith buildValue view counts)
    pure (ranked, automatonShrinkRanks (FTA.dropConstraints view) counts)

-- | Compile Boolean equality over annotated symbols with exact unique ranks.
compileSymbolicAutomaton ::
    (Symbol -> Refinement -> [a] -> a) ->
    Automaton ->
    View ->
    Either GeneratorError (Compiled a)
compileSymbolicAutomaton buildValue pruned view = do
    mapM_ (first ResidualGuard . constraintTerms . FTA.transitionConstraint) (viewTransitions view)
    (root, alphabet) <- symbolicGraph view
    terms <- first fromRankedError $ symbolicRankedWith interpret root
    let generated term = Generated 1 (foldTerm alphabet buildValue term) (fmap (alphabet IntMap.!) term)
        size rank = either (const 0) nodeSize $ Ranked.unrank terms rank
        shrinks rank = filter ((< size rank) . size) $ Ranked.shrinkRank terms rank
    pure $ Compiled (AutomatonSupport pruned) (generated <$> terms) shrinks
  where
    interpret constraint = case constraintTerms constraint of
        Right terms -> terms
        Left _ -> error "compileSymbolicAutomaton: unsupported guard after validation"
    foldTerm alphabet build = Tree.foldTree $ \identifier childValues ->
        let LiquidSymbol symbol refinement = alphabet IntMap.! identifier
         in build symbol refinement childValues
    nodeSize :: Tree.Tree Int -> Integer
    nodeSize = Tree.foldTree $ \_ counts -> 1 + sum counts

-- | Every transition of the explicit view, in table order.
viewTransitions :: View -> [FTA.Transition InternedState LiquidSymbol LiquidConstraint]
viewTransitions = concat . Map.elems . FTA.transitionTable

-- | Give symbolic ranks a textual alphabet order independent of interning order.
symbolicGraph :: View -> Either GeneratorError (Node Int LiquidConstraint, IntMap.IntMap LiquidSymbol)
symbolicGraph view = do
    case FTA.cycleState view of
        Just _ -> Left RecursiveAutomaton
        Nothing -> Right ()
    renamed <- first (const RecursiveAutomaton) $ FTA.mapSymbols (identifiers Map.!) view
    pure (fromFTA renamed, IntMap.fromList $ zip [0 ..] alphabet)
  where
    alphabet =
        sortOn name
            $ Map.keys
            $ Map.fromList [(FTA.transitionSymbol transition, ()) | transition <- viewTransitions view]
    name (LiquidSymbol symbol refinement) = (show symbol, show refinement)
    identifiers = Map.fromList $ zip alphabet [0 ..]

-- | Express a residual liquid constraint as a sum of positive equalities.
constraintTerms :: LiquidConstraint -> Either Guard [(Integer, [[Path]])]
constraintTerms constraint = do
    semantic <- guardTerms $ constraintGuard constraint
    pure $ conjoin ordinary semantic
  where
    ordinary = maybe [] (\classes -> [(1, map unPathEClass classes)]) $ subsumptionOrderedEclasses $ constraintEqualities constraint

    guardTerms Top = Right [(1, [])]
    guardTerms Bottom = Right []
    guardTerms (Same left right) = Right [(1, [[left, right]])]
    guardTerms (Not guard) = complement <$> guardTerms guard
    guardTerms (And guards) = foldl' conjoin [(1, [])] <$> traverse guardTerms guards
    guardTerms (Or guards) = complement . foldl' conjoin [(1, [])] . map complement <$> traverse guardTerms guards
    guardTerms guard = Left guard

    complement terms = (1, []) : [(negate weight, classes) | (weight, classes) <- terms]
    conjoin left right =
        [ (leftWeight * rightWeight, leftClasses <> rightClasses)
        | (leftWeight, leftClasses) <- left
        , (rightWeight, rightClasses) <- right
        ]

-- | Count ordinary candidate runs through the common automaton compiler.
countAutomaton :: View -> Either GeneratorError (Map.Map InternedState Integer)
countAutomaton = first (const RecursiveAutomaton) . Ordinary.countRuns

{- | Exact accepting-run counts of a view whose runs are distinct terms.

The result is 'Nothing' when several runs accept one term, because then run
counts do not count terms and the symbolic ranker must be used instead.
-}
distinctCounts :: View -> Either GeneratorError (Maybe (Map.Map InternedState Integer))
distinctCounts view = do
    counts <- countAutomaton view
    pure $ case Ordinary.ambiguousState view (Map.keys counts) of
        Nothing -> Just counts
        Just _ -> Nothing

-- | Decode the value and lazy witness through the same ordinary rank fold.
generatedAtWith ::
    (Symbol -> Refinement -> [a] -> a) ->
    View ->
    Map.Map InternedState Integer ->
    Integer ->
    Generated a
generatedAtWith buildValue view counts rank =
    Generated
        1
        (Ordinary.foldAt (\(LiquidSymbol symbol refinement) -> buildValue symbol refinement) view counts rank)
        (Ordinary.foldAt Tree.Node view counts rank)
