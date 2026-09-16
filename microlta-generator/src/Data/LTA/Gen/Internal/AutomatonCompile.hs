{- | Compile a core LTA directly into a ranked generator.

The core 'prune' pass runs first. An equality-free, unambiguous result uses
the ordinary FTA ranker. Other equality languages use shared symbolic counts.
Unsupported semantic guards produce an error before any member is constructed.
-}
module Data.LTA.Gen.Internal.AutomatonCompile (
    compileAutomaton,
    compileAutomatonWith,
    compileAutomatonUpToDepth,
    compileAutomatonUpToDepthWith,
    compileBoundedAutomaton,
    countAutomaton,
    ensureUnconstrained,
    constraintTerms,
    symbolicGraph,
) where

import Data.Bifunctor (first)
import qualified Data.IntMap.Strict as IntMap
import Data.List (sortOn)
import qualified Data.Map.Strict as Map

import Data.ECTA.Gen.Internal.Symbolic (symbolicRankedWith)
import Data.ECTA.Paths (EqConstraints (EmptyConstraints), subsumptionOrderedEclasses, unPathEClass)
import Data.LTA
import Data.LTA.Gen.Internal.Bounded (boundAutomaton)
import Data.LTA.Gen.Internal.Error (GeneratorError (..), fromRankedError)
import Data.LTA.Gen.Internal.Types
import Data.LTA.Gen.Internal.Witness (cacheEntailment)
import qualified Data.Tree.FTA as FTA
import qualified Data.Tree.FTA.Gen.Internal.Automaton as Ordinary
import Data.Tree.FTA.Gen.Internal.Shrink (automatonShrinkRanks)
import qualified Data.Tree.FTA.Interned as Interned
import qualified Data.Tree.Gen as Tree
import Data.Tree.Term (Term (Term))

{- | Prune and rank a finite acyclic LTA.

The core's authoritative 'prune' pass runs first. If no syntactic equality
remains, the adapter counts accepting runs by dynamic programming and only
'unrank' materializes the chosen 'LiquidTerm'. Positive equality residuals are
compiled through the shared symbolic equality ranker.
Use 'compileAutomatonUpToDepth' for recursive automata or general constraints.
Shrinks reduce the tree node count and remain in the accepted language.
-}
compileAutomaton :: Entailment -> Automaton -> IO (Either GeneratorError (Compiled LiquidTerm))
compileAutomaton entailment =
    compileAutomatonWith entailment LiquidTerm

{- | Compile an LTA while folding each selected transition directly into a value.

The annotated witness remains available through 'generatedTerm', but is lazy.
QuickCheck sampling that only demands 'generatedValue' therefore avoids
constructing and immediately decoding an intermediate 'LiquidTerm'.
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
give 'InvalidPruning'; undecidable solver obligations give 'SolverUnknown'.
Each distinct 'LiquidTerm' has one rank, even when
multiple runs accept it. Ranks are deterministic for a fixed automaton and bound.
Shrinks stay in the accepted language and strictly reduce the tree node count.
-}
compileAutomatonUpToDepth ::
    Entailment -> Int -> Automaton -> IO (Either GeneratorError (Compiled LiquidTerm))
compileAutomatonUpToDepth entailment =
    compileAutomatonUpToDepthWith entailment LiquidTerm

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
    | otherwise = case boundAutomaton maximumHeight automaton of
        Left err -> pure $ Left $ InvalidSupport err
        Right bounded -> compilePrunedAutomaton entailment buildValue bounded

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
        case lowerToEqualityAutomaton pruned of
            Right acceptedSupport ->
                case ensureUnconstrained acceptedSupport >> compileUnconstrainedAutomaton buildValue acceptedSupport of
                    Right (ranked, shrinks) ->
                        Right $ Compiled (EqualitySupport acceptedSupport) ranked shrinks
                    Left (ResidualEquality _ _) -> compileSymbolicAutomaton buildValue (SymbolicSupport pruned) pruned
                    Left (AmbiguousAutomaton _) -> compileSymbolicAutomaton buildValue (SymbolicSupport pruned) pruned
                    Left err -> Left err
            Left _ -> compileSymbolicAutomaton buildValue (SymbolicSupport pruned) pruned
  where
    pruningError (PruneUnknown _) = SolverUnknown
    pruningError err = InvalidPruning err

-- | Count and unrank an equality-free reduced LTA as an ordinary FTA.
compileUnconstrainedAutomaton ::
    (Symbol -> Refinement -> [a] -> a) ->
    EqualityAutomaton ->
    Either GeneratorError (Tree.Ranked (Generated a), Integer -> [Integer])
compileUnconstrainedAutomaton buildValue acceptedSupport = do
    counts <- countAutomaton acceptedSupport
    ensureUnambiguous acceptedSupport $ Map.keys counts
    let total = Map.findWithDefault 0 (automatonInitial acceptedSupport) counts
    ranked <-
        first fromRankedError
            $ Tree.fromIndexedOnDemand
            $ Tree.Indexed
                total
                (generatedAtWith buildValue acceptedSupport counts)
    pure (ranked, automatonShrinkRanks (FTA.stripGuards acceptedSupport) counts)

-- | Compile Boolean equality over annotated symbols with exact unique ranks.
compileSymbolicAutomaton ::
    (Symbol -> Refinement -> [a] -> a) ->
    CompiledSupport ->
    Automaton ->
    Either GeneratorError (Compiled a)
compileSymbolicAutomaton buildValue support automaton = do
    mapM_
        validate
        [ (state, transitionConstraint transition)
        | (state, transitions) <- Map.toList $ automatonTransitions automaton
        , transition <- transitions
        ]
    (root, alphabet) <- symbolicGraph automaton
    terms <- first fromRankedError $ symbolicRankedWith interpret root
    let generated term = Generated 1 (foldTerm alphabet buildValue term) (foldTerm alphabet LiquidTerm term)
        size rank = either (const 0) nodeCount $ Tree.unrank terms rank
        shrinks rank = filter ((< size rank) . size) $ Tree.shrinkRank terms rank
    pure $ Compiled support (generated <$> terms) shrinks
  where
    validate (state, constraint) =
        first (InvalidPruning . ResidualLTAConstraint state) $ constraintTerms constraint
    interpret constraint = case constraintTerms constraint of
        Right terms -> terms
        Left _ -> error "compileSymbolicAutomaton: unsupported guard after validation"
    foldTerm alphabet build (Term identifier childTerms) =
        let LiquidSymbol symbol refinement = alphabet IntMap.! identifier
         in build symbol refinement $ map (foldTerm alphabet build) childTerms
    nodeCount :: Term Int -> Integer
    nodeCount (Term _ childTerms) = 1 + sum (map nodeCount childTerms)

-- | Give symbolic ranks a textual alphabet order independent of interning order.
symbolicGraph :: Automaton -> Either GeneratorError (Interned.Node Int LiquidConstraint, IntMap.IntMap LiquidSymbol)
symbolicGraph automaton = do
    renamed <- first (const RecursiveAutomaton) $ FTA.mapSymbols (identifiers Map.!) automaton
    root <- first (const RecursiveAutomaton) $ Interned.fromFTA renamed
    pure (root, IntMap.fromList $ zip [0 ..] alphabet)
  where
    alphabet =
        sortOn name
            $ Map.keys
            $ Map.fromList
                [ (FTA.transitionSymbol transition, ())
                | transitions <- Map.elems $ automatonTransitions automaton
                , transition <- transitions
                ]
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

{- | Require the pruned automaton to be an ordinary FTA before multiplying
child cardinalities.

Semantic guards are eliminated by LTA state splitting. Syntactic equality may
remain because equality between arbitrary subtrees is not a regular tree
language; it needs the ECTA counting path instead of an FTA product count.
-}
ensureUnconstrained :: EqualityAutomaton -> Either GeneratorError ()
ensureUnconstrained automaton =
    case [ (state, FTA.transitionGuard transition)
         | (state, transitions) <- Map.toList $ automatonTransitions automaton
         , transition <- transitions
         , FTA.transitionGuard transition /= EmptyConstraints
         ] of
        residual : _ -> Left $ uncurry ResidualEquality residual
        [] -> Right ()

-- | Count ordinary candidate runs through the common automaton compiler.
countAutomaton :: EqualityAutomaton -> Either GeneratorError (Map.Map State Integer)
countAutomaton = first (const RecursiveAutomaton) . Ordinary.countRuns

-- | Require distinct terms after constraints have been discharged.
ensureUnambiguous :: EqualityAutomaton -> [State] -> Either GeneratorError ()
ensureUnambiguous automaton states = case Ordinary.ambiguousState automaton states of
    Nothing -> Right ()
    Just state -> Left $ AmbiguousAutomaton state

-- | Decode the value and lazy witness through the same ordinary rank fold.
generatedAtWith ::
    (Symbol -> Refinement -> [a] -> a) ->
    EqualityAutomaton ->
    Map.Map State Integer ->
    Integer ->
    Generated a
generatedAtWith buildValue automaton counts rank =
    Generated
        1
        (Ordinary.foldAt (\(LiquidSymbol symbol refinement) -> buildValue symbol refinement) automaton counts rank)
        (Ordinary.foldAt (\(LiquidSymbol symbol refinement) -> LiquidTerm symbol refinement) automaton counts rank)
