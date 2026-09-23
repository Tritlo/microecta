{- | Semantic pruning and the complete reduction phase.

Pruning discharges a transition guard by splitting the nodes below it until
every observed position is homogeneous in what the guard reads. Combinations
that fail are removed, and an alternative whose child became empty goes with
them. Syntactic equalities first narrow the equal positions to their
intersection. Nodes are pruned bottom up and shared through their identity; a
recursive node is pruned to a fixed point, because a guard inside its body may
observe through the node itself.
-}
module Data.CFTA.Refinement.Prune (
    PruneError (..),
    prune,
    ReductionError (..),
    reduce,
) where

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Strict (StateT, evalStateT, gets, modify')
import Data.Bifunctor (first)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set

import Data.CFTA.Equality.Constraint (EqConstraints (EmptyConstraints))
import Data.CFTA.Equality.Operations (reduceEdgeIntersection)
import Data.CFTA.Interned (
    InternedMu (internedMuBody, internedMuId),
    Node (..),
    NodeId (..),
    RecNodeId (RecInt),
    createMu,
    edgeChildren,
    edgeConstraint,
    edgeSymbol,
    freeVars,
    mkEdge,
    nodeEdges,
    nodeIdentity,
    substFree,
 )
import Data.CFTA.Path (ChildIndex (..), unPath)

import Data.CFTA.Constraint (
    Constraint (..),
    Guard (..),
    guardPaths,
    splitGuard,
    symbolSensitivePaths,
 )
import Data.CFTA.Refinement.Automaton (
    Automaton,
    AutomatonError,
    Transition,
    validate,
 )
import Data.CFTA.Refinement.Evaluate (evaluateGuardWithShape, substitutionValues)
import Data.CFTA.Refinement.Minimize (
    MinimizeError,
    SimilarityError,
    Subtyping,
    minimize,
    similarity,
 )
import Data.CFTA.Refinement.Verdict (Entailment, Verdict (..))
import Data.CFTA.Symbol (Formula, Symbol (RefinedSymbol))

-- | A semantic obstacle encountered while pruning guarded transitions.
data PruneError
    = -- | The solver could not decide the guard of this transition.
      PruneUnknown !Transition
    | -- | The automaton is not a valid LTA.
      InvalidPrunedAutomaton !AutomatonError
    deriving (Eq, Show)

-- | Pruned nodes, node partitions, and the recursive nodes in scope.
data PruneBuild = PruneBuild
    { prunedNodes :: !(IntMap.IntMap Automaton)
    , splitMemo :: !(Map.Map (NodeId, PathPlan) [Variant])
    , binders :: !(IntMap.IntMap Automaton)
    }

type PruneM = StateT PruneBuild (ExceptT PruneError IO)

{- | Apply the paper's pruning rules and retain the resulting LTA.

A guard is discharged by partitioning the nodes at every finite position it
observes. A partition is homogeneous in the refinement needed by ordinary
entailment, or in both symbol and refinement where substitution names a value.
Successful combinations become specialized nodes. Failed combinations are
removed. The returned automaton keeps its equality classes and any guard the
sparse observations cannot decide. This is the paper's semantic-intersection
rule, expressed as node splitting without materializing an accepted tree.
-}
prune :: Entailment -> Automaton -> IO (Either PruneError Automaton)
prune entailment automaton = case validate automaton of
    Left err -> pure $ Left $ InvalidPrunedAutomaton err
    Right () ->
        runExceptT $
            evalStateT (pruneNode entailment automaton) (PruneBuild IntMap.empty Map.empty IntMap.empty)

-- | Prune one node, sharing the result through the node's identity.
pruneNode :: Entailment -> Automaton -> PruneM Automaton
pruneNode _ EmptyNode = pure EmptyNode
pruneNode _ node@(Rec _) = pure node
pruneNode entailment node = do
    known <- gets (IntMap.lookup ident . prunedNodes)
    case known of
        Just pruned -> pure pruned
        Nothing -> do
            pruned <- case node of
                InternedMu mu -> pruneMu entailment node mu
                _ -> Node . concat <$> traverse (pruneEdge entailment) (nodeEdges node)
            modify' $ \build -> build{prunedNodes = IntMap.insert ident pruned (prunedNodes build)}
            pure pruned
  where
    NodeId ident = nodeIdentity node

{- | Prune the body of a recursive node to a fixed point.

The body is pruned with its recursive reference left in place. If that
changed the node, the rebuilt node is pruned again, because a guard in the
body may observe through the reference.
-}
pruneMu :: Entailment -> Automaton -> InternedMu Symbol -> PruneM Automaton
pruneMu entailment node mu = do
    let NodeId ident = internedMuId mu
    modify' $ \build -> build{binders = IntMap.insert ident node (binders build)}
    body <- pruneNode entailment (internedMuBody mu)
    let rebuilt = createMu $ \self -> substFree (RecInt (internedMuId mu)) self body
    if rebuilt == node then pure node else pruneNode entailment rebuilt

-- | Prune the children of one transition, narrow them by its equalities, then discharge its guard.
pruneEdge :: Entailment -> Transition -> PruneM [Transition]
pruneEdge entailment edge = do
    children <- traverse (pruneNode entailment) (edgeChildren edge)
    let narrowed = reduceEdgeIntersection EmptyConstraints $ mkEdge (edgeSymbol edge) children (edgeConstraint edge)
    if EmptyNode `elem` edgeChildren narrowed
        then pure []
        else pruneSemantic entailment narrowed

-- | Discharge the semantic part of a transition's guard by specializing its children.
pruneSemantic :: Entailment -> Transition -> PruneM [Transition]
pruneSemantic entailment edge
    | semanticGuard == Top = pure [setGuard residualGuard edge]
    -- A recursive node that is being pruned has no pruned form yet, so the
    -- transition keeps its whole guard. Enumeration and 'accepts' check it.
    | not (all (null . freeVars) (edgeChildren edge))
    , readsThroughRecursion (planGuard semanticGuard) (edgeChildren edge) =
        pure [edge]
    | otherwise = do
        candidates <- specializations semanticGuard edge
        check [] candidates
  where
    (semanticGuard, residualGuard) = splitGuard $ constraintGuard $ edgeConstraint edge

    check retained [] = pure $ reverse retained
    check retained ((specialized, resolved) : rest) = do
        verdict <-
            liftIO $
                evaluateGuardWithShape
                    entailment
                    (lookupResolved resolved)
                    (lookupLeaf resolved)
                    semanticGuard
        case verdict of
            Yes -> check (setGuard residualGuard specialized : retained) rest
            No -> check retained rest
            Unknown
                | hasAmbiguousActuals resolved -> pure [edge]
                | otherwise -> throwError $ PruneUnknown edge

    hasAmbiguousActuals resolved =
        not . Set.null . snd $
            substitutionValues
                (lookupResolved resolved)
                (lookupLeaf resolved)
                (\_ _ -> Nothing)
                semanticGuard

    lookupResolved resolved target = do
        (RefinedSymbol symbol refinement, _) <- Map.lookup (unPath target) resolved
        pure (symbol, refinement)

    lookupLeaf resolved target = snd <$> Map.lookup (unPath target) resolved

{- | Whether a path plan reaches a recursive reference below the children of a
transition.

Only a recursive node whose body is being pruned leaves a reference in its
children: the edges of a closed recursive node unfold to the node itself. A
split through such a reference would copy the unpruned node into its variant,
and pruning the variant would prune the node again without end.
-}
readsThroughRecursion :: PathPlan -> [Automaton] -> Bool
readsThroughRecursion plan children =
    or
        [ reaches child childPlan
        | (index, childPlan) <- Map.toList $ planChildren plan
        , child <- take 1 $ drop index children
        ]
  where
    reaches (Rec _) _ = True
    -- A node without free references has none below it.
    reaches node childPlan =
        not (null $ freeVars node) && any (readsThroughRecursion childPlan . edgeChildren) (nodeEdges node)

-- | Replace a transition's guard without changing its symbol or children.
setGuard :: Guard -> Transition -> Transition
setGuard guard edge =
    mkEdge (edgeSymbol edge) (edgeChildren edge) (edgeConstraint edge){constraintGuard = guard}

-- | How precisely one observed position must be partitioned.
data ObservationNeed
    = RefinementNeed
    | SymbolNeed
    deriving (Eq, Ord, Show)

-- | Trie of the finite term positions inspected by one semantic guard.
data PathPlan = PathPlan
    { planObservation :: !(Maybe ObservationNeed)
    , planChildren :: !(Map.Map Int PathPlan)
    }
    deriving (Eq, Ord, Show)

-- | One partition value. Symbol observations also record whether the term is a leaf.
data Observation
    = RefinementObservation !Formula
    | SymbolObservation !Symbol !Bool
    deriving (Eq, Ord, Show)

-- | Observations at relative positions, and the symbols substitution may read there.
type Signature = Map.Map [ChildIndex] Observation

type Symbols = Map.Map [ChildIndex] (Symbol, Bool)

-- | One node whose language is homogeneous at every planned position.
data Variant = Variant
    { variantNode :: !Automaton
    , variantSignature :: !Signature
    , variantSymbols :: !Symbols
    }

-- | Every homogeneous child specialization required to evaluate one guard.
specializations :: Guard -> Transition -> PruneM [(Transition, Symbols)]
specializations guard edge = do
    children <- specializeChildren (planChildren plan) (edgeChildren edge)
    pure
        [ (mkEdge (edgeSymbol edge) specialized (edgeConstraint edge), rootSymbols `Map.union` childSymbols)
        | (specialized, _, childSymbols) <- children
        ]
  where
    plan = planGuard guard
    rootSymbols = rootSymbolsOf plan edge

-- | The root symbol observation of a transition, if the plan reads the root.
rootSymbolsOf :: PathPlan -> Transition -> Symbols
rootSymbolsOf plan edge = case planObservation plan of
    Nothing -> Map.empty
    Just _ -> Map.singleton [] (edgeSymbol edge, null $ edgeChildren edge)

-- | Partition one node's language by the observations in a path plan.
specializeNode :: Automaton -> PathPlan -> PruneM [Variant]
specializeNode node plan = do
    known <- gets (Map.lookup key . splitMemo)
    case known of
        Just variants -> pure variants
        Nothing -> do
            edges <- alternatives node
            candidates <- concat <$> traverse (specializeEdge plan) edges
            let variants =
                    [ Variant (Node group) signature symbols
                    | (signature, symbols, group) <- groupVariants candidates
                    ]
            modify' $ \build -> build{splitMemo = Map.insert key variants (splitMemo build)}
            pure variants
  where
    key = (nodeIdentity node, plan)

-- | The alternatives of a node, resolving a reference to the recursive node it names.
alternatives :: Automaton -> PruneM [Transition]
alternatives (Rec (RecInt (NodeId ident))) = do
    binder <- gets (IntMap.lookup ident . binders)
    pure $ maybe [] nodeEdges binder
alternatives node = pure $ nodeEdges node

-- | Specialize one transition inside a node being partitioned.
specializeEdge :: PathPlan -> Transition -> PruneM [(Signature, Symbols, Transition)]
specializeEdge plan edge = do
    children <- specializeChildren (planChildren plan) (edgeChildren edge)
    pure
        [ ( rootSignature `Map.union` childSignature
          , rootSymbols `Map.union` childSymbols
          , mkEdge (edgeSymbol edge) specialized (edgeConstraint edge)
          )
        | (specialized, childSignature, childSymbols) <- children
        ]
  where
    rootSignature = case planObservation plan of
        Nothing -> Map.empty
        Just need -> Map.singleton [] $ observe need edge
    rootSymbols = rootSymbolsOf plan edge

-- | Cartesian product of child variants, sharing every unobserved child.
specializeChildren :: Map.Map Int PathPlan -> [Automaton] -> PruneM [([Automaton], Signature, Symbols)]
specializeChildren plans = go 0
  where
    go _ [] = pure [([], Map.empty, Map.empty)]
    go index (child : rest) = do
        variants <- case Map.lookup index plans of
            Nothing -> pure [Variant child Map.empty Map.empty]
            Just plan -> specializeNode child plan
        suffixes <- go (index + 1) rest
        pure
            [ ( variantNode variant : suffixNodes
              , prefixMap (ChildIndex index) (variantSignature variant) `Map.union` suffixSignature
              , prefixMap (ChildIndex index) (variantSymbols variant) `Map.union` suffixSymbols
              )
            | variant <- variants
            , (suffixNodes, suffixSignature, suffixSymbols) <- suffixes
            ]

    -- Prefix every relative observation path by one child index.
    prefixMap :: ChildIndex -> Map.Map [ChildIndex] value -> Map.Map [ChildIndex] value
    prefixMap index = Map.mapKeysMonotonic (index :)

-- | Regroup transition candidates by signature without disturbing first-seen order.
groupVariants :: [(Signature, Symbols, Transition)] -> [(Signature, Symbols, [Transition])]
groupVariants = foldl' insertVariant []
  where
    insertVariant [] (signature, symbols, edge) = [(signature, symbols, [edge])]
    insertVariant (group@(signature, symbols, edges) : rest) candidate@(candidateSignature, _, edge)
        | signature == candidateSignature = (signature, symbols, edges <> [edge]) : rest
        | otherwise = group : insertVariant rest candidate

-- | Observation used to partition a node's transitions.
observe :: ObservationNeed -> Transition -> Observation
observe RefinementNeed edge = let RefinedSymbol _ refinement = edgeSymbol edge in RefinementObservation refinement
observe SymbolNeed edge = SymbolObservation (edgeSymbol edge) (null $ edgeChildren edge)

-- | Construct the observation trie for every position read by a semantic guard.
planGuard :: Guard -> PathPlan
planGuard guard = foldl' (flip $ uncurry insertPlan) emptyPlan observations
  where
    observations =
        [ (unPath target, if Set.member target sensitive then SymbolNeed else RefinementNeed)
        | target <- Set.toList $ Set.fromList $ guardPaths guard
        ]
      where
        sensitive = Set.fromList $ symbolSensitivePaths guard

-- | An observation plan containing no positions.
emptyPlan :: PathPlan
emptyPlan = PathPlan Nothing Map.empty

-- | Insert or strengthen one observed position in a path trie.
insertPlan :: [ChildIndex] -> ObservationNeed -> PathPlan -> PathPlan
insertPlan [] need plan =
    plan{planObservation = Just $ maybe need (max need) $ planObservation plan}
insertPlan (ChildIndex index : rest) need plan =
    plan
        { planChildren =
            Map.alter
                (Just . insertPlan rest need . fromMaybe emptyPlan)
                index
                (planChildren plan)
        }

-- | Failure in the paper's prune-similarity-minimize reduction phase.
data ReductionError
    = -- | Semantic pruning failed.
      ReductionPrune !PruneError
    | -- | Similarity inference failed.
      ReductionSimilarity !SimilarityError
    | -- | Minimization failed.
      ReductionMinimize !MinimizeError
    deriving (Eq, Show)

{- | Apply one complete LTA reduction phase.

This keeps the paper's reduction order: semantic pruning, similarity inference,
then minimization.
-}
reduce :: Entailment -> Subtyping -> Automaton -> IO (Either ReductionError Automaton)
reduce entailment subtyping automaton = do
    pruned <- prune entailment automaton
    case pruned of
        Left err -> pure $ Left $ ReductionPrune err
        Right reduced -> do
            inferred <- similarity subtyping reduced
            pure $ do
                related <- first ReductionSimilarity inferred
                first ReductionMinimize $ minimize reduced related
