{-# LANGUAGE PatternSynonyms #-}

{- | Transitions, automata, and the structural validation of an LTA.

An LTA is an interned graph from "Data.CFTA.Interned" whose symbols carry
refinements and whose edges carry liquid constraints. Build it with 'Node',
'Edge', 'mkEdge', and 'Mu', or with "Data.CFTA.Refinement.Guard" when a guard
names the constructor arguments. 'validate' checks the paper's restriction
that no guard inspects a position whose node is recursive, and that each
ranked symbol keeps one arity.
-}
module Data.CFTA.Refinement.Automaton (
    Automaton,
    Transition,
    pattern Transition,
    transitionSymbol,
    transitionRefinement,
    transitionChildren,
    transitionConstraint,
    transitionEqualities,
    AutomatonError (..),
    validate,
    explicitView,
    fromViewError,
    located,
    automatonAlphabet,
    transitionsAt,
) where

import Data.Bifunctor (first)
import Data.Containers.ListUtils (nubOrdOn)
import qualified Data.IntMap.Strict as IntMap
import Data.List ((!?))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint.Equality (EqConstraints)
import Data.CFTA.Interned (
    Edge (InternedEdge),
    FTAViewError (..),
    InternedState (..),
    Node (..),
    UninternedEdge (..),
    edgeChildren,
    edgeConstraint,
    edgeSymbol,
    mkEdge,
    nodeEdges,
    nodeIdentity,
    toFTA,
 )
import Data.CFTA.Path (Path, unPath)
import Data.CFTA.Symbol (Symbol)

import Data.CFTA.Refinement.Constraint (LiquidConstraint (constraintEqualities), constraintPaths)
import Data.CFTA.Refinement.Types (LiquidSymbol (LiquidSymbol), Refinement)

-- | A liquid tree automaton: an interned graph with refined symbols and liquid constraints.
type Automaton = Node LiquidSymbol LiquidConstraint

-- | One refinement-labelled, constrained alternative of an LTA node.
type Transition = Edge LiquidSymbol LiquidConstraint

-- | Construct or match an LTA transition.
pattern Transition :: Symbol -> Refinement -> [Automaton] -> LiquidConstraint -> Transition
pattern Transition symbol refinement children constraint <-
    InternedEdge _ (UninternedEdge (LiquidSymbol symbol refinement) children constraint)
  where
    Transition symbol refinement children constraint =
        mkEdge (LiquidSymbol symbol refinement) children constraint

{-# COMPLETE Transition #-}

-- | Symbol at the root of a transition.
transitionSymbol :: Transition -> Symbol
transitionSymbol (Transition symbol _ _ _) = symbol

-- | Refinement formula at the root of a transition.
transitionRefinement :: Transition -> Refinement
transitionRefinement (Transition _ refinement _ _) = refinement

-- | Child nodes of a transition, from left to right.
transitionChildren :: Transition -> [Automaton]
transitionChildren = edgeChildren

-- | Complete equality and semantic constraint attached to a transition.
transitionConstraint :: Transition -> LiquidConstraint
transitionConstraint = edgeConstraint

-- | ECTA equality classes attached to a transition.
transitionEqualities :: Transition -> EqConstraints
transitionEqualities = constraintEqualities . transitionConstraint

-- | A structural error found while validating an automaton.
data AutomatonError
    = -- | A recursive reference is free in the root.
      OpenAutomaton
    | {- | A guard position reaches a recursive node, which would produce an
      unbounded logical obligation during semantic operations.
      -}
      CyclicGuardReference !Transition !Path
    | InconsistentArity !Symbol !Int !Int
    | -- | Named guard arguments do not match the constructor's child count.
      GuardArityMismatch !Symbol !Int !Int
    deriving (Eq, Show)

{- | Check the structure of an LTA.

The graph must be closed, each ranked symbol must keep one arity, and no
guard may inspect a position whose node is recursive. The check does not
enumerate terms or call a solver.
-}
validate :: Automaton -> Either AutomatonError ()
validate root = do
    view <- explicitView root
    consistentArity Map.empty [edge | (_, edges) <- alternativesOf, edge <- edges]
    let cyclic = FTA.cyclicStates view
        recursive node = Set.member (InternedState (nodeIdentity node)) cyclic
        offending =
            [ (edge, target)
            | (node, edges) <- alternativesOf
            , edge <- edges
            , target <- constraintPaths (edgeConstraint edge)
            , reached <- if null (unPath target) then [node] else nodesAt edge target
            , recursive reached
            ]
    case offending of
        (edge, target) : _ -> Left $ CyclicGuardReference edge target
        [] -> Right ()
  where
    alternativesOf = located root

    consistentArity _ [] = Right ()
    consistentArity known (Transition symbol _ children _ : rest) =
        case Map.lookup symbol known of
            Nothing -> consistentArity (Map.insert symbol (length children) known) rest
            Just expected
                | expected == length children -> consistentArity known rest
                | otherwise -> Left $ InconsistentArity symbol expected (length children)

-- | The explicit-state view of an LTA, with one state per reachable node.
explicitView :: Automaton -> Either AutomatonError (FTA.FTA InternedState LiquidSymbol LiquidConstraint)
explicitView = first viewError . toFTA
  where
    viewError OpenNode = OpenAutomaton
    viewError (InvalidFTA err) = fromViewError err

-- | Translate a structural error of the explicit view into the LTA vocabulary.
fromViewError :: FTA.FTAError InternedState LiquidSymbol -> AutomatonError
fromViewError (FTA.InconsistentArity (LiquidSymbol symbol _) expected actual) =
    InconsistentArity symbol expected actual
fromViewError err =
    error $
        "microcfta bug in Data.CFTA.Refinement.Automaton: the explicit view of an interned graph is malformed: " <> show err

{- | Every reachable node with its alternatives, in identity order.

A recursive node lists its unfolded alternatives, so the children of every
listed transition are again listed nodes.
-}
located :: Automaton -> [(Automaton, [Transition])]
located EmptyNode = []
located root = IntMap.elems $ collect IntMap.empty [root]
  where
    collect seen [] = seen
    collect seen (Rec _ : pending) = collect seen pending
    collect seen (node : pending)
        | IntMap.member ident seen = collect seen pending
        | otherwise = collect (IntMap.insert ident (node, edges) seen) (concatMap edgeChildren edges <> pending)
      where
        ident = nodeIdentity node
        edges = nodeEdges node

-- | Finite ranked alphabet used by an automaton.
automatonAlphabet :: Automaton -> Set.Set LiquidSymbol
automatonAlphabet root = Set.fromList [edgeSymbol edge | (_, edges) <- located root, edge <- edges]

{- | The nodes at a child-index path below a transition.

The first index selects a child of the transition; each further index selects
that child of every alternative of the nodes reached so far. The empty path
gives no nodes.
-}
nodesAt :: Transition -> Path -> [Automaton]
nodesAt edge target = case unPath target of
    [] -> []
    index : rest -> maybe [] (descend rest) (edgeChildren edge !? index)
  where
    descend [] node = [node]
    descend (index : rest) node =
        nubOrdOn nodeIdentity $
            concat
                [ descend rest child
                | alternative <- nodeEdges node
                , Just child <- [edgeChildren alternative !? index]
                ]

{- | Transitions reachable at a position below one transition (Definition 5).

The empty position denotes the supplied transition. A non-empty position
selects the alternatives of every node at that position.
-}
transitionsAt :: Transition -> Path -> [Transition]
transitionsAt edge target
    | null (unPath target) = [edge]
    | otherwise = concatMap nodeEdges $ nodesAt edge target
