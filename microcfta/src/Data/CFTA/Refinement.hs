{-# LANGUAGE PatternSynonyms #-}

{- | Liquid tree automata over Liquid Fixpoint refinements.

An LTA transition has a ranked symbol, child states, and the paper's Boolean
constraint language over paths into the candidate term. 'Same' is syntactic
equality and 'Entails' is semantic refinement implication. 'Satisfies' compares
a path with a literal requirement, avoiding phantom constant children.
'Substitute' applies the paper's actual-for-formal position substitutions before
semantic checks and syntactic comparison. Refinements are Liquid Fixpoint
expressions.

Recursive automata are accepted. As required by the LTA construction, a guard
may only inspect positions whose states are acyclic; recursive states can still
occur elsewhere in the generated term.

"Data.CFTA.Refinement.Guard" provides higher-level guard syntax in terms of constructor
arguments. This module also exposes the underlying constructors for tools that
need arbitrary paths.
-}
module Data.CFTA.Refinement (
    -- * Terms and refinements
    Symbol (Symbol),
    Path,
    path,
    unPath,
    Refinement,
    LiquidSymbol (..),
    eraseRefinements,

    -- * Guards
    Substitution (..),
    Guard (..),
    LiquidConstraint (..),
    unconstrainedConstraint,
    semanticConstraint,
    equalityConstraint,
    combineConstraints,
    constraintAsGuard,
    guardPaths,
    constraintPaths,
    Verdict (..),
    Entailment (Entailment, entails),
    entailmentWithBindings,
    entailsWithBindings,
    RefinementRelation (..),
    refinementRelation,
    SemanticIntersection (..),
    semanticIntersection,
    evaluateGuard,
    evaluateGuardWithShape,
    evaluateConstraint,

    -- * Automata
    State (..),
    Transition,
    pattern Transition,
    transitionSymbol,
    transitionRefinement,
    transitionChildren,
    transitionConstraint,
    transitionEqualities,
    Automaton,
    ViewPath,
    StateView (..),
    toTree,
    EqualityAutomaton,
    AutomatonError (..),
    InternedAutomatonError (..),
    fromInterned,
    annotateFTA,
    PruneError (..),
    EnumerationError (..),
    TransitionId (..),
    Subtyping (..),
    refinementSubtypingBy,
    Similarity,
    SimilarityError (..),
    similarity,
    similarityPairs,
    MinimizeError (..),
    minimize,
    ReductionError (..),
    reduce,
    automatonStates,
    automatonAlphabet,
    automatonInitial,
    automatonTransitions,
    transitionsAt,
    mkAutomaton,
    mkAutomatonWithFinals,
    lowerToEqualityAutomaton,
    pruneToECTA,
    prune,
    accepts,
    denotationAtMost,
) where

import Data.CFTA.Path (Path, path, unPath)
import Data.CFTA.Symbol (Symbol (Symbol))

import Data.CFTA.Refinement.Automaton
import Data.CFTA.Refinement.Constraint
import Data.CFTA.Refinement.Denotation
import Data.CFTA.Refinement.Evaluate
import Data.CFTA.Refinement.Minimize
import Data.CFTA.Refinement.Prune
import Data.CFTA.Refinement.Types
import Data.CFTA.Refinement.Verdict
