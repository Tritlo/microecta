{-# LANGUAGE PatternSynonyms #-}

{- | Liquid tree automata over Liquid Fixpoint refinements.

An LTA is an interned graph whose symbols carry refinements. A transition has
a ranked symbol, child nodes, and the paper's Boolean constraint language
over paths into the candidate term. 'Same' is syntactic
equality and 'Entails' is semantic refinement implication. 'Satisfies' compares
a path with a literal requirement, avoiding phantom constant children.
'Holds' states a formula about the terms at several paths, and assumes each
term's refinement for its name. 'Substitute' applies the paper's
actual-for-formal position substitutions before semantic checks and syntactic
comparison. A stored refinement is a 'Formula', a Liquid Fixpoint expression
about the variable @v@. "Data.CFTA.Refinement.Expression" writes refinements
as Haskell functions of the value.

Recursive automata are accepted. As required by the LTA construction, a guard
may only inspect positions whose nodes are acyclic; recursive nodes can still
occur elsewhere in the generated term.

"Data.CFTA.Refinement.Guard" provides higher-level guard syntax in terms of constructor
arguments. This module also exposes the underlying constructors for tools that
need arbitrary paths.
-}
module Data.CFTA.Refinement (
    -- * Terms and refinements
    Symbol (Symbol),
    module Data.CFTA.Path,
    Formula,
    LiquidSymbol (..),
    eraseRefinements,

    -- * Guards
    Substitution (..),
    Guard (..),
    contractTermName,
    LiquidConstraint (..),
    unconstrainedConstraint,
    semanticConstraint,
    equalityConstraint,
    combineConstraints,
    constraintAsGuard,
    constraintIndicators,
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
    module Data.CFTA.Interned,
    module Data.CFTA.Enumeration,
    module Data.CFTA.Template,
    Automaton,
    Transition,
    pattern Transition,
    transitionSymbol,
    transitionRefinement,
    AutomatonError (..),
    validate,
    explicitView,
    automatonAlphabet,
    transitionsAt,

    -- * Pruning and denotation
    PruneError (..),
    prune,
    DenotationError (..),
    accepts,
    denotationAtMost,

    -- * Similarity and minimization
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
) where

import Data.CFTA.Enumeration
import Data.CFTA.Interned
import Data.CFTA.Path
import Data.CFTA.Symbol (Symbol (Symbol))
import Data.CFTA.Template

import Data.CFTA.Refinement.Automaton
import Data.CFTA.Refinement.Constraint
import Data.CFTA.Refinement.Denotation
import Data.CFTA.Refinement.Evaluate
import Data.CFTA.Refinement.Minimize
import Data.CFTA.Refinement.Prune
import Data.CFTA.Refinement.Types
import Data.CFTA.Refinement.Verdict
