{-# LANGUAGE OverloadedStrings #-}

{- | The reference semantics of an LTA.

'accepts' decides one annotated term. 'denotationAtMost' lists the Figure 6
denotation up to a depth bound. The tests check the generators against these
two functions, and check 'denotationAtMost' against "Data.CFTA.Simple".
-}
module Data.CFTA.Refinement.Denotation (
    DenotationError (..),
    accepts,
    denotationAtMost,
) where

import Control.Monad (filterM)
import Control.Monad.Except (runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Data.Containers.ListUtils (nubOrd)
import Data.IORef (newIORef, readIORef, writeIORef)
import qualified Language.Fixpoint.Types as Fixpoint

import Data.CFTA.Constraint (Constraint)
import Data.CFTA.Enumeration (plainTermsAtMost, runs, unconstrained)
import Data.CFTA.Index (Depth (..))
import Data.CFTA.Internal.Tree (acceptsBy, andM)
import Data.CFTA.Interned (boundDepth, edgeChildren, edgeConstraint, edgeSymbol, nodeEdges)
import Data.CFTA.Refinement.Automaton (Automaton)
import Data.CFTA.Refinement.Evaluate (evaluateConstraint)
import Data.CFTA.Refinement.Verdict (Entailment, Verdict (..))
import Data.CFTA.Symbol (Symbol (RefinedSymbol))
import Data.CFTA.Term (Term)

-- | Failure while computing the bounded denotation from Figure 6.
data DenotationError
    = -- | The solver could not decide a transition's guard on the subterm the transition built.
      DenotationUnknown Constraint (Term Symbol)
    deriving (Eq, Show)

{- | Decide whether an annotated term is accepted at the root.

The result is 'Yes' when some run accepts the term with every guard decided
'Yes'. It is 'No' when no run accepts the term and the solver decided every
guard the search evaluated. It is 'Unknown' otherwise. A guard is decided
only after the children of its transition have accepted their subterms. When
the search comes to a subterm again with the same node, it uses the first
result, so the solver decides each guard at most once at each position in the
term.
-}
accepts :: Entailment -> Automaton -> Term Symbol -> IO Verdict
accepts entailment automaton term = do
    undecided <- newIORef False
    accepted <- acceptsBy nodeEdges edgeSymbol edgeChildren (check undecided) automaton term
    unknown <- readIORef undecided
    pure $ if accepted then Yes else if unknown then Unknown else No
  where
    check undecided _ edge candidate = do
        verdict <- evaluateConstraint entailment (edgeConstraint edge) candidate
        case verdict of
            Yes -> pure True
            No -> pure False
            Unknown -> writeIORef undecided True >> pure False

{- | List the Figure 6 denotation up to a depth bound.

A leaf has depth zero. The bound makes the result finite for a cyclic LTA. A
graph without constraints is listed level by level up to the bound. Otherwise
'runs' lists the bounded graph on the shared enumerator: path equalities are
solved by unification, and the solver decides each remaining guard on the
complete subterm its transition built. A term is accepted when the guards of
some run all hold. The result has each term once, in the order of the runs,
because the paper defines a set of terms. Check a generator against it on
bounded inputs.
-}
denotationAtMost :: Entailment -> Depth -> Automaton -> IO (Either DenotationError [Term Symbol])
denotationAtMost entailment bound automaton
    | bound < 0 = pure (Right [])
    | unconstrained automaton = pure (Right (plainTermsAtMost bound automaton))
    | otherwise = runExceptT $ do
        accepted <- filterM (andM . map decide . snd) (runs recursion bounded)
        pure $ nubOrd $ map fst accepted
  where
    bounded = boundDepth bound automaton
    recursion = RefinedSymbol "Mu" Fixpoint.PTrue
    decide (constraint, term) = do
        verdict <- liftIO $ evaluateConstraint entailment constraint term
        case verdict of
            Yes -> pure True
            No -> pure False
            Unknown -> throwError (DenotationUnknown constraint term)
