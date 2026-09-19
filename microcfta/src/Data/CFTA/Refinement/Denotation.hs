{-# LANGUAGE OverloadedStrings #-}

{- | The reference semantics of an LTA.

'accepts' decides one annotated term. 'denotationAtMost' materializes the
Figure 6 denotation up to a height bound. Both are deliberately simple, so they
serve as the oracle that generator backends are checked against.
-}
module Data.CFTA.Refinement.Denotation (
    EnumerationError (..),
    accepts,
    denotationAtMost,
) where

import Control.Monad (filterM)
import Control.Monad.Except (runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Data.Containers.ListUtils (nubOrd)
import Data.IORef (newIORef, readIORef, writeIORef)
import qualified Data.Tree as Tree
import qualified Language.Fixpoint.Types as Fixpoint

import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint (..))
import Data.CFTA.Constraint.Equality (EqConstraints (EmptyConstraints))
import Data.CFTA.Enumeration (runs)
import Data.CFTA.Interned (fromFTA)
import Data.CFTA.Refinement.Automaton (Automaton, transitionConstraint)
import Data.CFTA.Refinement.Constraint (LiquidConstraint)
import Data.CFTA.Refinement.Evaluate (evaluateConstraint)
import Data.CFTA.Refinement.Types (LiquidSymbol (LiquidSymbol))
import Data.CFTA.Refinement.Verdict (Entailment, Verdict (..))

-- | Failure while computing the bounded denotation from Figure 6.
data EnumerationError
    = -- | The solver could not decide a transition's guard on the subterm the transition built.
      EnumerationUnknown LiquidConstraint (Tree.Tree LiquidSymbol)
    deriving (Eq, Show)

{- | Decide whether an annotated term is accepted from the initial state.

The result is 'Yes' when some run accepts the term with every guard decided
'Yes'. It is 'No' when no run accepts the term and the solver decided every
guard the search evaluated. It is 'Unknown' otherwise.
-}
accepts :: Entailment -> Automaton -> Tree.Tree LiquidSymbol -> IO Verdict
accepts entailment automaton term = do
    undecided <- newIORef False
    accepted <- FTA.acceptsM (check undecided) automaton term
    unknown <- readIORef undecided
    pure $ if accepted then Yes else if unknown then Unknown else No
  where
    check undecided _ transition candidate = do
        verdict <- evaluateConstraint entailment (transitionConstraint transition) candidate
        case verdict of
            Yes -> pure True
            No -> pure False
            Unknown -> writeIORef undecided True >> pure False

{- | Materialize the Figure 6 denotation up to a tree-height bound.

A leaf has height zero. The bound makes this reference interpreter total for
cyclic LTAs as well as acyclic ones. The bounded automaton is interned and
listed by the shared enumerator: path equalities are solved by unification,
and the solver decides each remaining guard on the complete subterm its
transition built. A term is accepted when the guards of some run all hold.
An automaton whose transitions carry no constraint is listed level by level
without interning. The result has each term once, in enumeration order,
because the paper defines a set of terms even when several runs accept the
same tree. This is the
authoritative, deliberately simple semantics oracle; generator backends are
optimizations and should be checked against it on bounded inputs.
-}
denotationAtMost :: Entailment -> Int -> Automaton -> IO (Either EnumerationError [Tree.Tree LiquidSymbol])
denotationAtMost entailment bound automaton
    | bound < 0 = pure (Right [])
    | all (all plain) (FTA.transitionTable bounded) = pure (Right (FTA.terms bounded))
    | otherwise = runExceptT $ do
        accepted <- filterM (allM . map decide . snd) (runs recursion root)
        pure $ nubOrd $ map fst accepted
  where
    bounded = FTA.boundDepth bound automaton
    plain transition =
        equalities (FTA.transitionConstraint transition) == EmptyConstraints
            && not (residual (FTA.transitionConstraint transition))
    root = case fromFTA bounded of
        Left err -> error $ "microcfta bug in Data.CFTA.Refinement.denotationAtMost: a depth-bounded automaton is cyclic: " <> show err
        Right node -> node
    recursion = LiquidSymbol "Mu" Fixpoint.PTrue
    decide (constraint, term) = do
        verdict <- liftIO $ evaluateConstraint entailment constraint term
        case verdict of
            Yes -> pure True
            No -> pure False
            Unknown -> throwError (EnumerationUnknown constraint term)
    allM [] = pure True
    allM (m : ms) = m >>= \ok -> if ok then allM ms else pure False
