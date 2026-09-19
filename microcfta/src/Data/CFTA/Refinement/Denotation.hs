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

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import qualified Data.CFTA as FTA
import Data.IORef (newIORef, readIORef, writeIORef)
import qualified Data.Tree as Tree

import Data.CFTA.Refinement.Automaton (Automaton, Transition, transitionConstraint)
import Data.CFTA.Refinement.Constraint (unconstrainedConstraint)
import Data.CFTA.Refinement.Evaluate (evaluateConstraint)
import Data.CFTA.Refinement.Types (LiquidSymbol, State)
import Data.CFTA.Refinement.Verdict (Entailment, Verdict (..))

-- | Failure while computing the bounded denotation from Figure 6.
newtype EnumerationError
    = -- | The solver could not decide a guard on one candidate transition.
      EnumerationUnknown State
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
cyclic LTAs as well as acyclic ones. Terms are built level by level by the
shared 'FTA.termsUpToM', and the solver decides each transition's constraint
as soon as its children are complete. Results are deduplicated because the
paper defines a set of terms even when several runs accept the same tree.
This is the authoritative, deliberately simple semantics oracle; generator
backends are optimizations and should be checked against it on bounded
inputs.
-}
denotationAtMost ::
    Entailment ->
    Int ->
    Automaton ->
    IO (Either EnumerationError [Tree.Tree LiquidSymbol])
denotationAtMost entailment maximumHeight automaton = runExceptT $ FTA.termsUpToM check maximumHeight automaton
  where
    check :: State -> Transition -> Tree.Tree LiquidSymbol -> ExceptT EnumerationError IO Bool
    check state transition term
        | transitionConstraint transition == unconstrainedConstraint = pure True
        | otherwise = do
            verdict <- liftIO $ evaluateConstraint entailment (transitionConstraint transition) term
            case verdict of
                Yes -> pure True
                No -> pure False
                Unknown -> throwError $ EnumerationUnknown state
