{- | The reference semantics of an LTA.

'accepts' decides one annotated term. 'denotationAtMost' materializes the
Figure 6 denotation up to a height bound. Both are deliberately simple, so they
serve as the oracle that generator backends are checked against.
-}
module Data.LTA.Denotation (
    EnumerationError (..),
    accepts,
    denotationAtMost,
) where

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import qualified Data.Map.Strict as Map
import qualified Data.Tree as Tree
import qualified Data.Tree.FTA as FTA

import Data.LTA.Automaton (
    Automaton,
    Transition,
    automatonInitial,
    automatonTransitions,
    transitionChildren,
    transitionConstraint,
    transitionRefinement,
    transitionSymbol,
 )
import Data.LTA.Evaluate (evaluateConstraint)
import Data.LTA.Types (LiquidSymbol (LiquidSymbol), State)
import Data.LTA.Verdict (Entailment, Verdict (..), andM, andVerdict, orM)

-- | Failure while computing the bounded denotation from Figure 6.
newtype EnumerationError
    = -- | The solver could not decide a guard on one candidate transition.
      EnumerationUnknown State
    deriving (Eq, Show)

-- | Decide whether an annotated term is accepted from the initial state.
accepts :: Entailment -> Automaton -> Tree.Tree LiquidSymbol -> IO Verdict
accepts entailment automaton =
    acceptsFrom (automatonInitial automaton)
  where
    acceptsFrom state term =
        orM $ map (acceptsTransition term) (Map.findWithDefault [] state $ automatonTransitions automaton)

    acceptsTransition term@(Tree.Node (LiquidSymbol symbol refinement) children) transition
        | transitionSymbol transition /= symbol = pure No
        | transitionRefinement transition /= refinement = pure No
        | length (transitionChildren transition) /= length children = pure No
        | otherwise = do
            childrenVerdict <-
                andM $
                    zipWith
                        acceptsFrom
                        (transitionChildren transition)
                        children
            case childrenVerdict of
                No -> pure No
                _ -> do
                    constraintVerdict <- evaluateConstraint entailment (transitionConstraint transition) term
                    pure (andVerdict childrenVerdict constraintVerdict)

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
    check state transition term = do
        verdict <- liftIO $ evaluateConstraint entailment (transitionConstraint transition) term
        case verdict of
            Yes -> pure True
            No -> pure False
            Unknown -> throwError $ EnumerationUnknown state
