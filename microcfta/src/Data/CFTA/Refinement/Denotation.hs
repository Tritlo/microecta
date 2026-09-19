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

import Data.CFTA.Enumeration (plainTermsAtMost, runs, unconstrained)
import Data.CFTA.Interned (boundDepth, edgeChildren, edgeConstraint, edgeSymbol, nodeEdges)
import Data.CFTA.Refinement.Automaton (Automaton)
import Data.CFTA.Refinement.Constraint (LiquidConstraint)
import Data.CFTA.Refinement.Evaluate (evaluateConstraint)
import Data.CFTA.Refinement.Types (LiquidSymbol (LiquidSymbol))
import Data.CFTA.Refinement.Verdict (Entailment, Verdict (..))

-- | Failure while computing the bounded denotation from Figure 6.
data EnumerationError
    = -- | The solver could not decide a transition's guard on the subterm the transition built.
      EnumerationUnknown LiquidConstraint (Tree.Tree LiquidSymbol)
    deriving (Eq, Show)

{- | Decide whether an annotated term is accepted at the root.

The result is 'Yes' when some run accepts the term with every guard decided
'Yes'. It is 'No' when no run accepts the term and the solver decided every
guard the search evaluated. It is 'Unknown' otherwise. A guard is decided
only after the children of its transition have accepted their subterms.
-}
accepts :: Entailment -> Automaton -> Tree.Tree LiquidSymbol -> IO Verdict
accepts entailment automaton term = do
    undecided <- newIORef False
    accepted <- acceptsAt undecided automaton term
    unknown <- readIORef undecided
    pure $ if accepted then Yes else if unknown then Unknown else No
  where
    acceptsAt undecided node candidate@(Tree.Node symbol children) =
        anyM
            [ allM (zipWith (acceptsAt undecided) (edgeChildren edge) children) >>= \ok ->
                if ok then check undecided edge candidate else pure False
            | edge <- nodeEdges node
            , edgeSymbol edge == symbol
            , length (edgeChildren edge) == length children
            ]

    check undecided edge candidate = do
        verdict <- evaluateConstraint entailment (edgeConstraint edge) candidate
        case verdict of
            Yes -> pure True
            No -> pure False
            Unknown -> writeIORef undecided True >> pure False

    anyM [] = pure False
    anyM (action : actions) = action >>= \ok -> if ok then pure True else anyM actions

{- | Materialize the Figure 6 denotation up to a tree-height bound.

A leaf has height zero. The bound makes this reference interpreter total for
cyclic LTAs as well as acyclic ones. A graph without constraints is listed
level by level up to the bound. Otherwise the bounded graph is listed by the
shared enumerator: path equalities are solved by unification, and the solver
decides each remaining guard on the complete subterm its transition built. A
term is accepted when the guards of some run all hold. The result has each
term once, in enumeration order, because
the paper defines a set of terms even when several runs accept the same tree.
This is the authoritative, deliberately simple semantics oracle; generator
backends are optimizations and should be checked against it on bounded inputs.
-}
denotationAtMost :: Entailment -> Int -> Automaton -> IO (Either EnumerationError [Tree.Tree LiquidSymbol])
denotationAtMost entailment bound automaton
    | bound < 0 = pure (Right [])
    | unconstrained automaton = pure (Right (plainTermsAtMost bound automaton))
    | otherwise = runExceptT $ do
        accepted <- filterM (allM . map decide . snd) (runs recursion bounded)
        pure $ nubOrd $ map fst accepted
  where
    bounded = boundDepth bound automaton
    recursion = LiquidSymbol "Mu" Fixpoint.PTrue
    decide (constraint, term) = do
        verdict <- liftIO $ evaluateConstraint entailment constraint term
        case verdict of
            Yes -> pure True
            No -> pure False
            Unknown -> throwError (EnumerationUnknown constraint term)

allM :: (Monad m) => [m Bool] -> m Bool
allM [] = pure True
allM (action : actions) = action >>= \ok -> if ok then allM actions else pure False
