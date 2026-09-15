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

import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Strict (StateT, get, modify', runStateT)
import Data.List (nub)
import qualified Data.Map.Strict as Map

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
import Data.LTA.Types (LiquidTerm (..), State)
import Data.LTA.Verdict (Entailment, Verdict (..), andM, andVerdict, orM)

-- | Failure while computing the bounded denotation from Figure 6.
data EnumerationError
    = -- | The solver could not decide a guard on one candidate transition.
      EnumerationUnknown !State
    deriving (Eq, Show)

-- | Decide whether an annotated term is accepted from the initial state.
accepts :: Entailment -> Automaton -> LiquidTerm -> IO Verdict
accepts entailment automaton =
    acceptsFrom (automatonInitial automaton)
  where
    acceptsFrom state term =
        orM $ map (acceptsTransition term) (Map.findWithDefault [] state $ automatonTransitions automaton)

    acceptsTransition term transition
        | transitionSymbol transition /= liquidSymbol term = pure No
        | transitionRefinement transition /= liquidRefinement term = pure No
        | length (transitionChildren transition) /= length (liquidChildren term) = pure No
        | otherwise = do
            childrenVerdict <-
                andM $
                    zipWith
                        acceptsFrom
                        (transitionChildren transition)
                        (liquidChildren term)
            case childrenVerdict of
                No -> pure No
                _ -> do
                    constraintVerdict <- evaluateConstraint entailment (transitionConstraint transition) term
                    pure (andVerdict childrenVerdict constraintVerdict)

{- | Materialize the Figure 6 denotation up to a tree-height bound.

A leaf has height zero. The bound makes this reference interpreter total for
cyclic LTAs as well as acyclic ones. Results are deduplicated because the paper
defines a set of terms even when several runs accept the same tree. This is the
authoritative, deliberately simple semantics oracle; generator backends are
optimizations and should be checked against it on bounded inputs.
-}
denotationAtMost ::
    Entailment ->
    Int ->
    Automaton ->
    IO (Either EnumerationError [LiquidTerm])
denotationAtMost entailment maximumHeight automaton
    | maximumHeight < 0 = pure $ Right []
    | otherwise = fmap fst $ runStateT (enumerateFrom maximumHeight $ automatonInitial automaton) Map.empty
  where
    table = automatonTransitions automaton

    enumerateFrom ::
        Int ->
        State ->
        StateT (Map.Map (State, Int) [LiquidTerm]) IO (Either EnumerationError [LiquidTerm])
    enumerateFrom remaining state = do
        cache <- get
        case Map.lookup (state, remaining) cache of
            Just terms -> pure $ Right terms
            Nothing -> do
                result <- enumerateTransitions remaining state $ Map.findWithDefault [] state table
                case result of
                    Left err -> pure $ Left err
                    Right terms -> do
                        let unique = nub terms
                        modify' $ Map.insert (state, remaining) unique
                        pure $ Right unique

    enumerateTransitions ::
        Int ->
        State ->
        [Transition] ->
        StateT (Map.Map (State, Int) [LiquidTerm]) IO (Either EnumerationError [LiquidTerm])
    enumerateTransitions _ _ [] = pure $ Right []
    enumerateTransitions remaining state (transition : rest) = do
        current <- enumerateTransition remaining state transition
        case current of
            Left err -> pure $ Left err
            Right terms -> fmap (fmap (terms <>)) $ enumerateTransitions remaining state rest

    enumerateTransition ::
        Int ->
        State ->
        Transition ->
        StateT (Map.Map (State, Int) [LiquidTerm]) IO (Either EnumerationError [LiquidTerm])
    enumerateTransition remaining state transition
        | null children = checkCandidates state transition [[]]
        | remaining == 0 = pure $ Right []
        | otherwise = do
            choices <- traverse (enumerateFrom $ remaining - 1) children
            case sequence choices of
                Left err -> pure $ Left err
                Right childTerms -> checkCandidates state transition $ cartesian childTerms
      where
        children = transitionChildren transition

    checkCandidates ::
        State ->
        Transition ->
        [[LiquidTerm]] ->
        StateT (Map.Map (State, Int) [LiquidTerm]) IO (Either EnumerationError [LiquidTerm])
    checkCandidates _ _ [] = pure $ Right []
    checkCandidates state transition (children : rest) = do
        let term =
                LiquidTerm
                    (transitionSymbol transition)
                    (transitionRefinement transition)
                    children
        verdict <- liftIO $ evaluateConstraint entailment (transitionConstraint transition) term
        case verdict of
            Yes -> fmap (fmap (term :)) $ checkCandidates state transition rest
            No -> checkCandidates state transition rest
            Unknown -> pure $ Left $ EnumerationUnknown state

    cartesian :: [[value]] -> [[value]]
    cartesian [] = [[]]
    cartesian (choices : rest) =
        [ choice : suffix
        | choice <- choices
        , suffix <- cartesian rest
        ]
