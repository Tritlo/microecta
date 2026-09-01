{-# LANGUAGE PatternSynonyms #-}

{- | Finite, acyclic liquid tree automata.

An LTA transition has a ranked symbol, child states, and a Boolean guard over
paths into the candidate term. 'Same' retains ECTA's syntactic equality, while
'Entails' asks whether the refinement at one path implies the refinement at
another. Refinements are Liquid Fixpoint expressions.

This initial implementation deliberately covers recognition only. It does not
yet implement position substitutions, recursive automata, synthesis, semantic
intersection, or similarity minimisation.

"Data.LTA.Guard" provides higher-level guard syntax in terms of constructor
arguments. This module also exposes the underlying constructors for tools that
need arbitrary paths.
-}
module Data.LTA (
    -- * Terms and refinements
    Symbol (Symbol),
    Path,
    path,
    Refinement,
    LiquidTerm (..),
    eraseRefinements,

    -- * Guards
    Guard (..),
    Verdict (..),
    Entailment (..),
    evaluateGuard,

    -- * Automata
    State (..),
    Transition,
    pattern Transition,
    transitionSymbol,
    transitionChildren,
    transitionGuard,
    Automaton,
    AutomatonError (..),
    automatonInitial,
    automatonTransitions,
    mkAutomaton,
    accepts,
) where

import Data.Bifunctor (first)
import qualified Data.Map.Strict as Map

import Data.ECTA.Paths (Path, path, unPath)
import Data.ECTA.Term (Symbol (Symbol), Term (Term))
import qualified Data.Tree.FTA as FTA
import qualified Language.Fixpoint.Types as Fixpoint

-- | A logical refinement understood by Liquid Fixpoint.
type Refinement = Fixpoint.Expr

-- | A concrete first-order term annotated with one refinement at every node.
data LiquidTerm = LiquidTerm
    { liquidSymbol :: !Symbol
    , liquidRefinement :: !Refinement
    , liquidChildren :: ![LiquidTerm]
    }
    deriving (Eq, Show)

-- | Remove refinements to recover the underlying MicroECTA term.
eraseRefinements :: LiquidTerm -> Term Symbol
eraseRefinements LiquidTerm{liquidSymbol, liquidChildren} =
    Term liquidSymbol (map eraseRefinements liquidChildren)

-- | A transition guard over paths relative to the transition's root term.
data Guard
    = -- | The guard that always succeeds.
      Top
    | -- | The guard that always fails.
      Bottom
    | -- | Require the two paths to contain the same unrefined term.
      Same !Path !Path
    | -- | Require the refinement at the first path to imply the second.
      Entails !Path !Path
    | -- | Logical negation.
      Not !Guard
    | -- | Logical conjunction.
      And ![Guard]
    | -- | Logical disjunction.
      Or ![Guard]
    deriving (Eq, Show)

-- | A three-valued decision. Solver uncertainty is never silently made false.
data Verdict = Yes | No | Unknown
    deriving (Eq, Show)

-- | The imperative entailment boundary used by the pure automaton structure.
newtype Entailment = Entailment
    { entails :: Refinement -> Refinement -> IO Verdict
    }

-- | Evaluate a guard against one candidate term.
evaluateGuard :: Entailment -> Guard -> LiquidTerm -> IO Verdict
evaluateGuard entailment guard term = go guard
  where
    go Top = pure Yes
    go Bottom = pure No
    go (Same left right) =
        pure $ case (termAt left term, termAt right term) of
            (Just leftTerm, Just rightTerm)
                | eraseRefinements leftTerm == eraseRefinements rightTerm -> Yes
            _ -> No
    go (Entails antecedent consequent) =
        case (termAt antecedent term, termAt consequent term) of
            (Just leftTerm, Just rightTerm) ->
                entails entailment (liquidRefinement leftTerm) (liquidRefinement rightTerm)
            _ -> pure No
    go (Not nested) = negateVerdict <$> go nested
    go (And guards) = andM (map go guards)
    go (Or guards) = orM (map go guards)

-- | An integer identity for one LTA state.
newtype State = State {unState :: Int}
    deriving (Eq, Ord, Show)

-- | One guarded outgoing alternative from an LTA state.
type Transition = FTA.Transition State Symbol Guard

-- | Construct or match an LTA transition.
pattern Transition :: Symbol -> [State] -> Guard -> Transition
pattern Transition symbol children guard = FTA.Transition symbol children guard

{-# COMPLETE Transition #-}

-- | Symbol at the root of a transition.
transitionSymbol :: Transition -> Symbol
transitionSymbol = FTA.transitionSymbol

-- | Child states of a transition, from left to right.
transitionChildren :: Transition -> [State]
transitionChildren = FTA.transitionChildren

-- | Liquid guard attached to a transition.
transitionGuard :: Transition -> Guard
transitionGuard = FTA.transitionGuard

-- | A validated finite, acyclic LTA.
type Automaton = FTA.FTA State Symbol Guard

-- | Initial state of an LTA.
automatonInitial :: Automaton -> State
automatonInitial = FTA.initialState

-- | Complete transition table of an LTA.
automatonTransitions :: Automaton -> Map.Map State [Transition]
automatonTransitions = FTA.transitionTable

-- | A structural error found while constructing an automaton.
data AutomatonError
    = MissingInitialState !State
    | DanglingState !State
    | CyclicState !State
    | InconsistentArity !Symbol !Int !Int
    deriving (Eq, Show)

-- | Validate and construct a finite, acyclic LTA.
mkAutomaton :: State -> [(State, [Transition])] -> Either AutomatonError Automaton
mkAutomaton initial rows = do
    automaton <- first fromFTAError $ FTA.mkFTA initial rows
    case FTA.cycleState automaton of
        Just state -> Left (CyclicState state)
        Nothing -> Right automaton
  where
    fromFTAError (FTA.MissingInitialState state) = MissingInitialState state
    fromFTAError (FTA.DanglingState state) = DanglingState state
    fromFTAError (FTA.InconsistentArity symbol expected actual) =
        InconsistentArity symbol expected actual

-- | Decide whether an annotated term is accepted from the initial state.
accepts :: Entailment -> Automaton -> LiquidTerm -> IO Verdict
accepts entailment automaton =
    acceptsFrom (automatonInitial automaton)
  where
    acceptsFrom state term =
        orM $ map (acceptsTransition term) (Map.findWithDefault [] state $ automatonTransitions automaton)

    acceptsTransition term transition
        | transitionSymbol transition /= liquidSymbol term = pure No
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
                    guardVerdict <- evaluateGuard entailment (transitionGuard transition) term
                    pure (andVerdict childrenVerdict guardVerdict)

termAt :: Path -> LiquidTerm -> Maybe LiquidTerm
termAt target = go (unPath target)
  where
    go [] term = Just term
    go (index : rest) LiquidTerm{liquidChildren}
        | index < 0 = Nothing
        | otherwise = case drop index liquidChildren of
            child : _ -> go rest child
            [] -> Nothing

negateVerdict :: Verdict -> Verdict
negateVerdict Yes = No
negateVerdict No = Yes
negateVerdict Unknown = Unknown

andVerdict :: Verdict -> Verdict -> Verdict
andVerdict No _ = No
andVerdict _ No = No
andVerdict Unknown _ = Unknown
andVerdict _ Unknown = Unknown
andVerdict Yes Yes = Yes

orVerdict :: Verdict -> Verdict -> Verdict
orVerdict Yes _ = Yes
orVerdict _ Yes = Yes
orVerdict Unknown _ = Unknown
orVerdict _ Unknown = Unknown
orVerdict No No = No

andM :: [IO Verdict] -> IO Verdict
andM [] = pure Yes
andM (action : rest) = do
    verdict <- action
    case verdict of
        No -> pure No
        _ -> andVerdict verdict <$> andM rest

orM :: [IO Verdict] -> IO Verdict
orM [] = pure No
orM (action : rest) = do
    verdict <- action
    case verdict of
        Yes -> pure Yes
        _ -> orVerdict verdict <$> orM rest
