{-# LANGUAGE PatternSynonyms #-}

{- | Liquid tree automata over Liquid Fixpoint refinements.

An LTA transition has a ranked symbol, child states, and a Boolean guard over
paths into the candidate term. 'Same' retains ECTA's syntactic equality, while
'Entails' asks whether the refinement at one path implies the refinement at
another. 'Satisfies' compares a path with a literal requirement, avoiding
phantom constant children. 'Substitute' applies the paper's actual-for-formal
position substitutions before semantic checks. Refinements are Liquid Fixpoint
expressions.

Recursive automata are accepted. As required by the LTA construction, a guard
may only inspect positions whose states are acyclic; recursive states can still
occur elsewhere in the generated term.

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
    LiquidSymbol,
    eraseRefinements,

    -- * Guards
    Substitution (..),
    Guard (..),
    guardPaths,
    Verdict (..),
    Entailment (..),
    RefinementRelation (..),
    refinementRelation,
    SemanticIntersection (..),
    semanticIntersection,
    evaluateGuard,

    -- * Automata
    State (..),
    Transition,
    pattern Transition,
    transitionSymbol,
    transitionRefinement,
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
import qualified Data.Set as Set

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
    | -- | Require the refinement at a path to imply a literal requirement.
      Satisfies !Path !Refinement
    | -- | Apply actual-for-formal substitutions before checking a guard.
      Substitute ![Substitution] !Guard
    | -- | Logical negation.
      Not !Guard
    | -- | Logical conjunction.
      And ![Guard]
    | -- | Logical disjunction.
      Or ![Guard]
    deriving (Eq, Show)

{- | Replace the variable named at the formal path with the variable named at
the actual path while evaluating a semantic guard. The instantiated refinement
carried by the actual subtree is added to each resulting entailment antecedent.

This is the paper's @[actual/formal]@ position substitution. Both positions are
relative to the root of the guarded transition.
-}
data Substitution = Substitution
    { substitutionActual :: !Path
    , substitutionFormal :: !Path
    }
    deriving (Eq, Show)

-- | Every term position inspected by a guard, including substitutions.
guardPaths :: Guard -> [Path]
guardPaths Top = []
guardPaths Bottom = []
guardPaths (Same left right) = [left, right]
guardPaths (Entails antecedent consequent) = [antecedent, consequent]
guardPaths (Satisfies target _) = [target]
guardPaths (Substitute substitutions nested) =
    concatMap substitutionPaths substitutions <> guardPaths nested
  where
    substitutionPaths Substitution{substitutionActual, substitutionFormal} =
        [substitutionActual, substitutionFormal]
guardPaths (Not nested) = guardPaths nested
guardPaths (And guards) = concatMap guardPaths guards
guardPaths (Or guards) = concatMap guardPaths guards

-- | A three-valued decision. Solver uncertainty is never silently made false.
data Verdict = Yes | No | Unknown
    deriving (Eq, Show)

-- | The imperative entailment boundary used by the pure automaton structure.
newtype Entailment = Entailment
    { entails :: Refinement -> Refinement -> IO Verdict
    }

-- | The semantic subtype relationship between two refinements.
data RefinementRelation
    = -- | Each refinement implies the other.
      Equivalent
    | -- | The left refinement is strictly more specific.
      StrictSubtype
    | -- | The right refinement is strictly more specific.
      StrictSupertype
    | -- | Neither refinement implies the other.
      Incomparable
    | -- | The solver could not decide at least one required implication.
      RelationUnknown
    deriving (Eq, Show)

{- | Compare two refinements by asking for implication in both directions.

This is the semantic comparison used by LTA intersection and similarity
minimisation. Solver uncertainty remains explicit.
-}
refinementRelation :: Entailment -> Refinement -> Refinement -> IO RefinementRelation
refinementRelation entailment left right = do
    leftToRight <- entails entailment left right
    rightToLeft <- entails entailment right left
    pure $ case (leftToRight, rightToLeft) of
        (Yes, Yes) -> Equivalent
        (Yes, No) -> StrictSubtype
        (No, Yes) -> StrictSupertype
        (No, No) -> Incomparable
        _ -> RelationUnknown

-- | Result of the paper's semantic intersection on refinement transitions.
data SemanticIntersection
    = -- | The intersection retains this more-specific refinement.
      MoreSpecific !Refinement
    | -- | The semantic entailment constraint cannot relate the transitions.
      BottomIntersection
    | -- | The solver could not decide the required relation.
      IntersectionUnknown
    deriving (Eq, Show)

{- | Intersect two refinement transitions by keeping their most-specific
representative when one subsumes the other.

This is the semantic-intersection rule used while pruning an LTA, not general
logical conjunction: overlapping but incomparable predicates yield
'BottomIntersection'.
-}
semanticIntersection :: Entailment -> Refinement -> Refinement -> IO SemanticIntersection
semanticIntersection entailment left right = do
    relation <- refinementRelation entailment left right
    pure $ case relation of
        Equivalent -> MoreSpecific left
        StrictSubtype -> MoreSpecific left
        StrictSupertype -> MoreSpecific right
        Incomparable -> BottomIntersection
        RelationUnknown -> IntersectionUnknown

-- | Evaluate a guard against one candidate term.
evaluateGuard :: Entailment -> Guard -> LiquidTerm -> IO Verdict
evaluateGuard entailment guard term = go guard
  where
    go = evaluateWith []

    evaluateWith _ Top = pure Yes
    evaluateWith _ Bottom = pure No
    evaluateWith _ (Same left right) =
        pure $ case (termAt left term, termAt right term) of
            (Just leftTerm, Just rightTerm)
                | eraseRefinements leftTerm == eraseRefinements rightTerm -> Yes
            _ -> No
    evaluateWith substitutions (Entails antecedent consequent) =
        case (termAt antecedent term, termAt consequent term) of
            (Just leftTerm, Just rightTerm) ->
                entails
                    entailment
                    ( withActualAssumptions substitutions $
                        applySubstitutions substitutions $
                            liquidRefinement leftTerm
                    )
                    (applySubstitutions substitutions $ liquidRefinement rightTerm)
            _ -> pure No
    evaluateWith substitutions (Satisfies target requirement) =
        case termAt target term of
            Just targetTerm ->
                entails
                    entailment
                    ( withActualAssumptions substitutions $
                        applySubstitutions substitutions $
                            liquidRefinement targetTerm
                    )
                    (applySubstitutions substitutions requirement)
            Nothing -> pure No
    evaluateWith substitutions (Substitute additions nested) =
        case traverse (resolveSubstitution term) additions of
            Just resolved -> evaluateWith (resolved <> substitutions) nested
            Nothing -> pure No
    evaluateWith substitutions (Not nested) =
        negateVerdict <$> evaluateWith substitutions nested
    evaluateWith substitutions (And guards) =
        andM (map (evaluateWith substitutions) guards)
    evaluateWith substitutions (Or guards) =
        orM (map (evaluateWith substitutions) guards)

-- | An integer identity for one LTA state.
newtype State = State {unState :: Int}
    deriving (Eq, Ord, Show)

-- | The ranked alphabet label carried by one LTA transition.
data LiquidSymbol = LiquidSymbol !Symbol !Refinement
    deriving (Eq, Ord, Show)

-- | One refinement-labelled, guarded alternative from an LTA state.
type Transition = FTA.Transition State LiquidSymbol Guard

-- | Construct or match an LTA transition.
pattern Transition :: Symbol -> Refinement -> [State] -> Guard -> Transition
pattern Transition symbol refinement children guard =
    FTA.Transition (LiquidSymbol symbol refinement) children guard

{-# COMPLETE Transition #-}

-- | Symbol at the root of a transition.
transitionSymbol :: Transition -> Symbol
transitionSymbol (FTA.Transition (LiquidSymbol symbol _) _ _) = symbol

-- | Refinement formula at the root of a transition.
transitionRefinement :: Transition -> Refinement
transitionRefinement (FTA.Transition (LiquidSymbol _ refinement) _ _) = refinement

-- | Child states of a transition, from left to right.
transitionChildren :: Transition -> [State]
transitionChildren = FTA.transitionChildren

-- | Liquid guard attached to a transition.
transitionGuard :: Transition -> Guard
transitionGuard = FTA.transitionGuard

-- | A validated LTA, possibly with recursive states.
type Automaton = FTA.FTA State LiquidSymbol Guard

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
    | {- | A guard position reaches a recursive state, which would produce an
      unbounded logical obligation during semantic operations.
      -}
      CyclicGuardReference !State !Path
    | InconsistentArity !Symbol !Int !Int
    deriving (Eq, Show)

-- | Validate and construct an LTA, including guarded-cycle well-formedness.
mkAutomaton :: State -> [(State, [Transition])] -> Either AutomatonError Automaton
mkAutomaton initial rows = do
    automaton <- first fromFTAError $ FTA.mkFTA initial rows
    ensureConsistentSymbolArity automaton
    ensureGuardedPositionsAcyclic automaton
    pure automaton
  where
    fromFTAError (FTA.MissingInitialState state) = MissingInitialState state
    fromFTAError (FTA.DanglingState state) = DanglingState state
    fromFTAError (FTA.InconsistentArity (LiquidSymbol symbol _) expected actual) =
        InconsistentArity symbol expected actual

ensureConsistentSymbolArity :: Automaton -> Either AutomatonError ()
ensureConsistentSymbolArity automaton = go Map.empty allTransitions
  where
    allTransitions = concat $ Map.elems $ automatonTransitions automaton

    go _ [] = Right ()
    go arities (transition : rest) =
        let symbol = transitionSymbol transition
            arity = length $ transitionChildren transition
         in case Map.lookup symbol arities of
                Nothing -> go (Map.insert symbol arity arities) rest
                Just expected
                    | expected == arity -> go arities rest
                    | otherwise -> Left (InconsistentArity symbol expected arity)

ensureGuardedPositionsAcyclic :: Automaton -> Either AutomatonError ()
ensureGuardedPositionsAcyclic automaton =
    case referencesIntoCycles of
        (state, target) : _ -> Left (CyclicGuardReference state target)
        [] -> Right ()
  where
    cyclic = FTA.cyclicStates automaton
    referencesIntoCycles =
        [ (referenced, target)
        | (state, transitions) <- Map.toList $ automatonTransitions automaton
        , transition <- transitions
        , target <- guardPaths $ transitionGuard transition
        , referenced <- Set.toList $ statesAtPath automaton state transition target
        , Set.member referenced cyclic
        ]

statesAtPath :: Automaton -> State -> Transition -> Path -> Set.Set State
statesAtPath automaton parent transition target =
    case unPath target of
        [] -> Set.singleton parent
        index : rest ->
            descend rest $ maybe Set.empty Set.singleton $ atIndex index (transitionChildren transition)
  where
    descend [] current = current
    descend (index : rest) current =
        descend rest . Set.fromList $
            [ child
            | state <- Set.toList current
            , outgoing <- FTA.transitionsFrom automaton state
            , Just child <- [atIndex index $ FTA.transitionChildren outgoing]
            ]

    atIndex index values
        | index < 0 = Nothing
        | otherwise = case drop index values of
            value : _ -> Just value
            [] -> Nothing

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

data ResolvedSubstitution = ResolvedSubstitution
    { resolvedReplacement :: !(Fixpoint.Symbol, Fixpoint.Expr)
    , resolvedActualAssumption :: !Refinement
    }

resolveSubstitution :: LiquidTerm -> Substitution -> Maybe ResolvedSubstitution
resolveSubstitution term Substitution{substitutionActual, substitutionFormal} = do
    LiquidTerm{liquidSymbol = Symbol actualName, liquidRefinement = actualRefinement} <-
        termAt substitutionActual term
    LiquidTerm{liquidSymbol = Symbol formalName} <- termAt substitutionFormal term
    let actualSymbol = Fixpoint.symbol actualName
        actualVariable = Fixpoint.EVar actualSymbol
    pure
        ResolvedSubstitution
            { resolvedReplacement = (Fixpoint.symbol formalName, actualVariable)
            , resolvedActualAssumption =
                Fixpoint.subst1 actualRefinement (refinementValueSymbol, actualVariable)
            }

-- | Conventional value variable used by public microlta refinements.
refinementValueSymbol :: Fixpoint.Symbol
refinementValueSymbol = Fixpoint.symbol ("v" :: String)

applySubstitutions :: [ResolvedSubstitution] -> Refinement -> Refinement
applySubstitutions substitutions refinement =
    foldl apply refinement substitutions
  where
    apply predicate ResolvedSubstitution{resolvedReplacement} =
        Fixpoint.subst1 predicate resolvedReplacement

{- | Add the instantiated refinement of every actual argument to an entailment
antecedent.

Substitution changes a formal name to the actual term's symbol. This assumption
connects that symbol back to the refinement carried by the actual subtree, so
dependent results compose through non-leaf nodes as well as named pool entries.
-}
withActualAssumptions :: [ResolvedSubstitution] -> Refinement -> Refinement
withActualAssumptions substitutions predicate =
    Fixpoint.pAnd $
        map (applySubstitutions substitutions . resolvedActualAssumption) substitutions
            <> [predicate]

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
