{-# LANGUAGE OverloadedStrings #-}
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
    PruneError (..),
    automatonInitial,
    automatonTransitions,
    mkAutomaton,
    prune,
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

-- | A semantic obstacle encountered while pruning guarded transitions.
data PruneError
    = {- | A guard reaches a state with no remaining transition, so no term
      can witness that position.
      -}
      EmptyGuardPosition !State !Path
    | {- | The current small implementation cannot choose one refinement for
      a position whose state has several distinct root refinements, or one
      value name for a substitution position with several root symbols. The
      full paper algorithm resolves this case by semantic intersection and
      state splitting.
      -}
      NonHomogeneousGuardPosition !State !Path
    | {- | Syntactic equality needs ECTA-style intersection rather than one
      refinement summary per observed position.
      -}
      StructuralGuardNeedsIntersection !State
    | -- | The solver could not decide a transition guard.
      PruneUnknown !State
    | -- | Pruning exposed an invalid automaton structure.
      InvalidPrunedAutomaton !AutomatonError
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

{- | Remove semantically impossible transitions without enumerating terms.

This is the transition-level boundary used by generated LTAs. A guard is
discharged from the transition's own refinement and homogeneous refinement
summaries at the finite positions it observes. Accepted guards become 'Top';
dead transitions and states are eliminated to a fixed point.

The current implementation deliberately reports non-homogeneous observations
and structural equality. Those are the cases where the paper's general
semantic-intersection construction must split states instead of summarising a
position by one refinement. Ordinary refinement guards, including dependent
actual-for-formal substitution, do not materialize any accepted tree.
-}
prune :: Entailment -> Automaton -> IO (Either PruneError Automaton)
prune entailment automaton = loop $ automatonTransitions automaton
  where
    initial = automatonInitial automaton

    loop table = do
        checked <- traverseRows table $ Map.toList table
        case checked of
            Left err -> pure $ Left err
            Right rows ->
                let next = Map.fromList rows
                 in if fmap length next == fmap length table
                        then
                            pure $
                                first (InvalidPrunedAutomaton) $
                                    mkAutomaton initial rows
                        else loop next

    traverseRows _ [] = pure $ Right []
    traverseRows table ((state, transitions) : rest) = do
        row <- pruneRow table state transitions
        case row of
            Left err -> pure $ Left err
            Right retained ->
                fmap ((state, retained) :) <$> traverseRows table rest

    pruneRow _ _ [] = pure $ Right []
    pruneRow table state (transition : rest)
        | any (null . transitionsAt table) $ transitionChildren transition =
            pruneRow table state rest
        | otherwise = do
            decision <- pruneTransition table state transition
            case decision of
                Left err -> pure $ Left err
                Right Nothing -> pruneRow table state rest
                Right (Just retained) ->
                    fmap (retained :) <$> pruneRow table state rest

    transitionsAt table state = Map.findWithDefault [] state table

    pruneTransition table state transition
        | hasStructuralGuard $ transitionGuard transition =
            pure $ Left $ StructuralGuardNeedsIntersection state
        | otherwise =
            case traverse resolve positions of
                Left (EmptyGuardPosition _ _) -> pure $ Right Nothing
                Left err -> pure $ Left err
                Right resolved -> do
                    verdict <-
                        evaluateGuard
                            entailment
                            (transitionGuard transition)
                            (sparseTerm transition resolved)
                    pure $ case verdict of
                        Yes -> Right $ Just $ setTransitionGuard Top transition
                        No -> Right Nothing
                        Unknown -> Left $ PruneUnknown state
      where
        positions = Set.toList $ Set.fromList $ guardPaths $ transitionGuard transition
        symbolPositions = Set.fromList $ symbolSensitivePaths $ transitionGuard transition
        resolve target =
            resolvePosition
                (Set.member target symbolPositions)
                table
                state
                transition
                target

-- | Replace a transition's guard without changing its ranked symbol or states.
setTransitionGuard :: Guard -> Transition -> Transition
setTransitionGuard guard transition =
    Transition
        (transitionSymbol transition)
        (transitionRefinement transition)
        (transitionChildren transition)
        guard

-- | Whether a guard needs structural ECTA intersection.
hasStructuralGuard :: Guard -> Bool
hasStructuralGuard Top = False
hasStructuralGuard Bottom = False
hasStructuralGuard (Same _ _) = True
hasStructuralGuard (Entails _ _) = False
hasStructuralGuard (Satisfies _ _) = False
hasStructuralGuard (Substitute _ nested) = hasStructuralGuard nested
hasStructuralGuard (Not nested) = hasStructuralGuard nested
hasStructuralGuard (And guards) = any hasStructuralGuard guards
hasStructuralGuard (Or guards) = any hasStructuralGuard guards

-- | Paths whose constructor symbol participates in substitution.
symbolSensitivePaths :: Guard -> [Path]
symbolSensitivePaths Top = []
symbolSensitivePaths Bottom = []
symbolSensitivePaths (Same left right) = [left, right]
symbolSensitivePaths (Entails _ _) = []
symbolSensitivePaths (Satisfies _ _) = []
symbolSensitivePaths (Substitute substitutions nested) =
    concatMap substitutionPaths substitutions <> symbolSensitivePaths nested
  where
    substitutionPaths Substitution{substitutionActual, substitutionFormal} =
        [substitutionActual, substitutionFormal]
symbolSensitivePaths (Not nested) = symbolSensitivePaths nested
symbolSensitivePaths (And guards) = concatMap symbolSensitivePaths guards
symbolSensitivePaths (Or guards) = concatMap symbolSensitivePaths guards

{- | Resolve one observed position to a representative root liquid symbol.

Ordinary semantic guards require one refinement but do not inspect the
constructor symbol. Substitution positions require both to be homogeneous,
because the constructor symbol names the value substituted into the formula.
-}
resolvePosition ::
    Bool ->
    Map.Map State [Transition] ->
    State ->
    Transition ->
    Path ->
    Either PruneError (Path, LiquidSymbol)
resolvePosition needsSymbol table parent transition target =
    case unPath target of
        [] -> Right (target, transitionLiquidSymbol transition)
        index : rest -> do
            child <-
                maybe
                    (Left $ EmptyGuardPosition parent target)
                    Right
                    (atIndex index $ transitionChildren transition)
            symbols <- symbolsAt table child rest
            case Set.toList symbols of
                [] -> Left $ EmptyGuardPosition parent target
                [symbol] -> Right (target, symbol)
                symbol : others
                    | not needsSymbol && all (sameRefinement symbol) others ->
                        Right (target, symbol)
                    | otherwise -> Left $ NonHomogeneousGuardPosition parent target
  where
    sameRefinement (LiquidSymbol _ expected) (LiquidSymbol _ actual) =
        expected == actual

-- | Liquid symbol carried by a transition.
transitionLiquidSymbol :: Transition -> LiquidSymbol
transitionLiquidSymbol (FTA.Transition symbol _ _) = symbol

-- | Possible liquid symbols at a fixed path below one state.
symbolsAt :: Map.Map State [Transition] -> State -> [Int] -> Either PruneError (Set.Set LiquidSymbol)
symbolsAt table state [] =
    Right . Set.fromList $ map transitionLiquidSymbol $ Map.findWithDefault [] state table
symbolsAt table state (index : rest) =
    Set.unions
        <$> traverse
            descend
            (Map.findWithDefault [] state table)
  where
    descend transition =
        case atIndex index $ transitionChildren transition of
            Nothing -> Right Set.empty
            Just child -> symbolsAt table child rest

-- | Build only the finite path trie needed by 'evaluateGuard'.
sparseTerm :: Transition -> [(Path, LiquidSymbol)] -> LiquidTerm
sparseTerm transition resolved = build [] rootSymbol
  where
    rootSymbol = transitionLiquidSymbol transition

    build prefix fallback =
        let LiquidSymbol symbol refinement = maybe fallback id $ lookupAt prefix
            childIndexes = Set.toAscList $ Set.fromList $ nextIndexes prefix
            maximumChild = case childIndexes of
                [] -> -1
                _ -> maximum childIndexes
         in LiquidTerm
                symbol
                refinement
                [ build (prefix <> [index]) dummySymbol
                | index <- [0 .. maximumChild]
                ]

    lookupAt prefix =
        lookup
            prefix
            [ (unPath target, symbol)
            | (target, symbol) <- resolved
            ]

    nextIndexes prefix =
        [ next
        | (target, _) <- resolved
        , let components = unPath target
        , take (length prefix) components == prefix
        , next : _ <- [drop (length prefix) components]
        ]

    dummySymbol = LiquidSymbol (Symbol "__lta_unobserved") Fixpoint.PTrue

-- | Safe zero-based list lookup.
atIndex :: Int -> [a] -> Maybe a
atIndex index values
    | index < 0 = Nothing
    | otherwise = case drop index values of
        value : _ -> Just value
        [] -> Nothing

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
