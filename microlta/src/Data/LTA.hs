{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

{- | Liquid tree automata over Liquid Fixpoint refinements.

An LTA transition has a ranked symbol, child states, and the paper's Boolean
constraint language over paths into the candidate term. 'Same' is syntactic
equality and 'Entails' is semantic refinement implication. 'Satisfies' compares
a path with a literal requirement, avoiding phantom constant children.
'Substitute' applies the paper's actual-for-formal position substitutions before
semantic checks. Refinements are Liquid Fixpoint expressions.

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
    unPath,
    Refinement,
    LiquidTerm (..),
    LiquidSymbol (..),
    eraseRefinements,

    -- * Guards
    Substitution (..),
    Guard (..),
    LiquidConstraint (..),
    unconstrainedConstraint,
    semanticConstraint,
    equalityConstraint,
    combineConstraints,
    constraintAsGuard,
    guardPaths,
    constraintPaths,
    Verdict (..),
    Entailment (..),
    RefinementRelation (..),
    refinementRelation,
    SemanticIntersection (..),
    semanticIntersection,
    evaluateGuard,
    evaluateGuardWith,
    evaluateConstraint,

    -- * Automata
    State (..),
    Transition,
    pattern Transition,
    transitionSymbol,
    transitionRefinement,
    transitionChildren,
    transitionConstraint,
    transitionEqualities,
    transitionGuard,
    Automaton,
    EqualityAutomaton,
    AutomatonError (..),
    PruneError (..),
    EnumerationError (..),
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
    automatonStates,
    automatonAlphabet,
    automatonFinalStates,
    automatonInitial,
    automatonTransitions,
    transitionsAt,
    mkAutomaton,
    mkAutomatonWithFinals,
    lowerToEqualityAutomaton,
    pruneToECTA,
    pruneSemantics,
    prune,
    accepts,
    denotationAtMost,
) where

import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Strict (StateT, get, modify', runStateT)
import Data.Bifunctor (first)
import Data.List (nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.ECTA.Paths (
    EqConstraints (EmptyConstraints),
    Path,
    combineEqConstraints,
    constraintsAreContradictory,
    mkEqConstraints,
    path,
    subsumptionOrderedEclasses,
    unPath,
    unPathEClass,
 )
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
    | -- | Require the two paths to contain the same annotated LTA term.
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

{- | A complete LTA constraint with an optional normalized equality cache.

The authoritative semantics is the full Boolean 'Guard', including 'Same'. The
equality field is a compiled positive-conjunction form used by the MicroECTA
optimization. 'constraintAsGuard' always recovers the complete paper-level
constraint, so the split representation cannot erase Boolean equality.
-}
data LiquidConstraint = LiquidConstraint
    { constraintEqualities :: !EqConstraints
    , constraintGuard :: !Guard
    }
    deriving (Eq, Show)

-- | A transition with neither equality nor liquid obligations.
unconstrainedConstraint :: LiquidConstraint
unconstrainedConstraint = LiquidConstraint EmptyConstraints Top

-- | Lift one semantic guard into an LTA transition constraint.
semanticConstraint :: Guard -> LiquidConstraint
semanticConstraint = LiquidConstraint EmptyConstraints

-- | Lift normalized positive equalities into an LTA transition constraint.
equalityConstraint :: EqConstraints -> LiquidConstraint
equalityConstraint equalities = LiquidConstraint equalities Top

-- | Conjoin equality classes and semantic obligations.
combineConstraints :: LiquidConstraint -> LiquidConstraint -> LiquidConstraint
combineConstraints
    (LiquidConstraint leftEqualities leftGuard)
    (LiquidConstraint rightEqualities rightGuard) =
        LiquidConstraint
            (combineEqConstraints leftEqualities rightEqualities)
            (combineGuards leftGuard rightGuard)

-- | Recover the complete paper-level Boolean constraint.
constraintAsGuard :: LiquidConstraint -> Guard
constraintAsGuard LiquidConstraint{constraintEqualities, constraintGuard} =
    combineGuards (equalitiesAsGuard constraintEqualities) constraintGuard

-- | Reify normalized positive ECTA equalities as ordinary LTA atoms.
equalitiesAsGuard :: EqConstraints -> Guard
equalitiesAsGuard equalities =
    case subsumptionOrderedEclasses equalities of
        Nothing -> Bottom
        Just classes -> conjoin $ concatMap classEqualities classes
  where
    classEqualities eclass = case unPathEClass eclass of
        anchor : rest -> map (Same anchor) rest
        [] -> []

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

-- | Every term position inspected by either transition constraint theory.
constraintPaths :: LiquidConstraint -> [Path]
constraintPaths LiquidConstraint{constraintEqualities, constraintGuard} =
    equalityPaths constraintEqualities <> guardPaths constraintGuard
  where
    equalityPaths equalities =
        case subsumptionOrderedEclasses equalities of
            Nothing -> []
            Just classes -> concatMap unPathEClass classes

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

This four-way view is useful to clients that need to inspect an ordering.
Pruning and similarity themselves use directional entailment, matching the
paper's judgments. Solver uncertainty remains explicit.
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
    = -- | Entailment holds, so the antecedent transition is retained.
      RetainedAntecedent !Refinement
    | -- | The semantic entailment constraint cannot relate the transitions.
      BottomIntersection
    | -- | The solver could not decide the required relation.
      IntersectionUnknown
    deriving (Eq, Show)

{- | Apply the paper's directional semantic intersection to two refinements.

The first refinement is the antecedent transition at @p1@ and the second is the
consequent at @p2@. If @p1@ entails @p2@, the operation retains @p1@; it never
reverses the query to retain @p2@. This is Equation 4, not logical conjunction
or a symmetric meet.
-}
semanticIntersection :: Entailment -> Refinement -> Refinement -> IO SemanticIntersection
semanticIntersection entailment antecedent consequent = do
    verdict <- entails entailment antecedent consequent
    pure $ case verdict of
        Yes -> RetainedAntecedent antecedent
        No -> BottomIntersection
        Unknown -> IntersectionUnknown

-- | Evaluate a guard against one candidate term.
evaluateGuard :: Entailment -> Guard -> LiquidTerm -> IO Verdict
evaluateGuard entailment guard term =
    evaluateGuardWithSame entailment lookupObservation sameAt guard
  where
    lookupObservation target = do
        observed <- termAt target term
        pure (liquidSymbol observed, liquidRefinement observed)

    sameAt left right = do
        leftTerm <- termAt left term
        rightTerm <- termAt right term
        pure $ leftTerm == rightTerm

{- | Evaluate a semantic guard from sparse observations of its referenced paths.

The callback returns the unrefined constructor symbol and refinement at one
path. Sparse observations cannot decide equality of complete subtrees, so a
'Same' atom yields 'Unknown'. An optimizer must either reject that fast path or
supply a complete-term equality oracle; it must never approximate equality from
root observations.
-}
evaluateGuardWith ::
    Entailment ->
    (Path -> Maybe (Symbol, Refinement)) ->
    Guard ->
    IO Verdict
evaluateGuardWith entailment lookupObservation =
    evaluateGuardWithSame entailment lookupObservation (\_ _ -> Nothing)

-- | Shared evaluator with an optional complete-subtree equality oracle.
evaluateGuardWithSame ::
    Entailment ->
    (Path -> Maybe (Symbol, Refinement)) ->
    (Path -> Path -> Maybe Bool) ->
    Guard ->
    IO Verdict
evaluateGuardWithSame entailment lookupObservation sameAt guard = go guard
  where
    go = evaluateWith []

    evaluateWith _ Top = pure Yes
    evaluateWith _ Bottom = pure No
    evaluateWith _ (Same left right) =
        pure $ case sameAt left right of
            Just True -> Yes
            Just False -> No
            Nothing -> Unknown
    evaluateWith substitutions (Entails antecedent consequent) =
        case (lookupObservation antecedent, lookupObservation consequent) of
            (Just (_, leftRefinement), Just (_, rightRefinement)) ->
                entails
                    entailment
                    ( withActualAssumptions substitutions $
                        applySubstitutions substitutions $
                            leftRefinement
                    )
                    (applySubstitutions substitutions rightRefinement)
            _ -> pure No
    evaluateWith substitutions (Satisfies target requirement) =
        case lookupObservation target of
            Just (_, targetRefinement) ->
                entails
                    entailment
                    ( withActualAssumptions substitutions $
                        applySubstitutions substitutions $
                            targetRefinement
                    )
                    (applySubstitutions substitutions requirement)
            Nothing -> pure No
    evaluateWith substitutions (Substitute additions nested) =
        case traverse (resolveSubstitutionWith lookupObservation) additions of
            Just resolved -> evaluateWith (resolved <> substitutions) nested
            Nothing -> pure No
    evaluateWith substitutions (Not nested) =
        negateVerdict <$> evaluateWith substitutions nested
    evaluateWith substitutions (And guards) =
        andM (map (evaluateWith substitutions) guards)
    evaluateWith substitutions (Or guards) =
        orM (map (evaluateWith substitutions) guards)

-- | Evaluate both the ECTA equality classes and liquid guard of a transition.
evaluateConstraint :: Entailment -> LiquidConstraint -> LiquidTerm -> IO Verdict
evaluateConstraint entailment constraint term
    | satisfiesEqualities (constraintEqualities constraint) term =
        evaluateGuard entailment (constraintGuard constraint) term
    | otherwise = pure No

-- | An integer identity for one LTA state.
newtype State = State {unState :: Int}
    deriving (Eq, Ord, Show)

-- | The ranked alphabet label carried by one LTA transition.
data LiquidSymbol = LiquidSymbol !Symbol !Refinement
    deriving (Eq, Ord, Show)

-- | One refinement-labelled, constrained alternative from an LTA state.
type Transition = FTA.Transition State LiquidSymbol LiquidConstraint

-- | Construct or match an LTA transition.
pattern Transition :: Symbol -> Refinement -> [State] -> LiquidConstraint -> Transition
pattern Transition symbol refinement children constraint =
    FTA.Transition (LiquidSymbol symbol refinement) children constraint

{-# COMPLETE Transition #-}

-- | Symbol at the root of a transition.
transitionSymbol :: FTA.Transition State LiquidSymbol constraint -> Symbol
transitionSymbol (FTA.Transition (LiquidSymbol symbol _) _ _) = symbol

-- | Refinement formula at the root of a transition.
transitionRefinement :: FTA.Transition State LiquidSymbol constraint -> Refinement
transitionRefinement (FTA.Transition (LiquidSymbol _ refinement) _ _) = refinement

-- | Child states of a transition, from left to right.
transitionChildren :: FTA.Transition State LiquidSymbol constraint -> [State]
transitionChildren = FTA.transitionChildren

-- | Complete equality and semantic constraint attached to a transition.
transitionConstraint :: Transition -> LiquidConstraint
transitionConstraint = FTA.transitionGuard

-- | ECTA equality classes attached to a transition.
transitionEqualities :: Transition -> EqConstraints
transitionEqualities = constraintEqualities . transitionConstraint

-- | Liquid semantic guard attached to a transition.
transitionGuard :: Transition -> Guard
transitionGuard = constraintGuard . transitionConstraint

-- | A validated LTA, possibly with recursive states.
type Automaton = FTA.FTA State LiquidSymbol LiquidConstraint

-- | The ECTA-shaped result of discharging every semantic guard in an LTA.
type EqualityAutomaton = FTA.FTA State LiquidSymbol EqConstraints

-- | Initial state of an LTA.
automatonInitial :: FTA.FTA State LiquidSymbol constraint -> State
automatonInitial = FTA.initialState

{- | States of the normalized LTA.

The implementation uses the standard top-down presentation of the paper's
bottom-up transition relation. Its initial state is the single normalized
accepting state.
-}
automatonStates :: FTA.FTA State LiquidSymbol constraint -> Set.Set State
automatonStates = Set.fromList . FTA.states

-- | Finite ranked alphabet actually used by an automaton.
automatonAlphabet :: FTA.FTA State LiquidSymbol constraint -> Set.Set LiquidSymbol
automatonAlphabet automaton =
    Set.fromList
        [ FTA.transitionSymbol transition
        | transitions <- Map.elems $ automatonTransitions automaton
        , transition <- transitions
        ]

{- | Accepting states after explicit many-final-state normalization.

Use 'mkAutomatonWithFinals' to construct the paper's arbitrary @Qf@. It copies
the outgoing alternatives of those states into one fresh accepting state, so
this accessor returns that language-equivalent singleton.
-}
automatonFinalStates :: FTA.FTA State LiquidSymbol constraint -> Set.Set State
automatonFinalStates = Set.singleton . automatonInitial

-- | Complete transition table of an LTA.
automatonTransitions :: FTA.FTA State LiquidSymbol constraint -> Map.Map State [FTA.Transition State LiquidSymbol constraint]
automatonTransitions = FTA.transitionTable

{- | Transitions reachable at a position below one transition (Definition 5).

The empty position denotes the supplied transition. A non-empty position first
selects one child state and then unions the alternatives encountered at each
subsequent component. An invalid component denotes the empty set.
-}
transitionsAt :: Automaton -> Transition -> Path -> [Transition]
transitionsAt automaton transition target =
    case unPath target of
        [] -> [transition]
        index : rest ->
            maybe [] (descend rest) $ atIndex index $ transitionChildren transition
  where
    descend [] state = FTA.transitionsFrom automaton state
    descend (index : rest) state =
        concat
            [ maybe [] (descend rest) $ atIndex index $ transitionChildren outgoing
            | outgoing <- FTA.transitionsFrom automaton state
            ]

-- | A structural error found while constructing an automaton.
data AutomatonError
    = MissingInitialState !State
    | -- | The paper requires at least one accepting state.
      NoFinalStates
    | -- | A declared accepting state has no transition row.
      MissingFinalState !State
    | DanglingState !State
    | {- | A guard position reaches a recursive state, which would produce an
      unbounded logical obligation during semantic operations.
      -}
      CyclicGuardReference !State !Path
    | InconsistentArity !Symbol !Int !Int
    deriving (Eq, Show)

-- | A semantic obstacle encountered while pruning guarded transitions.
data PruneError
    = -- | The solver could not decide a transition guard.
      PruneUnknown !State
    | -- | Product construction violated an FTA invariant.
      InvalidSyntacticIntersection
    | -- | ECTA lowering was requested while a non-equality LTA guard remained.
      ResidualLTAConstraint !State !Guard
    | -- | Pruning exposed an invalid automaton structure.
      InvalidPrunedAutomaton !AutomatonError
    deriving (Eq, Show)

-- | Failure while computing the bounded denotation from Figure 6.
data EnumerationError
    = -- | The solver could not decide a guard on one candidate transition.
      EnumerationUnknown !State
    deriving (Eq, Show)

{- | Stable address of a transition in one automaton snapshot.

The state is the transition's target state; the ordinal is its zero-based
position in that state's transition row. The paper writes the same target on
the right of a bottom-up transition arrow.
-}
data TransitionId = TransitionId
    { transitionTargetState :: !State
    , transitionOrdinal :: !Int
    }
    deriving (Eq, Ord, Show)

{- | Source-language subtyping used by the paper's @Similarity@ procedure.

The callback receives the current automaton and compares the type sub-automata
associated with two program transitions. 'refinementSubtypingBy' is a compact
adapter for encodings that store the complete type refinement on the program
transition itself.
-}
newtype Subtyping = Subtyping
    { isTransitionSubtypeOf :: Automaton -> Transition -> Transition -> IO Verdict
    }

{- | Compare transition refinements after a structural type classification.

The projection supplies the non-liquid part of the type shape. Two transitions
are comparable only when both project to the same class; 'Nothing' excludes a
transition from similarity inference. This corresponds to the syntactic part
of the paper's @SubType@ relation, while implication checks its refinement.
-}
refinementSubtypingBy ::
    (Eq key) =>
    Entailment ->
    (Transition -> Maybe key) ->
    Subtyping
refinementSubtypingBy entailment classify =
    Subtyping $ \_ subtype supertype ->
        case (classify subtype, classify supertype) of
            (Just subtypeClass, Just supertypeClass)
                | subtypeClass == supertypeClass ->
                    entails
                        entailment
                        (transitionRefinement subtype)
                        (transitionRefinement supertype)
            _ -> pure No

-- | Directed transition pairs inferred by the paper's @Similarity@ procedure.
newtype Similarity = Similarity
    { unSimilarity :: [(TransitionId, TransitionId)]
    }
    deriving (Eq, Show)

-- | A source-language subtyping query that could not be decided.
data SimilarityError
    = SimilarityUnknown !TransitionId !TransitionId
    deriving (Eq, Show)

{- | Infer directed @(subtype, supertype)@ transition pairs.

Every unordered transition pair is considered once. If both directions hold,
the earlier transition is the representative, making equivalence deterministic
without introducing a cycle into the similarity set. A known direction is
usable even if its converse is unknown; an unresolved possible direction is
reported rather than treated as false.
-}
similarity :: Subtyping -> Automaton -> IO (Either SimilarityError Similarity)
similarity subtyping automaton = go [] $ unorderedPairs $ locatedTransitions automaton
  where
    go related [] = pure $ Right $ Similarity $ reverse related
    go related (((leftId, left) :&: (rightId, right)) : rest) = do
        leftToRight <- isTransitionSubtypeOf subtyping automaton left right
        case leftToRight of
            Yes -> go ((leftId, rightId) : related) rest
            No -> do
                rightToLeft <- isTransitionSubtypeOf subtyping automaton right left
                case rightToLeft of
                    Yes -> go ((rightId, leftId) : related) rest
                    No -> go related rest
                    Unknown -> pure $ Left $ SimilarityUnknown rightId leftId
            Unknown -> do
                rightToLeft <- isTransitionSubtypeOf subtyping automaton right left
                case rightToLeft of
                    Yes -> go ((rightId, leftId) : related) rest
                    No -> pure $ Left $ SimilarityUnknown leftId rightId
                    Unknown -> pure $ Left $ SimilarityUnknown leftId rightId

-- | Inspect the inferred @(subtype, supertype)@ transition pairs.
similarityPairs :: Similarity -> [(TransitionId, TransitionId)]
similarityPairs = unSimilarity

-- | Structural failure while applying the paper's @Minimize@ procedure.
data MinimizeError
    = -- | The similarity set was inferred for a different transition table.
      StaleSimilarity !TransitionId
    | -- | A caller-provided relation contains a directed cycle.
      CyclicSimilarity ![TransitionId]
    | {- | A redirected target contains another surviving transition. The
      paper's construction gives a representative transition its own target
      state; without that invariant, redirecting the state would also discard
      unrelated alternatives.
      -}
      SharedSimilarityTarget !State
    | -- | One removed target state was assigned two different representatives.
      ConflictingSimilarityTargets !State ![State]
    | {- | A cross-state merge would strand the normalized final state.
      The paper's construction only minimizes program transitions below its
      distinguished goal transition.
      -}
      FinalSimilarityTarget !State
    | -- | Minimization exposed an invalid automaton structure.
      InvalidMinimizedAutomaton !AutomatonError
    deriving (Eq, Show)

{- | Remove supertype transitions and redirect incoming state edges.

This is the paper's M-Trans rule over the complete similarity set. When several
incomparable subtypes dominate the same transition, the first inferred pair is
the deterministic representative. Transitive dominators are resolved before
rewriting, all removals happen together, and the automaton's initial state is
left unchanged just as the paper leaves its final-state set unchanged.
-}
minimize :: Automaton -> Similarity -> Either MinimizeError Automaton
minimize automaton (Similarity related) = do
    mapM_ ensureCurrent $ concatMap pairMembers related
    resolved <- traverse resolveSupertype $ Map.keys dominators
    redirects <- buildRedirects resolved
    first InvalidMinimizedAutomaton $
        mkAutomaton
            (automatonInitial automaton)
            (Map.toList $ fmap (map $ redirectTransition redirects) retained)
  where
    table = automatonTransitions automaton
    current = Map.fromList $ locatedTransitions automaton
    dominators = foldl' rememberDominator Map.empty related
    removed = Map.keysSet dominators

    pairMembers (subtype, supertype) = [subtype, supertype]

    ensureCurrent identifier
        | Map.member identifier current = Right ()
        | otherwise = Left $ StaleSimilarity identifier

    rememberDominator known (subtype, supertype) =
        Map.insertWith keepEarlier supertype subtype known

    keepEarlier _ earlier = earlier

    resolveSupertype supertype = do
        representative <- resolve Set.empty supertype
        pure (supertype, representative)

    resolve visited identifier
        | Set.member identifier visited =
            Left $ CyclicSimilarity $ Set.toAscList $ Set.insert identifier visited
        | otherwise =
            case Map.lookup identifier dominators of
                Nothing -> Right identifier
                Just representative ->
                    resolve (Set.insert identifier visited) representative

    buildRedirects resolved =
        Map.fromList <$> traverse validateRedirect grouped
      where
        grouped =
            Map.toAscList $
                Map.fromListWith
                    Set.union
                    [ (source, Set.singleton destination)
                    | (supertype, representative) <- resolved
                    , let source = transitionTargetState supertype
                    , let destination = transitionTargetState representative
                    , source /= destination
                    ]

        validateRedirect (source, destinations)
            | Set.size destinations > 1 =
                Left $ ConflictingSimilarityTargets source $ Set.toAscList destinations
            | source == automatonInitial automaton = Left $ FinalSimilarityTarget source
            | rowHasSurvivor source = Left $ SharedSimilarityTarget source
            | otherwise = Right (source, Set.findMin destinations)

    rowHasSurvivor state =
        or
            [ Set.notMember (TransitionId state ordinal) removed
            | ordinal <- [0 .. length (Map.findWithDefault [] state table) - 1]
            ]

    retained =
        Map.mapWithKey
            ( \state transitions ->
                [ transition
                | (ordinal, transition) <- zip [0 ..] transitions
                , Set.notMember (TransitionId state ordinal) removed
                ]
            )
            table

-- | Failure in the paper's prune-similarity-minimize reduction phase.
data ReductionError
    = ReductionPrune !PruneError
    | ReductionSimilarity !SimilarityError
    | ReductionMinimize !MinimizeError
    deriving (Eq, Show)

{- | Apply one complete LTA reduction phase to a static automaton.

This keeps the paper's reduction order: semantic pruning, similarity inference,
then minimization.
-}
reduce :: Entailment -> Subtyping -> Automaton -> IO (Either ReductionError Automaton)
reduce entailment subtyping automaton = do
    pruned <- prune entailment automaton
    case pruned of
        Left err -> pure $ Left $ ReductionPrune err
        Right reduced -> do
            inferred <- similarity subtyping reduced
            pure $ do
                related <- first ReductionSimilarity inferred
                first ReductionMinimize $ minimize reduced related

-- | Rewrite every incoming edge that targeted a removed supertype state.
redirectTransition :: Map.Map State State -> Transition -> Transition
redirectTransition redirects transition =
    replaceTransitionChildren
        (map redirect $ transitionChildren transition)
        transition
  where
    redirect state = Map.findWithDefault state state redirects

-- | Every transition paired with its stable address, in table order.
locatedTransitions :: Automaton -> [(TransitionId, Transition)]
locatedTransitions automaton =
    [ (TransitionId state ordinal, transition)
    | (state, transitions) <- Map.toAscList $ automatonTransitions automaton
    , (ordinal, transition) <- zip [0 ..] transitions
    ]

-- | An unordered pair without exposing a tuple nested inside the recursion pattern.
data Pair a = a :&: a

-- | Every unordered pair of distinct list elements, preserving first-seen order.
unorderedPairs :: [a] -> [Pair a]
unorderedPairs [] = []
unorderedPairs (value : rest) = map (value :&:) rest <> unorderedPairs rest

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

{- | Construct the paper's LTA with an arbitrary non-empty final-state set.

Internally, multiple final states are normalized to one fresh state whose row
is the union of their outgoing transitions. This preserves
@union [JqK | q <- Qf]@ from Figure 6 without adding epsilon transitions or
changing any constructor in the ranked alphabet. A singleton set needs no
normalization.
-}
mkAutomatonWithFinals ::
    [State] ->
    [(State, [Transition])] ->
    Either AutomatonError Automaton
mkAutomatonWithFinals [] _ = Left NoFinalStates
mkAutomatonWithFinals finals rows =
    case missingFinals of
        missing : _ -> Left $ MissingFinalState missing
        [] -> case uniqueFinals of
            [final] -> mkAutomaton final rows
            _ -> mkAutomaton normalizedFinal ((normalizedFinal, finalTransitions) : rows)
  where
    table = Map.fromListWith (flip (<>)) rows
    uniqueFinals = Set.toAscList $ Set.fromList finals
    missingFinals = filter (`Map.notMember` table) uniqueFinals
    normalizedFinal = State $ 1 + maximum (-1 : map unState (Map.keys table))
    finalTransitions = concatMap (table Map.!) uniqueFinals

{- | Remove semantically impossible transitions and lower the result to ECTA.

This is the transition-level boundary used by generated LTAs. A guard is
discharged by partitioning the transition sets at every finite position it
observes. A partition is homogeneous in the refinement needed by ordinary
entailment, or in both symbol and refinement where substitution names a value.
Successful combinations become specialized states; failed combinations and
newly dead states are removed to a fixed point. The returned automaton retains
only normalized ECTA equality classes. This is the paper's semantic-intersection
rule, expressed as explicit state splitting without materializing an accepted
tree.

For a required syntactic equality, the paper's ordinary FTA product intersection
narrows the first position to terms also admitted at the second. The equality
class remains on the returned ECTA: intersection can discard disjoint
sub-languages, but equality between two independently chosen arbitrary subtrees
is not in general a regular tree language.
-}
pruneToECTA :: Entailment -> Automaton -> IO (Either PruneError EqualityAutomaton)
pruneToECTA entailment automaton = do
    reduced <- prune entailment automaton
    pure $ reduced >>= lowerToEqualityAutomaton

-- | Compatibility name for 'pruneToECTA'.
pruneSemantics :: Entailment -> Automaton -> IO (Either PruneError EqualityAutomaton)
pruneSemantics = pruneToECTA

{- | Lower a reduced LTA to ECTA when every residual guard is positive equality.

This is an optimization, not LTA semantics. It succeeds for 'Top', 'Same', and
conjunctions of those atoms, combining them with any already-normalized
'EqConstraints'. Negated, disjunctive, or semantic guards remain LTAs and cause
an explicit failure.
-}
lowerToEqualityAutomaton :: Automaton -> Either PruneError EqualityAutomaton
lowerToEqualityAutomaton automaton = do
    rows <- traverse lowerRow $ Map.toList $ automatonTransitions automaton
    case FTA.mkFTA (automatonInitial automaton) rows of
        Left err -> Left $ InvalidPrunedAutomaton $ fromFTAError err
        Right lowered -> Right lowered
  where
    lowerRow (state, transitions) =
        fmap (\lowered -> (state, lowered)) $ traverse (lowerTransition state) transitions

    lowerTransition state (FTA.Transition symbol children constraint) = do
        equalities <- constraintEqualitiesOnly state constraint
        pure $ FTA.Transition symbol children equalities

    fromFTAError (FTA.MissingInitialState state) = MissingInitialState state
    fromFTAError (FTA.DanglingState state) = DanglingState state
    fromFTAError (FTA.InconsistentArity (LiquidSymbol symbol _) expected actual) =
        InconsistentArity symbol expected actual

-- | Extract the ECTA fragment of one complete LTA constraint.
constraintEqualitiesOnly :: State -> LiquidConstraint -> Either PruneError EqConstraints
constraintEqualitiesOnly state LiquidConstraint{constraintEqualities, constraintGuard} =
    combineEqConstraints constraintEqualities <$> guardEqualities constraintGuard
  where
    guardEqualities Top = Right EmptyConstraints
    guardEqualities (Same left right) = Right $ mkEqConstraints [[left, right]]
    guardEqualities (And guards) = foldr combine (Right EmptyConstraints) guards
    guardEqualities residual = Left $ ResidualLTAConstraint state residual

    combine guard rest = combineEqConstraints <$> guardEqualities guard <*> rest

-- | Apply the paper's pruning rules and retain the resulting LTA.
prune :: Entailment -> Automaton -> IO (Either PruneError Automaton)
prune = pruneConstrained

-- | Internal fixed-point pruning while both constraint fields are available.
pruneConstrained :: Entailment -> Automaton -> IO (Either PruneError Automaton)
pruneConstrained entailment automaton = do
    syntactic <- pruneSyntacticEqualities automaton
    case syntactic of
        Left err -> pure $ Left err
        Right narrowed -> loop $ automatonTransitions narrowed
  where
    initial = automatonInitial automaton

    loop table = do
        (checked, split) <-
            runStateT
                (traverseRows table $ Map.toList table)
                (emptySplitBuild $ nextState table)
        case checked of
            Left err -> pure $ Left err
            Right rows -> do
                let withSplits = Map.union (Map.fromList rows) (splitRows split)
                    next = reachableTable initial withSplits
                if next == table
                    then
                        pure $
                            first InvalidPrunedAutomaton $
                                mkAutomaton initial (Map.toList next)
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
        | any (null . transitionsFromTable table) $ transitionChildren transition =
            pruneRow table state rest
        | otherwise = do
            decision <- pruneTransition entailment table state transition
            case decision of
                Left err -> pure $ Left err
                Right retained ->
                    fmap (retained <>) <$> pruneRow table state rest

    transitionsFromTable table state = Map.findWithDefault [] state table

-- | Apply the paper's P-Syn-Eq narrowing once before semantic pruning.
pruneSyntacticEqualities :: Automaton -> IO (Either PruneError Automaton)
pruneSyntacticEqualities automaton = do
    (checked, build) <-
        runStateT
            (traverseRows $ Map.toList original)
            (emptySplitBuild $ nextState original)
    pure $ do
        rows <- checked
        first InvalidPrunedAutomaton $
            mkAutomaton
                (automatonInitial automaton)
                (Map.toList $ Map.union (Map.fromList rows) (splitRows build))
  where
    original = automatonTransitions automaton

    traverseRows [] = pure $ Right []
    traverseRows ((state, transitions) : rest) = do
        row <- traverseTransitions transitions
        case row of
            Left err -> pure $ Left err
            Right narrowed ->
                fmap ((state, narrowed) :) <$> traverseRows rest

    traverseTransitions [] = pure $ Right []
    traverseTransitions (transition : rest) = do
        if constraintsAreContradictory $ transitionEqualities transition
            then traverseTransitions rest
            else do
                narrowed <- applyEqualities [transition] $ requiredConstraintEqualities $ transitionConstraint transition
                case narrowed of
                    Left err -> pure $ Left err
                    Right retained ->
                        fmap (retained <>) <$> traverseTransitions rest

    applyEqualities transitions [] = pure $ Right transitions
    applyEqualities transitions ((left, right) : rest)
        | left == right = applyEqualities transitions rest
        | otherwise = do
            narrowed <- traverse (pruneEquality original left right) transitions
            case sequence narrowed of
                Left err -> pure $ Left err
                Right retained -> applyEqualities (concat retained) rest

-- | One spanning set of path pairs for each normalized ECTA equality class.
requiredEqualityPairs :: EqConstraints -> [(Path, Path)]
requiredEqualityPairs equalities =
    case subsumptionOrderedEclasses equalities of
        Nothing -> []
        Just classes -> concatMap pairs classes
  where
    pairs eclass = case unPathEClass eclass of
        anchor : rest -> map (\other -> (anchor, other)) rest
        [] -> []

-- | Positive syntactic equalities eligible for the paper's P-Syn-Eq rule.
requiredConstraintEqualities :: LiquidConstraint -> [(Path, Path)]
requiredConstraintEqualities LiquidConstraint{constraintEqualities, constraintGuard} =
    requiredEqualityPairs constraintEqualities <> positiveEqualities constraintGuard
  where
    positiveEqualities Top = []
    positiveEqualities (Same left right) = [(left, right)]
    positiveEqualities (And guards) = concatMap positiveEqualities guards
    positiveEqualities _ = []

-- | Narrow one transition at the left side of a required equality.
pruneEquality ::
    Map.Map State [Transition] ->
    Path ->
    Path ->
    Transition ->
    StateT SplitBuild IO (Either PruneError [Transition])
pruneEquality original left right transition = do
    current <- effectiveTable original
    rightStates <- statesAtTransitionPath current transition $ unPath right
    if Set.null rightStates
        then pure $ Right []
        else case unPath left of
            [] -> intersectRoot rightStates
            leftPath -> intersectBelow current leftPath rightStates
  where
    intersectRoot rightStates = do
        leftState <- allocateRow [transition]
        narrowed <- intersectWithStates original leftState rightStates
        case narrowed of
            Left err -> pure $ Left err
            Right state -> do
                table <- effectiveTable original
                pure $ Right $ Map.findWithDefault [] state table

    intersectBelow current leftPath rightStates =
        case statesAtTransitionPathPure current transition leftPath of
            leftStates
                | Set.null leftStates -> pure $ Right []
                | otherwise -> do
                    replacements <- traverse replacement $ Set.toAscList leftStates
                    case sequence replacements of
                        Left err -> pure $ Left err
                        Right pairs -> do
                            rewritten <- rewriteTransitionPath original leftPath (Map.fromList pairs) transition
                            pure $ Right $ maybe [] pure rewritten
      where
        replacement leftState = do
            narrowed <- intersectWithStates original leftState rightStates
            pure $ fmap (\state -> (leftState, state)) narrowed

-- | Intersect one state with the union of the supplied right-hand states.
intersectWithStates ::
    Map.Map State [Transition] ->
    State ->
    Set.Set State ->
    StateT SplitBuild IO (Either PruneError State)
intersectWithStates original leftState rightStates = do
    intersections <- traverse (intersectStatePair original leftState) $ Set.toAscList rightStates
    case sequence intersections of
        Left err -> pure $ Left err
        Right states -> Right <$> unionStates original states

-- | Construct and install a structural product rooted at two LTA states.
intersectStatePair ::
    Map.Map State [Transition] ->
    State ->
    State ->
    StateT SplitBuild IO (Either PruneError State)
intersectStatePair original leftState rightState = do
    table <- effectiveTable original
    case (FTA.mkFTA leftState $ Map.toList table, FTA.mkFTA rightState $ Map.toList table) of
        (Right left, Right right) ->
            case FTA.intersectWith matchSymbol combineConstraints left right of
                Left _ -> pure $ Left InvalidSyntacticIntersection
                Right productAutomaton -> Right <$> installProduct productAutomaton
        _ -> pure $ Left InvalidSyntacticIntersection
  where
    matchSymbol left right
        | left == right = Just left
        | otherwise = Nothing

-- | Conjoin two semantic guards.
combineGuards :: Guard -> Guard -> Guard
combineGuards Top right = right
combineGuards left Top = left
combineGuards left right
    | left == right = left
    | otherwise = And [left, right]

-- | Split independently reducible semantic conjuncts from syntactic equality.
splitGuard :: Guard -> (Guard, Guard)
splitGuard guard
    | not $ containsSame guard = (guard, Top)
splitGuard (And guards) =
    (conjoin semantic, conjoin structural)
  where
    (semantic, structural) = foldr separate ([], []) guards
    separate nested (semanticGuards, structuralGuards)
        | containsSame nested = (semanticGuards, nested : structuralGuards)
        | otherwise = (nested : semanticGuards, structuralGuards)
splitGuard guard = (Top, guard)

-- | Whether a Boolean constraint contains syntactic equality.
containsSame :: Guard -> Bool
containsSame Top = False
containsSame Bottom = False
containsSame (Same _ _) = True
containsSame (Entails _ _) = False
containsSame (Satisfies _ _) = False
containsSame (Substitute _ nested) = containsSame nested
containsSame (Not nested) = containsSame nested
containsSame (And guards) = any containsSame guards
containsSame (Or guards) = any containsSame guards

-- | Build a conjunction without redundant Boolean structure.
conjoin :: [Guard] -> Guard
conjoin [] = Top
conjoin [guard] = guard
conjoin guards = And guards

-- | Install reachable product rows, reusing any pair already constructed.
installProduct ::
    FTA.FTA (FTA.ProductState State State) LiquidSymbol LiquidConstraint ->
    StateT SplitBuild IO State
installProduct productAutomaton = do
    build <- get
    let productStates = FTA.states productAutomaton
        missing = filter (`Map.notMember` splitProducts build) productStates
        fresh = map State [splitNextState build ..]
        allocated = Map.fromList $ zip missing fresh
        products = Map.union (splitProducts build) allocated
        installed =
            Map.fromList
                [ (stateFor productState products, map (mapTransition products) $ FTA.transitionsFrom productAutomaton productState)
                | productState <- missing
                ]
    modify' $ \updated ->
        updated
            { splitNextState = splitNextState updated + length missing
            , splitRows = Map.union installed $ splitRows updated
            , splitProducts = products
            }
    pure $ stateFor (FTA.initialState productAutomaton) products
  where
    stateFor productState products = products Map.! productState

    mapTransition products (FTA.Transition symbol children guard) =
        FTA.Transition symbol (map (`stateFor` products) children) guard

-- | Form a union state without copying descendants.
unionStates :: Map.Map State [Transition] -> [State] -> StateT SplitBuild IO State
unionStates original states =
    case Set.toAscList $ Set.fromList states of
        [state] -> pure state
        unique -> do
            table <- effectiveTable original
            allocateRow $ concatMap (\state -> Map.findWithDefault [] state table) unique

-- | Allocate one fresh state with the supplied outgoing row.
allocateRow :: [Transition] -> StateT SplitBuild IO State
allocateRow transitions = do
    build <- get
    let state = State $ splitNextState build
    modify' $ \updated ->
        updated
            { splitNextState = splitNextState updated + 1
            , splitRows = Map.insert state transitions $ splitRows updated
            }
    pure state

-- | Include all rows allocated earlier in this syntactic pruning phase.
effectiveTable :: Map.Map State [Transition] -> StateT SplitBuild IO (Map.Map State [Transition])
effectiveTable original = do
    build <- get
    pure $ Map.union (splitRows build) original

-- | States reached at one path under a particular transition.
statesAtTransitionPath ::
    Map.Map State [Transition] ->
    Transition ->
    [Int] ->
    StateT SplitBuild IO (Set.Set State)
statesAtTransitionPath _ transition [] = Set.singleton <$> allocateRow [transition]
statesAtTransitionPath table transition target =
    pure $ statesAtTransitionPathPure table transition target

-- | Pure non-root case of 'statesAtTransitionPath'.
statesAtTransitionPathPure ::
    Map.Map State [Transition] ->
    Transition ->
    [Int] ->
    Set.Set State
statesAtTransitionPathPure _ _ [] = Set.empty
statesAtTransitionPathPure table transition (index : rest) =
    descend rest $ maybe Set.empty Set.singleton $ atIndex index $ transitionChildren transition
  where
    descend [] current = current
    descend (childIndex : remaining) current =
        descend remaining . Set.fromList $
            [ child
            | state <- Set.toList current
            , outgoing <- Map.findWithDefault [] state table
            , child <- maybe [] pure $ atIndex childIndex $ transitionChildren outgoing
            ]

-- | Clone the context above a path and replace each endpoint state.
rewriteTransitionPath ::
    Map.Map State [Transition] ->
    [Int] ->
    Map.Map State State ->
    Transition ->
    StateT SplitBuild IO (Maybe Transition)
rewriteTransitionPath _ [] _ transition = pure $ Just transition
rewriteTransitionPath original (index : rest) replacements transition =
    case atIndex index $ transitionChildren transition of
        Nothing -> pure Nothing
        Just child -> do
            rewritten <- rewriteStatePath original rest replacements child
            pure $ fmap (replaceChild index transition) rewritten

-- | Clone all viable transitions on one path down to a replacement endpoint.
rewriteStatePath ::
    Map.Map State [Transition] ->
    [Int] ->
    Map.Map State State ->
    State ->
    StateT SplitBuild IO (Maybe State)
rewriteStatePath _ [] replacements state = pure $ Map.lookup state replacements
rewriteStatePath original components replacements state = do
    table <- effectiveTable original
    rewritten <- traverse (rewriteTransitionPath original components replacements) $ Map.findWithDefault [] state table
    Just <$> allocateRow [transition | Just transition <- rewritten]

-- | Replace one known-valid child position.
replaceChild :: Int -> Transition -> State -> Transition
replaceChild index transition child =
    replaceTransitionChildren
        (take index children <> [child] <> drop (index + 1) children)
        transition
  where
    children = transitionChildren transition

-- | How precisely one observed position must be partitioned.
data ObservationNeed
    = RefinementNeed
    | LiquidSymbolNeed
    deriving (Eq, Ord, Show)

-- | Trie of the finite term positions inspected by one semantic guard.
data PathPlan = PathPlan
    { planObservation :: !(Maybe ObservationNeed)
    , planChildren :: !(Map.Map Int PathPlan)
    }
    deriving (Eq, Ord, Show)

-- | One value used to partition a state at an observed position.
data Observation
    = RefinementObservation !Refinement
    | LiquidSymbolObservation !LiquidSymbol
    deriving (Eq, Ord, Show)

-- | One state whose language is homogeneous at every planned position.
data StateVariant = StateVariant
    { variantState :: !State
    , variantSignature :: !(Map.Map [Int] Observation)
    , variantSymbols :: !(Map.Map [Int] LiquidSymbol)
    }

-- | One candidate transition before equal observation signatures are regrouped.
data TransitionVariant = TransitionVariant
    { transitionVariantSignature :: !(Map.Map [Int] Observation)
    , transitionVariantSymbols :: !(Map.Map [Int] LiquidSymbol)
    , transitionVariantValue :: !Transition
    }

-- | Transitions that form one homogeneous split state.
data VariantGroup = VariantGroup
    { groupSignature :: !(Map.Map [Int] Observation)
    , groupSymbols :: !(Map.Map [Int] LiquidSymbol)
    , groupTransitions :: ![Transition]
    }

-- | Fresh states and memoized state partitions constructed during one pruning round.
data SplitBuild = SplitBuild
    { splitNextState :: !Int
    , splitRows :: !(Map.Map State [Transition])
    , splitMemo :: !(Map.Map (State, PathPlan) [StateVariant])
    , splitProducts :: !(Map.Map (FTA.ProductState State State) State)
    }

-- | Initial state for one splitting round.
emptySplitBuild :: Int -> SplitBuild
emptySplitBuild firstFresh = SplitBuild firstFresh Map.empty Map.empty Map.empty

-- | One state identity beyond every state currently in the automaton.
nextState :: Map.Map State [Transition] -> Int
nextState table =
    1 + maximum (-1 : [unState state | state <- Map.keys table])

-- | Compile one transition's semantic guard by partitioning only its observed paths.
pruneTransition ::
    Entailment ->
    Map.Map State [Transition] ->
    State ->
    Transition ->
    StateT SplitBuild IO (Either PruneError [Transition])
pruneTransition entailment table parent transition
    | semanticGuard == Top = pure $ Right [setTransitionGuard residualGuard transition]
    | otherwise = do
        candidates <- transitionSpecializations table semanticGuard transition
        check candidates
  where
    (semanticGuard, residualGuard) = splitGuard $ transitionGuard transition

    check [] = pure $ Right []
    check ((specialized, resolved) : rest) = do
        verdict <-
            liftIO $
                evaluateGuard
                    entailment
                    semanticGuard
                    (sparseTerm specialized $ map resolvedPosition $ Map.toList resolved)
        case verdict of
            Yes -> do
                remaining <- check rest
                pure $ fmap (setTransitionGuard residualGuard specialized :) remaining
            No -> check rest
            Unknown -> pure $ Left $ PruneUnknown parent

    resolvedPosition (components, symbol) = (path components, symbol)

-- | Replace a transition's guard without changing its ranked symbol or states.
setTransitionGuard :: Guard -> Transition -> Transition
setTransitionGuard guard transition =
    Transition
        (transitionSymbol transition)
        (transitionRefinement transition)
        (transitionChildren transition)
        (transitionConstraint transition){constraintGuard = guard}

-- | Every homogeneous child-state specialization required to evaluate one guard.
transitionSpecializations ::
    Map.Map State [Transition] ->
    Guard ->
    Transition ->
    StateT SplitBuild IO [(Transition, Map.Map [Int] LiquidSymbol)]
transitionSpecializations table guard transition = do
    children <- specializeChildren table (planChildren plan) $ transitionChildren transition
    pure
        [ ( replaceTransitionChildren specializedChildren transition
          , rootSymbols `Map.union` childSymbols
          )
        | (specializedChildren, _, childSymbols) <- children
        ]
  where
    plan = planGuard guard
    rootSymbols = case planObservation plan of
        Nothing -> Map.empty
        Just _ -> Map.singleton [] $ transitionLiquidSymbol transition

-- | Partition one state's language by the observations in a path plan.
specializeState ::
    Map.Map State [Transition] ->
    State ->
    PathPlan ->
    StateT SplitBuild IO [StateVariant]
specializeState table state plan = do
    build <- get
    case Map.lookup (state, plan) $ splitMemo build of
        Just variants -> pure variants
        Nothing -> do
            candidates <-
                concat
                    <$> traverse
                        (specializeStateTransition table plan)
                        (Map.findWithDefault [] state table)
            variants <- traverse allocateVariant $ groupVariants candidates
            modify' $ \updated ->
                updated
                    { splitMemo = Map.insert (state, plan) variants $ splitMemo updated
                    }
            pure variants

-- | Specialize one transition inside a state being partitioned.
specializeStateTransition ::
    Map.Map State [Transition] ->
    PathPlan ->
    Transition ->
    StateT SplitBuild IO [TransitionVariant]
specializeStateTransition table plan transition = do
    children <- specializeChildren table (planChildren plan) $ transitionChildren transition
    pure
        [ TransitionVariant
            (rootSignature `Map.union` childSignature)
            (rootSymbols `Map.union` childSymbols)
            (replaceTransitionChildren specializedChildren transition)
        | (specializedChildren, childSignature, childSymbols) <- children
        ]
  where
    liquidSymbol = transitionLiquidSymbol transition
    rootSignature = case planObservation plan of
        Nothing -> Map.empty
        Just need -> Map.singleton [] $ observe need liquidSymbol
    rootSymbols = case planObservation plan of
        Nothing -> Map.empty
        Just _ -> Map.singleton [] liquidSymbol

-- | Cartesian product of child variants, sharing every unobserved child state.
specializeChildren ::
    Map.Map State [Transition] ->
    Map.Map Int PathPlan ->
    [State] ->
    StateT SplitBuild IO [([State], Map.Map [Int] Observation, Map.Map [Int] LiquidSymbol)]
specializeChildren table plans children
    | any invalid $ Map.keys plans = pure []
    | otherwise = go 0 children
  where
    invalid index = index < 0 || index >= length children

    go _ [] = pure [([], Map.empty, Map.empty)]
    go index (child : rest) = do
        variants <- case Map.lookup index plans of
            Nothing -> pure [StateVariant child Map.empty Map.empty]
            Just plan -> specializeState table child plan
        suffixes <- go (index + 1) rest
        pure
            [ ( variantState variant : suffixStates
              , prefixMap index (variantSignature variant) `Map.union` suffixSignature
              , prefixMap index (variantSymbols variant) `Map.union` suffixSymbols
              )
            | variant <- variants
            , (suffixStates, suffixSignature, suffixSymbols) <- suffixes
            ]

-- | Prefix every relative observation path by one child index.
prefixMap :: Int -> Map.Map [Int] value -> Map.Map [Int] value
prefixMap index = Map.mapKeysMonotonic (index :)

-- | Allocate one fresh state for a homogeneous transition group.
allocateVariant :: VariantGroup -> StateT SplitBuild IO StateVariant
allocateVariant VariantGroup{groupSignature, groupSymbols, groupTransitions} = do
    build <- get
    let state = State $ splitNextState build
    modify' $ \updated ->
        updated
            { splitNextState = splitNextState updated + 1
            , splitRows = Map.insert state groupTransitions $ splitRows updated
            }
    pure $ StateVariant state groupSignature groupSymbols

-- | Regroup transition candidates without disturbing first-seen rank order.
groupVariants :: [TransitionVariant] -> [VariantGroup]
groupVariants = foldl' insertVariant []
  where
    insertVariant [] variant = [singletonGroup variant]
    insertVariant (group : rest) variant
        | groupSignature group == transitionVariantSignature variant =
            group
                { groupTransitions =
                    groupTransitions group <> [transitionVariantValue variant]
                }
                : rest
        | otherwise = group : insertVariant rest variant

    singletonGroup TransitionVariant{transitionVariantSignature, transitionVariantSymbols, transitionVariantValue} =
        VariantGroup
            transitionVariantSignature
            transitionVariantSymbols
            [transitionVariantValue]

-- | Observation used to partition a state's transitions.
observe :: ObservationNeed -> LiquidSymbol -> Observation
observe RefinementNeed (LiquidSymbol _ refinement) = RefinementObservation refinement
observe LiquidSymbolNeed symbol = LiquidSymbolObservation symbol

-- | Construct the observation trie for every position read by a semantic guard.
planGuard :: Guard -> PathPlan
planGuard guard =
    foldl'
        (flip $ uncurry insertPlan)
        emptyPlan
        observations
  where
    sensitive = Set.fromList $ symbolSensitivePaths guard
    observations =
        [ ( unPath target
          , if Set.member target sensitive then LiquidSymbolNeed else RefinementNeed
          )
        | target <- Set.toList $ Set.fromList $ guardPaths guard
        ]

-- | An observation plan containing no positions.
emptyPlan :: PathPlan
emptyPlan = PathPlan Nothing Map.empty

-- | Insert or strengthen one observed position in a path trie.
insertPlan :: [Int] -> ObservationNeed -> PathPlan -> PathPlan
insertPlan [] need plan =
    plan{planObservation = Just $ maybe need (max need) $ planObservation plan}
insertPlan (index : rest) need plan =
    plan
        { planChildren =
            Map.alter
                (Just . insertPlan rest need . maybe emptyPlan id)
                index
                (planChildren plan)
        }

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

-- | Replace only the child states of one transition.
replaceTransitionChildren :: [State] -> Transition -> Transition
replaceTransitionChildren children transition =
    Transition
        (transitionSymbol transition)
        (transitionRefinement transition)
        children
        (transitionConstraint transition)

-- | Keep only states reachable from the initial state.
reachableTable :: State -> Map.Map State [Transition] -> Map.Map State [Transition]
reachableTable initial table =
    Map.restrictKeys table $ visit Set.empty [initial]
  where
    visit reached [] = reached
    visit reached (state : rest)
        | Set.member state reached = visit reached rest
        | otherwise =
            visit
                (Set.insert state reached)
                ( concatMap transitionChildren (Map.findWithDefault [] state table)
                    <> rest
                )

-- | Liquid symbol carried by a transition.
transitionLiquidSymbol :: Transition -> LiquidSymbol
transitionLiquidSymbol (FTA.Transition symbol _ _) = symbol

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
        , target <- constraintPaths $ transitionConstraint transition
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

-- | Check positive ECTA equality classes against the complete LTA term shape.
satisfiesEqualities :: EqConstraints -> LiquidTerm -> Bool
satisfiesEqualities equalities term =
    case subsumptionOrderedEclasses equalities of
        Nothing -> False
        Just classes -> all classSatisfied classes
  where
    classSatisfied eclass = case unPathEClass eclass of
        [] -> True
        firstPath : rest ->
            case termAt firstPath term of
                Nothing -> False
                Just expected ->
                    all
                        (\target -> termAt target term == Just expected)
                        rest

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

resolveSubstitutionWith ::
    (Path -> Maybe (Symbol, Refinement)) ->
    Substitution ->
    Maybe ResolvedSubstitution
resolveSubstitutionWith lookupObservation Substitution{substitutionActual, substitutionFormal} = do
    (Symbol actualName, actualRefinement) <- lookupObservation substitutionActual
    (Symbol formalName, _) <- lookupObservation substitutionFormal
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
