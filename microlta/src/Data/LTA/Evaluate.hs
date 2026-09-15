{- | Decide an LTA guard against a term or against sparse observations.

'evaluateGuard' reads a complete candidate term. 'evaluateGuardWithShape' reads
only the positions a guard names, which lets the pruner decide a guard without
enumerating terms. Both share one evaluator, so the two views cannot drift.
-}
module Data.LTA.Evaluate (
    evaluateGuard,
    evaluateGuardWithShape,
    evaluateConstraint,
    substitutionValues,
) where

import Data.List (nub)
import qualified Data.Map.Strict as Map
import Data.Maybe (isNothing)
import qualified Data.Set as Set

import Data.ECTA.Paths (EqConstraints, Path)
import Data.ECTA.Term (Symbol (Symbol))
import qualified Language.Fixpoint.Types as Fixpoint

import Data.LTA.Constraint (
    Guard (..),
    LiquidConstraint (constraintEqualities, constraintGuard),
    Substitution (..),
    equalityPathPairs,
    guardPaths,
 )
import Data.LTA.Types (LiquidTerm (..), Refinement, termAt)
import Data.LTA.Verdict (
    Entailment,
    Verdict (..),
    andM,
    entailsWithBindings,
    negateVerdict,
    orM,
 )

-- | Evaluate a guard against one candidate term.
evaluateGuard :: Entailment -> Guard -> LiquidTerm -> IO Verdict
evaluateGuard entailment guard term =
    evaluateGuardWithSame entailment lookupObservation leafAt sameAt guard
  where
    lookupObservation target = do
        observed <- termAt target term
        pure (liquidSymbol observed, liquidRefinement observed)

    sameAt substitutions left right = do
        leftTerm <- termAt left term
        rightTerm <- termAt right term
        pure $ substituteTerm substitutions leftTerm == substituteTerm substitutions rightTerm

    leafAt target = null . liquidChildren <$> termAt target term

{- | Evaluate a guard from sparse observations of its referenced paths.

The first callback returns the unrefined constructor symbol and refinement at
one path. 'Same' rejects absent paths and accepts an existing path compared
with itself. The shape callback returns 'Just' 'True' for a leaf and 'Just'
'False' for a non-leaf; equal named leaves denote the same ambient value,
while separate non-leaf positions may denote different results despite equal
constructor labels. With no shape information, a comparison of complete
subtrees at distinct positions yields 'Unknown', so an optimizer must reject
that fast path or supply a complete-term equality oracle.
-}
evaluateGuardWithShape ::
    Entailment ->
    (Path -> Maybe (Symbol, Refinement)) ->
    (Path -> Maybe Bool) ->
    Guard ->
    IO Verdict
evaluateGuardWithShape entailment lookupObservation leafAt =
    evaluateGuardWithSame entailment lookupObservation leafAt sameAt
  where
    sameAt scopes left right = do
        leftObservation <- substituteObservation scopes <$> lookupObservation left
        rightObservation <- substituteObservation scopes <$> lookupObservation right
        if leftObservation /= rightObservation
            then Just False
            else case (leafAt left, leafAt right) of
                (Just True, Just True) -> Just True
                (Just leftLeaf, Just rightLeaf) | leftLeaf /= rightLeaf -> Just False
                _ -> Nothing

-- | Shared evaluator with an optional complete-subtree equality oracle.
evaluateGuardWithSame ::
    Entailment ->
    (Path -> Maybe (Symbol, Refinement)) ->
    (Path -> Maybe Bool) ->
    ([[ResolvedSubstitution]] -> Path -> Path -> Maybe Bool) ->
    Guard ->
    IO Verdict
evaluateGuardWithSame entailment lookupObservation leafAt sameAt guard = go guard
  where
    go = evaluateWith []
    (freshValues, ambiguousValues) = substitutionValues lookupObservation leafAt (sameAt []) guard

    decide substitutions antecedent consequent = do
        verdict <- entailsWithBindings entailment bindings antecedent consequent
        pure $ case verdict of
            No | not (all (all resolvedIdentityKnown) substitutions) -> Unknown
            _ -> verdict
      where
        bindings =
            nub
                [ binding
                | scope <- substitutions
                , resolved <- scope
                , Just binding <- [resolvedDeclaration resolved]
                ]

    evaluateWith _ Top = pure Yes
    evaluateWith _ Bottom = pure No
    evaluateWith substitutions (Same left right) =
        pure $ case (lookupObservation left, lookupObservation right) of
            (Just _, Just _)
                | left == right -> Yes
                | otherwise -> case sameAt substitutions left right of
                    Just True -> Yes
                    Just False -> No
                    Nothing -> Unknown
            _ -> No
    evaluateWith substitutions (Entails antecedent consequent) =
        case (lookupObservation antecedent, lookupObservation consequent) of
            (Just (_, leftRefinement), Just (_, rightRefinement)) ->
                decide
                    substitutions
                    ( withActualAssumptions substitutions
                        $ applySubstitutions substitutions
                        $ leftRefinement
                    )
                    (applySubstitutions substitutions rightRefinement)
            _ -> pure No
    evaluateWith substitutions (Satisfies target requirement) =
        case lookupObservation target of
            Just (_, targetRefinement) ->
                decide
                    substitutions
                    ( withActualAssumptions substitutions
                        $ applySubstitutions substitutions
                        $ targetRefinement
                    )
                    (applySubstitutions substitutions requirement)
            Nothing -> pure No
    evaluateWith substitutions (Substitute additions nested) =
        case traverse (resolveSubstitutionWith lookupObservation freshValues ambiguousValues) additions of
            Just resolved -> evaluateWith (resolved : substitutions) nested
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

-- | Check positive ECTA equality classes against the complete LTA term shape.
satisfiesEqualities :: EqConstraints -> LiquidTerm -> Bool
satisfiesEqualities equalities term =
    maybe False (all agrees) $ equalityPathPairs equalities
  where
    agrees (anchor, other) = case termAt anchor term of
        Nothing -> False
        Just expected -> termAt other term == Just expected

{- | One position substitution with its actual-value assumption.

Keep solver bookkeeping lazy. Structural comparisons need only the literal
symbol mapping, so they must not inspect actual-term identity for solver names.
-}
data ResolvedSubstitution = ResolvedSubstitution
    { resolvedReplacement :: (Fixpoint.Symbol, Fixpoint.Expr)
    , resolvedSymbolReplacement :: !(Symbol, Symbol)
    , resolvedActualAssumption :: Refinement
    , resolvedDeclaration :: Maybe (Fixpoint.Symbol, Fixpoint.Symbol)
    , resolvedIdentityKnown :: Bool
    }

{- | Allocate distinct values for actual positions that share a name.

An unambiguous name retains its ambient meaning. Repeated positions share one
value. Distinct positions with the same name receive separate solver values.
-}
substitutionValues ::
    (Path -> Maybe (Symbol, Refinement)) ->
    (Path -> Maybe Bool) ->
    (Path -> Path -> Maybe Bool) ->
    Guard ->
    (Map.Map Path (Fixpoint.Symbol, Fixpoint.Symbol), Set.Set Path)
substitutionValues lookupObservation leafAt sameAt guard =
    ( Map.fromList
        [ (target, binding)
        | actual@(target, _, _) <- actuals
        , Just binding <- [Map.lookup (representative actual) allocated]
        ]
    , ambiguous
    )
  where
    actuals =
        [ (target, Fixpoint.symbol name, refinement)
        | target <- Set.toAscList $ Set.fromList $ actualPaths guard
        , Just (Symbol name, refinement) <- [lookupObservation target]
        ]
    representative (target, name, refinement) =
        case [ other
             | (other, otherName, otherRefinement) <- actuals
             , otherName == name
             , otherRefinement == refinement
             , sameAt target other == Just True
                || (leafAt target == Just True && leafAt other == Just True)
             ] of
            canonical : _ -> canonical
            [] -> target
    values = nub [(representative actual, name) | actual@(_, name, _) <- actuals]
    names = Map.fromListWith (+) [(name, 1 :: Int) | (_, name) <- values]
    conflicts = [(target, name) | (target, name) <- values, names Map.! name > 1]
    allocated = Map.fromList $ zipWith allocate conflicts available
    allocate (target, original) fresh = (target, (fresh, original))
    ambiguous =
        Set.fromList
            [ target
            | (target, name, refinement) <- actuals
            , (other, otherName, otherRefinement) <- actuals
            , target /= other
            , name == otherName
            , refinement == otherRefinement
            , isNothing (sameAt target other)
            , leafAt target /= Just True || leafAt other /= Just True
            ]
    available =
        filter (`Set.notMember` used) $
            [Fixpoint.symbol $ "__microlta_actual_" <> show index | index <- [0 :: Integer ..]]
    used =
        Set.fromList $
            concat
                [ Fixpoint.symbol name : Fixpoint.syms refinement
                | target <- guardPaths guard
                , Just (Symbol name, refinement) <- [lookupObservation target]
                ]
                <> concatMap Fixpoint.syms (requirements guard)

    actualPaths (Substitute substitutions nested) =
        map substitutionActual substitutions <> actualPaths nested
    actualPaths (Not nested) = actualPaths nested
    actualPaths (And guards) = concatMap actualPaths guards
    actualPaths (Or guards) = concatMap actualPaths guards
    actualPaths _ = []

    requirements (Satisfies _ refinement) = [refinement]
    requirements (Substitute _ nested) = requirements nested
    requirements (Not nested) = requirements nested
    requirements (And guards) = concatMap requirements guards
    requirements (Or guards) = concatMap requirements guards
    requirements _ = []

-- | Resolve actual and formal positions within one simultaneous scope.
resolveSubstitutionWith ::
    (Path -> Maybe (Symbol, Refinement)) ->
    Map.Map Path (Fixpoint.Symbol, Fixpoint.Symbol) ->
    Set.Set Path ->
    Substitution ->
    Maybe ResolvedSubstitution
resolveSubstitutionWith lookupObservation freshValues ambiguousValues Substitution{substitutionActual, substitutionFormal} = do
    (Symbol actualName, actualRefinement) <- lookupObservation substitutionActual
    (Symbol formalName, _) <- lookupObservation substitutionFormal
    let declaration = Map.lookup substitutionActual freshValues
        actualSymbol = maybe (Fixpoint.symbol actualName) fst declaration
        actualVariable = Fixpoint.EVar actualSymbol
    pure
        ResolvedSubstitution
            { resolvedReplacement = (Fixpoint.symbol formalName, actualVariable)
            , resolvedSymbolReplacement = (Symbol formalName, Symbol actualName)
            , resolvedActualAssumption =
                substituteRefinement [(refinementValueSymbol, actualVariable)] actualRefinement
            , resolvedDeclaration = declaration
            , resolvedIdentityKnown = Set.notMember substitutionActual ambiguousValues
            }

-- | Conventional value variable used by public microlta refinements.
refinementValueSymbol :: Fixpoint.Symbol
refinementValueSymbol = Fixpoint.symbol ("v" :: String)

-- | Apply simultaneous scopes from the innermost scope to the outermost.
applySubstitutions :: [[ResolvedSubstitution]] -> Refinement -> Refinement
applySubstitutions scopes refinement =
    foldl apply refinement scopes
  where
    apply predicate scope =
        substituteRefinement (map resolvedReplacement scope) predicate

{- | Apply scoped symbol substitutions to one structural comparison operand.

Each scope renames symbols simultaneously, including free names in refinement
annotations. Refinement binders remain capture-avoiding. Constructor children
stay in place: a name substitution does not splice in the actual subtree.
Solver-generated value identities are not symbols in the structural alphabet.
The first non-identity mapping for a repeated formal name takes precedence,
matching refinement substitution.
-}
substituteTerm :: [[ResolvedSubstitution]] -> LiquidTerm -> LiquidTerm
substituteTerm scopes (LiquidTerm symbol refinement children) =
    let (renamed, annotation) = substituteObservation scopes (symbol, refinement)
     in LiquidTerm renamed annotation $ map (substituteTerm scopes) children

-- | Apply structural name substitutions to one finite root observation.
substituteObservation :: [[ResolvedSubstitution]] -> (Symbol, Refinement) -> (Symbol, Refinement)
substituteObservation scopes observation = foldl apply observation scopes
  where
    apply (symbol, refinement) scope =
        ( Map.findWithDefault symbol symbol replacements
        , substituteRefinement refinementReplacements refinement
        )
      where
        replacements =
            Map.fromList $ reverse $ filter (uncurry (/=)) $ map resolvedSymbolReplacement scope
        refinementReplacements =
            [ (Fixpoint.symbol formal, Fixpoint.EVar $ Fixpoint.symbol actual)
            | (Symbol formal, Symbol actual) <- Map.toList replacements
            ]

-- | Substitute simultaneously and rename binders to prevent name capture.
substituteRefinement :: [(Fixpoint.Symbol, Fixpoint.Expr)] -> Refinement -> Refinement
substituteRefinement replacements refinement =
    Fixpoint.rapierSubstExpr
        (Fixpoint.exprSymbolsSet refinement <> Fixpoint.substSymbolsSet substitution)
        substitution
        refinement
  where
    substitution = Fixpoint.mkSubst replacements

{- | Add the instantiated refinement of every actual argument to an entailment
antecedent.

Substitution changes a formal name to the actual term's symbol. This assumption
connects that symbol back to the refinement carried by the actual subtree, so
dependent results compose through non-leaf nodes as well as named pool entries.
Actual terms belong to the surrounding environment. Guard substitutions do not
rename their value identities or their refinement assumptions.
-}
withActualAssumptions :: [[ResolvedSubstitution]] -> Refinement -> Refinement
withActualAssumptions scopes predicate =
    Fixpoint.pAnd $
        map resolvedActualAssumption (concat scopes)
            <> [predicate]
