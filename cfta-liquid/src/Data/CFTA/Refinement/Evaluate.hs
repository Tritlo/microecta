{- | Decide an LTA guard against a term or against sparse observations.

'evaluateGuard' reads a complete candidate term. 'evaluateGuardWithShape' reads
only the positions a guard names, which lets the pruner decide a guard without
enumerating terms. Both share one evaluator, so the two views cannot drift.
-}
module Data.CFTA.Refinement.Evaluate (
    Observed (..),
    Leafness (..),
    Observations,
    leafnessOf,
    evaluateGuard,
    evaluateGuardWithShape,
    evaluateConstraint,
    substitutionValues,
) where

import Data.Containers.ListUtils (nubOrd)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust, isNothing)
import qualified Data.Set as Set
import Data.String (fromString)

import Data.CFTA.Index (ArgumentIndex (..))
import Data.CFTA.Path (Path, getPath)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

import Data.CFTA.Constraint (
    Constraint (constraintGuard),
    Guard (..),
    Substitution (..),
    contractTermName,
    equalitiesHold,
    guardPaths,
 )
import Data.CFTA.Formula (Name (..))
import qualified Data.CFTA.Formula as Formula
import Data.CFTA.Refinement.Verdict (
    Entailment,
    Verdict (..),
    andVerdicts,
    entailsWithBindings,
    negateVerdict,
    orVerdicts,
 )
import Data.CFTA.Symbol (Formula, Symbol (RefinedSymbol, Symbol), valueName)

{- | What a guard reads at one path: the symbol, and whether the node there is
a leaf.

The order compares the symbol texts, then the refinements, then the
leafness. It does not compare the interned identities of the symbols, because
these differ between processes. The refinement compiler orders its groups by
their observations, so ranks follow this order.
-}
data Observed = Observed
    { observedSymbol :: !Symbol
    , observedLeaf :: !Leafness
    }
    deriving (Eq, Ord, Show)

{- | Whether the node at a path is a leaf. 'Mixed' is for a group of terms:
some members of the group are leaves and some are not. An observer reads
'Mixed' as not known.

The constructors are in the order that ranks follow: 'Mixed', then 'Inner',
then 'Leaf'.
-}
data Leafness = Mixed | Inner | Leaf
    deriving (Eq, Ord, Show)

-- | The observation at each observed path of a term or of a group.
type Observations = Map.Map Path Observed

-- | 'Leaf' for a node without children, and 'Inner' for a node with children.
leafnessOf :: [child] -> Leafness
leafnessOf children = if null children then Leaf else Inner
{-# INLINE leafnessOf #-}

-- | Evaluate a guard against one candidate term.
evaluateGuard :: Entailment -> Guard -> Term Symbol -> IO Verdict
evaluateGuard entailment guard term =
    evaluateGuardWithSame entailment observedAt sameAt guard
  where
    observedAt target = do
        Term.Node symbol children <- getPath target term
        pure $ Observed symbol $ leafnessOf children

    sameAt substitutions left right = do
        leftTerm <- getPath left term
        rightTerm <- getPath right term
        pure $ substituteTerm substitutions leftTerm == substituteTerm substitutions rightTerm

{- | Evaluate a guard from sparse observations of its referenced paths.

The callback returns the symbol at one path and whether the node there is a
leaf. 'Same' rejects absent paths and accepts an existing path compared with
itself. Equal named leaves denote the same ambient value, while separate
'Inner' positions may denote different results despite equal constructor
labels. 'Mixed' gives no shape information. Without shape information, a
comparison of complete subtrees at distinct positions yields 'Unknown', so an
optimizer must reject that fast path or supply a complete-term equality
oracle. The refinement compiler rejects it: it reports
@RelationalSyntacticEqualityUnsupported@ for such a comparison.
-}
evaluateGuardWithShape ::
    Entailment ->
    (Path -> Maybe Observed) ->
    Guard ->
    IO Verdict
evaluateGuardWithShape entailment observedAt =
    evaluateGuardWithSame entailment observedAt sameAt
  where
    sameAt scopes left right = do
        Observed leftSymbol leftLeaf <- observedAt left
        Observed rightSymbol rightLeaf <- observedAt right
        if substituted leftSymbol /= substituted rightSymbol
            then Just False
            else case (leftLeaf, rightLeaf) of
                (Leaf, Leaf) -> Just True
                (Leaf, Inner) -> Just False
                (Inner, Leaf) -> Just False
                _ -> Nothing
      where
        substituted (RefinedSymbol symbol refinement) = substituteObservation scopes (symbol, refinement)

-- | Shared evaluator with an optional complete-subtree equality oracle.
evaluateGuardWithSame ::
    Entailment ->
    (Path -> Maybe Observed) ->
    ([[ResolvedSubstitution]] -> Path -> Path -> Maybe Bool) ->
    Guard ->
    IO Verdict
evaluateGuardWithSame entailment observedAt sameAt guard = go guard
  where
    go = evaluateWith []
    (freshValues, ambiguousValues) = substitutionValues observedAt (sameAt []) guard

    decide = decideWith []

    decideWith extraBindings substitutions antecedent consequent = do
        verdict <- entailsWithBindings entailment bindings antecedent consequent
        pure $ case verdict of
            No | not (all (all resolvedIdentityKnown) substitutions) -> Unknown
            _ -> verdict
      where
        bindings =
            nubOrd $
                extraBindings
                    <> [ binding
                       | scope <- substitutions
                       , resolved <- scope
                       , Just binding <- [resolvedDeclaration resolved]
                       ]

    evaluateWith _ Top = pure Yes
    evaluateWith _ Bottom = pure No
    evaluateWith substitutions (Same left right) =
        pure $ case (observedAt left, observedAt right) of
            (Just _, Just _)
                | left == right -> Yes
                | otherwise -> case sameAt substitutions left right of
                    Just True -> Yes
                    Just False -> No
                    Nothing -> Unknown
            _ -> No
    evaluateWith substitutions (Entails antecedent consequent) =
        case (observedAt antecedent, observedAt consequent) of
            (Just (Observed (RefinedSymbol _ leftRefinement) _), Just (Observed (RefinedSymbol _ rightRefinement) _)) ->
                decide
                    substitutions
                    ( withActualAssumptions substitutions $
                        applySubstitutions
                            substitutions
                            leftRefinement
                    )
                    (applySubstitutions substitutions rightRefinement)
            _ -> pure No
    evaluateWith substitutions (Satisfies target requirement) =
        case observedAt target of
            Just (Observed (RefinedSymbol _ targetRefinement) _) ->
                decide
                    substitutions
                    ( withActualAssumptions substitutions $
                        applySubstitutions
                            substitutions
                            targetRefinement
                    )
                    (applySubstitutions substitutions requirement)
            Nothing -> pure No
    evaluateWith substitutions (Holds targets formula) =
        case traverse observedAt targets of
            Just observations ->
                let formals = [fromString (contractTermName index) | index <- map ArgumentIndex [0 .. length targets - 1]]
                    assumed =
                        Formula.conjunction
                            [ Formula.substitute [(refinementValueName, Formula.Var formal)] refinement
                            | (formal, Observed (RefinedSymbol _ refinement) _) <- zip formals observations
                            ]
                 in decideWith
                        [(formal, refinementValueName) | formal <- formals]
                        substitutions
                        (withActualAssumptions substitutions $ applySubstitutions substitutions assumed)
                        (applySubstitutions substitutions formula)
            Nothing -> pure No
    evaluateWith substitutions (Substitute additions nested) =
        case traverse (resolveSubstitutionWith observedAt freshValues ambiguousValues) additions of
            Just resolved -> evaluateWith (resolved : substitutions) nested
            Nothing -> pure No
    -- A 'No' for a condition or a contract only means that the refinements do
    -- not prove the formula. So negation moves down to the formula, also into
    -- a substitution, and the negation holds only when the refinements refute
    -- the formula. A missing path still makes the negation hold.
    evaluateWith substitutions (Not nested) = case nested of
        Not inner -> evaluateWith substitutions inner
        And guards -> evaluateWith substitutions $ Or $ map Not guards
        Or guards -> evaluateWith substitutions $ And $ map Not guards
        Satisfies target requirement
            | isJust (observedAt target) ->
                evaluateWith substitutions $ Satisfies target $ Formula.Not requirement
        Holds targets formula
            | all (isJust . observedAt) targets ->
                evaluateWith substitutions $ Holds targets $ Formula.Not formula
        Substitute additions inner
            | all (isJust . resolveSubstitutionWith observedAt freshValues ambiguousValues) additions ->
                evaluateWith substitutions $ Substitute additions $ Not inner
        _ -> negateVerdict <$> evaluateWith substitutions nested
    evaluateWith substitutions (And guards) =
        andVerdicts (map (evaluateWith substitutions) guards)
    evaluateWith substitutions (Or guards) =
        orVerdicts (map (evaluateWith substitutions) guards)

-- | Evaluate both the ECTA equality classes and liquid guard of a transition.
evaluateConstraint :: Entailment -> Constraint -> Term Symbol -> IO Verdict
evaluateConstraint entailment constraint term
    | equalitiesHold constraint term =
        evaluateGuard entailment (constraintGuard constraint) term
    | otherwise = pure No

{- | One position substitution with its actual-value assumption.

Keep solver bookkeeping lazy. Structural comparisons need only the literal
symbol mapping, so they must not inspect actual-term identity for solver names.
-}
data ResolvedSubstitution = ResolvedSubstitution
    { resolvedReplacement :: (Name, Formula.Term)
    , resolvedSymbolReplacement :: !(Symbol, Symbol)
    , resolvedActualAssumption :: Formula
    , resolvedDeclaration :: Maybe (Name, Name)
    , resolvedIdentityKnown :: Bool
    }

{- | Allocate distinct values for actual positions that share a name.

An unambiguous name retains its ambient meaning. Repeated positions share one
value. Distinct positions with the same name receive separate solver values.
-}
substitutionValues ::
    (Path -> Maybe Observed) ->
    (Path -> Path -> Maybe Bool) ->
    Guard ->
    (Map.Map Path (Name, Name), Set.Set Path)
substitutionValues observedAt sameAt guard =
    ( Map.fromList
        [ (target, binding)
        | actual@(target, _, _) <- actuals
        , Just binding <- [Map.lookup (representative actual) allocated]
        ]
    , ambiguous
    )
  where
    leafAt target = observedLeaf <$> observedAt target
    actuals =
        [ (target, Name name, refinement)
        | target <- Set.toAscList $ Set.fromList $ actualPaths guard
        , Just (Observed (RefinedSymbol (Symbol name) refinement) _) <- [observedAt target]
        ]
      where
        actualPaths (Substitute substitutions nested) =
            map substitutionActual substitutions <> actualPaths nested
        actualPaths (Not nested) = actualPaths nested
        actualPaths (And guards) = concatMap actualPaths guards
        actualPaths (Or guards) = concatMap actualPaths guards
        actualPaths _ = []
    representative (target, name, refinement) =
        case [ other
             | (other, otherName, otherRefinement) <- actuals
             , otherName == name
             , otherRefinement == refinement
             , sameAt target other == Just True
                || (leafAt target == Just Leaf && leafAt other == Just Leaf)
             ] of
            canonical : _ -> canonical
            [] -> target
    conflicts = [(target, name) | (target, name) <- values, names Map.! name > 1]
      where
        names = Map.fromListWith (+) [(name, 1 :: Int) | (_, name) <- values]

        values = nubOrd [(representative actual, name) | actual@(_, name, _) <- actuals]
    allocated = Map.fromList $ zipWith allocate conflicts available
      where
        allocate (target, original) fresh = (target, (fresh, original))

        available =
            filter (`Set.notMember` used) $
                [fromString $ "__cfta_actual_" <> show index | index <- [0 :: Integer ..]]

        used =
            Set.fromList $
                concat
                    [ Name name : Formula.freeNames refinement
                    | target <- Set.toList $ guardPaths guard
                    , Just (Observed (RefinedSymbol (Symbol name) refinement) _) <- [observedAt target]
                    ]
                    <> concatMap Formula.freeNames (requirements guard)

        requirements (Satisfies _ refinement) = [refinement]
        requirements (Holds _ formula) = [formula]
        requirements (Substitute _ nested) = requirements nested
        requirements (Not nested) = requirements nested
        requirements (And guards) = concatMap requirements guards
        requirements (Or guards) = concatMap requirements guards
        requirements _ = []
    ambiguous =
        Set.fromList
            [ target
            | (target, name, refinement) <- actuals
            , (other, otherName, otherRefinement) <- actuals
            , target /= other
            , name == otherName
            , refinement == otherRefinement
            , isNothing (sameAt target other)
            , leafAt target /= Just Leaf || leafAt other /= Just Leaf
            ]

-- | Resolve actual and formal positions within one simultaneous scope.
resolveSubstitutionWith ::
    (Path -> Maybe Observed) ->
    Map.Map Path (Name, Name) ->
    Set.Set Path ->
    Substitution ->
    Maybe ResolvedSubstitution
resolveSubstitutionWith observedAt freshValues ambiguousValues Substitution{substitutionActual, substitutionFormal} = do
    Observed (RefinedSymbol (Symbol actualName) actualRefinement) _ <- observedAt substitutionActual
    Observed (Symbol formalName) _ <- observedAt substitutionFormal
    let declaration = Map.lookup substitutionActual freshValues
        actualSymbol = maybe (Name actualName) fst declaration
        actualVariable = Formula.Var actualSymbol
    pure
        ResolvedSubstitution
            { resolvedReplacement = (Name formalName, actualVariable)
            , resolvedSymbolReplacement = (Symbol formalName, Symbol actualName)
            , resolvedActualAssumption =
                Formula.substitute [(refinementValueName, actualVariable)] actualRefinement
            , resolvedDeclaration = declaration
            , resolvedIdentityKnown = Set.notMember substitutionActual ambiguousValues
            }

-- | The name 'valueName', the value variable of every refinement.
refinementValueName :: Name
refinementValueName = fromString valueName

-- | Apply simultaneous scopes from the innermost scope to the outermost.
applySubstitutions :: [[ResolvedSubstitution]] -> Formula -> Formula
applySubstitutions scopes refinement =
    foldl apply refinement scopes
  where
    apply predicate scope =
        Formula.substitute (map resolvedReplacement scope) predicate

{- | Apply scoped symbol substitutions to one structural comparison operand.

Each scope renames symbols simultaneously, including free names in refinement
annotations. Constructor children stay in place: a name substitution does not
splice in the actual subtree. Solver-generated value identities are not
symbols in the structural alphabet.
The first non-identity mapping for a repeated formal name takes precedence,
matching refinement substitution.
-}
substituteTerm :: [[ResolvedSubstitution]] -> Term Symbol -> Term Symbol
substituteTerm scopes = fmap $ \(RefinedSymbol symbol refinement) ->
    let (renamed, annotation) = substituteObservation scopes (symbol, refinement)
     in RefinedSymbol renamed annotation

-- | Apply structural name substitutions to one finite root observation.
substituteObservation :: [[ResolvedSubstitution]] -> (Symbol, Formula) -> (Symbol, Formula)
substituteObservation scopes observation = foldl apply observation scopes
  where
    apply (symbol, refinement) scope =
        ( Map.findWithDefault symbol symbol replacements
        , Formula.substitute refinementReplacements refinement
        )
      where
        replacements =
            Map.fromList $ reverse $ filter (uncurry (/=)) $ map resolvedSymbolReplacement scope
        refinementReplacements =
            [ (Name formal, Formula.Var $ Name actual)
            | (Symbol formal, Symbol actual) <- Map.toList replacements
            ]

{- | Add the instantiated refinement of every actual argument to an entailment
antecedent.

Substitution changes a formal name to the actual term's symbol. This assumption
connects that symbol back to the refinement carried by the actual subtree, so
dependent results compose through non-leaf nodes as well as named pool entries.
Actual terms belong to the surrounding environment. Guard substitutions do not
rename their value identities or their refinement assumptions.
-}
withActualAssumptions :: [[ResolvedSubstitution]] -> Formula -> Formula
withActualAssumptions scopes predicate =
    Formula.conjunction $
        map resolvedActualAssumption (concat scopes)
            <> [predicate]
