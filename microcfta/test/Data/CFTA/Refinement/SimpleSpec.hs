{-# LANGUAGE OverloadedStrings #-}

{- | Check the liquid tree automata against "Data.CFTA.Simple".

The automata are random explicit automata over at most three states. Leaves
carry exact or bounded integer refinements, and unary and binary nodes carry
guards built from conditions, contracts, entailment, 'Same', 'Bottom',
substitutions, and the connectives. Every refinement is bounded, so
'latticeEntailment' decides the queries without a solver. The simple
definition decides each constraint by brute force over the integers of each
refinement, without the evaluator of the library. A case where the library
answers 'Unknown' is discarded. The same automata check the structural
promises of 'minimize', and that 'reduce' adds no term when only equal
transitions are similar.
-}
module Data.CFTA.Refinement.SimpleSpec (spec) where

import Control.Monad (forM)
import Data.Either (isLeft)
import Data.Functor.Identity (Identity (..))
import Data.List (sort)
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Tree as Tree
import Test.Hspec (Spec, describe, it)
import Test.QuickCheck (
    Gen,
    chooseInt,
    counterexample,
    discard,
    elements,
    forAll,
    frequency,
    ioProperty,
    oneof,
    property,
    suchThat,
    vectorOf,
    (.&&.),
    (===),
 )

import Data.CFTA (FTA, Transition (Transition), mapConstraints, mkFTA)
import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (
    Constraint (constraintGuard),
    Guard (..),
    contractTermName,
    equalitiesHold,
    noConstraint,
    semanticConstraint,
 )
import Data.CFTA.Path (getPath, path)
import Data.CFTA.Refinement (
    PruneError (PruneUnknown),
    ReductionError (ReductionPrune, ReductionSimilarity),
    SimilarityError (SimilarityUnknown),
    Substitution (..),
    Symbol (RefinedSymbol),
    Verdict (..),
    accepts,
    denotationAtMost,
    edgeChildren,
    explicitView,
    fromFTA,
    minimize,
    prune,
    reduce,
    refinementSubtypingOn,
    similarity,
    similarityPairs,
    validate,
 )
import Data.CFTA.Refinement.Expression (literal, refinementFormula, variable, (.&&), (.<), (.<=), (.==), (.>=))
import Data.CFTA.Refinement.Lattice (latticeEntailment)
import qualified Data.CFTA.Simple as Simple
import Data.CFTA.Symbol (Formula)
import qualified Language.Fixpoint.Types as Fixpoint

spec :: Spec
spec = describe "liquid tree automata against Data.CFTA.Simple" $ do
    it "recognize the terms that the simple definition accepts" $
        property $
            forAll automaton $ \explicit -> ioProperty $ do
                let node = fromFTA explicit
                actual <- forM (candidates explicit) $ \term -> (term,) <$> accepts latticeEntailment node term
                let expected = [(term, if simpleAccepts explicit term then Yes else No) | (term, _) <- actual]
                -- A substitution whose actual value is ambiguous gives 'Unknown'.
                pure $ if any ((== Unknown) . snd) actual then discard else expected === actual

    it "denote the terms that the simple definition lists up to each depth, also after pruning" $
        property $
            forAll automaton $ \explicit -> ioProperty $ do
                let node = fromFTA explicit
                pruned <- prune latticeEntailment node
                checks <- forM [0 .. 3] $ \depth -> do
                    denoted <- denotationAtMost latticeEntailment depth node
                    afterPruning <- traverse (denotationAtMost latticeEntailment depth) pruned
                    pure (Simple.termsUpToM (\constraint -> Identity . holds constraint) depth explicit, denoted, afterPruning)
                -- Denotation and pruning may stop at a query that the lattice cannot decide, and at nothing else.
                pure $ case pruned of
                    Left (PruneUnknown _) -> discard
                    _
                        | any (\(_, denoted, afterPruning) -> isLeft denoted || either (const False) isLeft afterPruning) checks -> discard
                        | otherwise ->
                            counterexample (show checks) $
                                and
                                    [ fmap sort denoted == Right expected && fmap (fmap sort) afterPruning == Right (Right expected)
                                    | (Identity expected, denoted, afterPruning) <- checks
                                    ]

    it "minimize to a valid, productive automaton with a finite term and only original labels" $
        property $
            forAll automaton $ \explicit -> ioProperty $ do
                let node = fromFTA explicit
                inferred <- similarity (refinementSubtypingOn latticeEntailment (Just . length . edgeChildren)) node
                pure $ case inferred of
                    Left _ -> discard
                    Right related -> case minimize node related of
                        Left err -> counterexample ("minimize failed: " <> show err) False
                        Right minimized ->
                            let view = either (error . show) id $ explicitView minimized
                                original = either (error . show) id $ explicitView node
                                erased = mapConstraints (const noConstraint) view
                                trimmed = FTA.trim erased
                                count fta = sum [length (FTA.transitionsFrom fta state) | state <- FTA.states fta]
                                nonEmpty fta = not $ null $ FTA.transitionsFrom fta $ FTA.initialState fta
                                labels fta = [(symbol, constraint) | state <- FTA.states fta, FTA.Transition symbol _ constraint <- FTA.transitionsFrom fta state]
                             in counterexample (show (similarityPairs related, view)) $
                                    (validate minimized === Right ())
                                        .&&. (nonEmpty (FTA.trim (mapConstraints (const noConstraint) original)) === nonEmpty trimmed)
                                        .&&. (count trimmed === count erased)
                                        .&&. property (all (`elem` labels original) (labels view))

    it "reduce to an automaton whose terms the input accepts, when only equal transitions are similar" $
        property $
            forAll automaton $ \explicit -> ioProperty $ do
                -- A transition is similar only to itself, so no step may add a term.
                reduced <- reduce latticeEntailment (refinementSubtypingOn latticeEntailment Just) (fromFTA explicit)
                case reduced of
                    -- Pruning and similarity may stop at a query that the lattice cannot decide.
                    Left (ReductionPrune (PruneUnknown _)) -> pure discard
                    Left (ReductionSimilarity (SimilarityUnknown _ _)) -> pure discard
                    Left err -> pure $ counterexample ("reduce failed: " <> show err) False
                    Right result -> do
                        denoted <- denotationAtMost latticeEntailment 3 result
                        pure $ case denoted of
                            Left _ -> discard
                            Right terms ->
                                let added = filter (not . simpleAccepts explicit) terms
                                 in counterexample (show (result, added)) $ null added

simpleAccepts :: FTA Int Symbol Constraint -> Tree.Tree Symbol -> Bool
simpleAccepts explicit = runIdentity . Simple.acceptsM (\constraint -> Identity . holds constraint) explicit

{- | Decide a constraint on a complete term by brute force. Every refinement
in these automata is a set of integers in 'domain', so each atom is a finite
check over these sets. The rules are those of 'Guard': an atom with a missing
path fails, and a negated condition or contract holds when the refinements
refute the formula. No formula names a constructor, so a substitution only
needs its two paths.
-}
holds :: Constraint -> Tree.Tree Symbol -> Bool
holds constraint term = equalitiesHold constraint term && decide (constraintGuard constraint)
  where
    decide guard = case guard of
        Top -> True
        Bottom -> False
        Same left right -> isJust (at left) && at left == at right
        Entails antecedent consequent -> case (values antecedent, values consequent) of
            (Just left, Just right) -> all (`elem` right) left
            _ -> False
        Satisfies target formula -> maybe False (all (\value -> truth [(valueName, value)] formula)) (values target)
        Holds targets formula -> maybe False (all (contract formula) . sequence) (traverse values targets)
        Substitute substitutions nested -> resolved substitutions && decide nested
        And guards -> all decide guards
        Or guards -> any decide guards
        Not nested -> case nested of
            Not inner -> decide inner
            And guards -> decide $ Or $ map Not guards
            Or guards -> decide $ And $ map Not guards
            Satisfies target formula
                | Just set <- values target -> not $ any (\value -> truth [(valueName, value)] formula) set
            Holds targets formula
                | Just sets <- traverse values targets -> not $ any (contract formula) (sequence sets)
            Substitute substitutions inner
                | resolved substitutions -> decide $ Substitute substitutions $ Not inner
            _ -> not $ decide nested
    at target = getPath target term
    values target = do
        Tree.Node (RefinedSymbol _ refinement) _ <- at target
        pure [value | value <- domain, truth [(valueName, value)] refinement]
    contract formula assignment = truth (zip (map contractTermName [0 ..]) assignment) formula
    resolved = all (\(Substitution actual formal) -> isJust (at actual) && isJust (at formal))

-- | The name of the value in a refinement formula.
valueName :: String
valueName = "v"

-- | Every integer that a refinement of the generated automata can hold.
domain :: [Integer]
domain = [-1 .. 6]

-- | The truth of a comparison formula, with the value of each variable.
truth :: [(String, Integer)] -> Formula -> Bool
truth bindings formula = case formula of
    Fixpoint.PAnd parts -> all (truth bindings) parts
    Fixpoint.POr parts -> any (truth bindings) parts
    Fixpoint.PNot inner -> not $ truth bindings inner
    Fixpoint.PAtom relation left right -> compareBy relation (valueOf left) (valueOf right)
    _ -> error $ "an unexpected formula: " <> show formula
  where
    valueOf (Fixpoint.ECon (Fixpoint.I number)) = number
    valueOf (Fixpoint.EVar name) = fromMaybe (error $ "an unbound variable: " <> show name) $ lookup (Fixpoint.symbolString name) bindings
    valueOf other = error $ "an unexpected expression: " <> show other
    compareBy relation = case relation of
        Fixpoint.Eq -> (==)
        Fixpoint.Ne -> (/=)
        Fixpoint.Lt -> (<)
        Fixpoint.Le -> (<=)
        Fixpoint.Gt -> (>)
        Fixpoint.Ge -> (>=)
        _ -> error $ "an unexpected relation: " <> show relation

{- | A random liquid automaton: at most three states, integer leaves, and
guarded nodes. The root has nodes more often. An automaton whose guard reads
a recursive position is left out, as 'validate' rejects it.
-}
automaton :: Gen (FTA Int Symbol Constraint)
automaton = (`suchThat` (either (const False) (const True) . validate . fromFTA)) $ do
    count <- chooseInt (1, 3)
    rows <- forM [0 .. count - 1] $ \state -> do
        width <- chooseInt (1, 3)
        (,) state
            <$> vectorOf width (if state == 0 then frequency [(1, leaf), (2, node count)] else frequency [(3, leaf), (1, node count)])
    pure $ either (error . show) id $ mkFTA 0 rows
  where
    node count = oneof [unary count, binary count]
    unary count = do
        child <- chooseInt (0, count - 1)
        guard <- elements unaryGuards
        pure $ Transition (RefinedSymbol "wrap" bounded) [child] (semanticConstraint guard)
    binary count = do
        children <- vectorOf 2 (chooseInt (0, count - 1))
        guard <- binaryGuard
        pure $ Transition (RefinedSymbol "pair" bounded) children (semanticConstraint guard)
    leaf =
        oneof
            [ do
                value <- chooseInt (0, 3)
                pure $ Transition (RefinedSymbol "n" $ refinementFormula (.== literal (toInteger value))) [] noConstraint
            , do
                low <- chooseInt (0, 2)
                high <- chooseInt (low, 3)
                pure $
                    Transition
                        (RefinedSymbol "r" $ refinementFormula (\v -> literal (toInteger low) .<= v .&& v .<= literal (toInteger high)))
                        []
                        noConstraint
            ]
    bounded = refinementFormula (\v -> 0 .<= v .&& v .<= 5)
    unaryGuards =
        [ Top
        , Satisfies (path [0]) (refinementFormula (.>= 1))
        , Not (Satisfies (path [0]) (refinementFormula (.<= 1)))
        , Satisfies (path [0, 0]) (refinementFormula (.== 0))
        ]
    binaryAtoms =
        [ Satisfies (path [0]) (refinementFormula (.>= 1))
        , Satisfies (path [1]) (refinementFormula (.<= 2))
        , Holds [path [0], path [1]] (variable (contractTermName 0) .< variable (contractTermName 1))
        , Entails (path [0]) (path [1])
        , Same (path [0]) (path [1])
        ]
    binaryGuard =
        oneof
            [ elements (Top : binaryAtoms)
            , Not <$> elements binaryAtoms
            , (\left right -> And [left, right]) <$> elements binaryAtoms <*> elements binaryAtoms
            , (\left right -> Or [left, right]) <$> elements binaryAtoms <*> elements binaryAtoms
            , pure Bottom
            , Substitute
                <$> elements
                    [ [Substitution (path [0]) (path [1])]
                    , [Substitution (path [1]) (path [0])]
                    , [Substitution (path [0]) (path [1]), Substitution (path [1]) (path [0])]
                    ]
                <*> elements binaryAtoms
            , (\atom -> Not (Substitute [Substitution (path [1]) (path [0])] atom)) <$> elements binaryAtoms
            ]

-- | The trees of the underlying graph up to depth two, to test recognition on.
candidates :: FTA Int Symbol Constraint -> [Tree.Tree Symbol]
candidates = fromMaybe [] . Simple.termsUpTo 2 . mapConstraints (const noConstraint)
