{-# LANGUAGE OverloadedStrings #-}

{- | Check the refinement compiler against the explicit check of every candidate.

'LTAGen.validOutcomes' lists every candidate that the recipe describes and
checks its guards one by one, which is the definition of the language.
Random generators of integers are compiled and must give the same multiset
of values. The leaves are pools, and the nodes are choices and conditions.
Both sides decide the queries with 'latticeEntailment'. The description
alone also gives the values, and 'LTAGen.validOutcomes' must agree with them.

A liquid automaton imported without a depth bound is compiled and compared
with "Data.CFTA.Simple": a recursive result by its count at each size, the
number of term nodes, and a finite one by its terms.
-}
module Data.CFTA.Gen.Refinement.OracleSpec (spec) where

import Control.Monad (forM, when)
import Data.CFTA.Index (Depth (..), Rank (..), everyRank)
import Data.Either (isRight)
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.List (sort)
import qualified Data.Tree as Tree
import Test.Hspec (Spec, describe, it)
import Test.QuickCheck (
    Gen,
    Property,
    chooseInt,
    counterexample,
    discard,
    elements,
    forAllShow,
    ioProperty,
    oneof,
    property,
    sized,
    sublistOf,
    suchThat,
    vectorOf,
    (.&&.),
    (===),
 )

import Data.CFTA (Transition (Transition), mkFTA)
import Data.CFTA.Constraint (Guard (..), Substitution (..), contractTermName, noConstraint, semanticConstraint)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Gen.Refinement.TestSupport (values)
import Data.CFTA.Interned (fromFTA)
import Data.CFTA.Path (path)
import Data.CFTA.Refinement (
    Automaton,
    Symbol (RefinedSymbol),
    Verdict (..),
    evaluateConstraint,
    explicitView,
    validate,
 )
import Data.CFTA.Refinement.Expression (
    literal,
    refinementFormula,
    variable,
    (.&&),
    (.<),
    (.<=),
    (.==),
    (.>=),
 )
import Data.CFTA.Refinement.Lattice (latticeEntailment)
import qualified Data.CFTA.Simple as Simple

spec :: Spec
spec = describe "the refinement compiler against validOutcomes" $ do
    -- validOutcomes checks every candidate, so the language must stay small.
    it "gives the values of the candidates that pass every guard"
        $ property
        $ forAllShow
            ( sized (\size -> generator (min 3 (1 + size `div` 25)))
                `suchThat` (\(_, modelled, _) -> length (take 201 modelled) <= 200)
            )
            (\(description, _, _) -> description)
        $ \(description, modelled, generator') -> ioProperty $ do
            agreed <- agreesWithOracle description generator'
            -- The definition of the language agrees with the values of the description.
            checked <- LTAGen.validOutcomes latticeEntailment generator'
            pure $
                agreed .&&. case checked of
                    Right expected -> sort expected === sort modelled
                    Left err -> counterexample (show err) $ null modelled

    it "gives the terms of an imported liquid automaton that pass every guard"
        $ property
        $ forAllShow
            ((,,) <$> liquidAutomaton <*> (Depth <$> chooseInt (1, 3)) <*> elements [Nothing, Just (1 :: Integer), Just 3])
            (\((described, _), depth, condition) -> show (described, depth, condition))
        $ \((described, automaton), depth, condition) ->
            ioProperty
                $ agreesWithOracle described
                $ maybe id (\bound imported -> imported `LTAGen.satisfying` (.>= literal bound)) condition
                $ LTAGen.fromAutomatonUpToDepth depth automaton

    it "gives the terms of an unbounded liquid import that the simple definition accepts" $
        property $
            forAllShow (liquidAutomaton `suchThat` (isRight . validate . snd)) fst $ \(_, automaton) -> ioProperty $ do
                compiled <- LTAGen.compileWith latticeEntailment (LTAGen.fromAutomaton automaton)
                expected <- simpleTerms automaton
                pure $ case (compiled, expected) of
                    (_, Nothing) -> discard
                    -- A recursive import cannot count a constrained or an ambiguous automaton.
                    (Left LTAGen.CannotCountConstrainedEdges, _) -> property True
                    (Left LTAGen.AmbiguousAutomaton, _) -> property True
                    -- Compile decides a guard from observations, and a substitution of a node may need the complete term.
                    (Left (LTAGen.ResidualGuard _), _) -> property True
                    (Left err, _) -> counterexample (show err) False
                    (Right generated, Just (bySize, shallow)) -> case LTAGen.cardinality generated of
                        -- Pruning can remove every cycle, and then the generator is finite.
                        Right _ -> sort (values generated) === sort shallow
                        Left LTAGen.EmptyGenerator -> (shallow, concat bySize) === ([], [])
                        -- A generator built at construction is returned unchanged, so its queries refuse.
                        Left LTAGen.AmbiguousAutomaton -> property True
                        Left LTAGen.CannotCountConstrainedEdges -> property True
                        Left LTAGen.UnboundedGenerator ->
                            [LTAGen.countAtSize generated size | size <- [1 .. 4]]
                                === [Right (toEnum (length terms)) | terms <- bySize]
                        Left err -> counterexample (show err) False

{- | The terms of a liquid automaton that "Data.CFTA.Simple" accepts, by node
count from one to four, and up to depth three. 'Nothing' when the lattice
cannot decide a guard.
-}
simpleTerms :: Automaton -> IO (Maybe ([[Tree.Tree Symbol]], [Tree.Tree Symbol]))
simpleTerms automaton = do
    undecided <- newIORef False
    let explicit = either (error . show) id $ explicitView automaton
        decide constraint term = do
            verdict <- evaluateConstraint latticeEntailment constraint term
            when (verdict == Unknown) $ writeIORef undecided True
            pure $ verdict == Yes
    bySize <- forM [1 .. 4] $ \size ->
        filter ((== size) . length . Tree.flatten) <$> Simple.termsUpToM decide (Depth (size - 1)) explicit
    shallow <- Simple.termsUpToM decide 3 explicit
    unknown <- readIORef undecided
    pure $ if unknown then Nothing else Just (bySize, shallow)

-- | Compile a generator and list its values beside the values of 'LTAGen.validOutcomes'.
agreesWithOracle :: (Ord a, Show a) => String -> LTAGen.LTAGen a -> IO Property
agreesWithOracle description generator' = do
    compiled <- LTAGen.compileWith latticeEntailment generator'
    checked <- LTAGen.validOutcomes latticeEntailment generator'
    pure $ counterexample description $ case (compiled, checked) of
        (Right generated, Right expected) ->
            sort (values generated) === sort expected
                -- Every shrink candidate is a member with a smaller rank.
                .&&. [ (rank, candidates)
                     | rank <- ranks generated
                     , let candidates = LTAGen.shrinkRank generated rank
                     , any (\candidate -> candidate < 0 || candidate >= rank) candidates
                     ]
                    === []
        (Left err, Left other) -> counterexample (show (err, other)) True
        -- validOutcomes reports an empty language as an error.
        (Right generated, Left LTAGen.EmptyGenerator) -> values generated === []
        -- Compile decides a guard from grouped observations, and cannot compare complete subtrees.
        (Left (LTAGen.RelationalSyntacticEqualityUnsupported _), Right _) -> property True
        _ -> counterexample (show (fmap values compiled, checked)) False

-- | A random liquid automaton of at most three states with integer leaves and guarded pairs.
liquidAutomaton :: Gen (String, Automaton)
liquidAutomaton = do
    count <- chooseInt (1, 3)
    rows <- forM [0 .. count - 1] $ \state -> do
        width <- chooseInt (1, 3)
        (,) state <$> vectorOf width (transition count)
    let explicit = either (error . show) id $ mkFTA (0 :: Int) rows
    pure (show explicit, fromFTA explicit)
  where
    transition count =
        oneof
            [ do
                value <- chooseInt (0, 3)
                pure $ Transition (RefinedSymbol "n" $ refinementFormula (.== literal (toInteger value))) [] noConstraint
            , do
                children <- vectorOf 2 (chooseInt (0, count - 1))
                guard <-
                    elements
                        [ Top
                        , Satisfies (path [0]) (refinementFormula (.>= 1))
                        , Holds [path [0], path [1]] (variable (contractTermName 0) .< variable (contractTermName 1))
                        , Same (path [0]) (path [1])
                        , Not (Satisfies (path [1]) (refinementFormula (.<= 1)))
                        , Bottom
                        , Substitute [Substitution (path [1]) (path [0])] (Satisfies (path [0]) (refinementFormula (.>= 1)))
                        , Substitute
                            [Substitution (path [0]) (path [1]), Substitution (path [1]) (path [0])]
                            (Holds [path [0], path [1]] (variable (contractTermName 0) .< variable (contractTermName 1)))
                        , Not (Substitute [Substitution (path [0]) (path [1])] (Satisfies (path [1]) (refinementFormula (.<= 1))))
                        ]
                refinement <-
                    elements
                        [ refinementFormula (\v -> 0 .<= v .&& v .<= 5)
                        , refinementFormula (\v -> 1 .<= v .&& v .<= 3)
                        , refinementFormula (.== 2)
                        ]
                pure $ Transition (RefinedSymbol "pair" refinement) children (semanticConstraint guard)
            ]

{- | A random generator of integers with a description and its values, nested
to the given depth. The values follow from the description alone.
-}
generator :: Int -> Gen (String, [Integer], LTAGen.LTAGen Integer)
generator depth
    | depth <= 0 = leaf
    | otherwise =
        oneof
            [ leaf
            , do
                (leftName, leftValues, left) <- generator (depth - 1)
                (rightName, rightValues, right) <- generator (depth - 1)
                weights <- elements [Nothing, Just (1, 3), Just (2, 1)]
                pure $ case weights of
                    Nothing -> ("oneof [" <> leftName <> ", " <> rightName <> "]", leftValues <> rightValues, LTAGen.oneof [left, right])
                    Just (leftWeight, rightWeight) ->
                        ( "frequency [" <> show (leftWeight, leftName) <> ", " <> show (rightWeight, rightName) <> "]"
                        , leftValues <> rightValues
                        , LTAGen.frequency [(leftWeight, left), (rightWeight, right)]
                        )
            , do
                (name, childValues, child) <- generator (depth - 1)
                bound <- toInteger <$> chooseInt (0, 3)
                pure
                    ( "(" <> name <> ") satisfying (>= " <> show bound <> ")"
                    , filter (>= bound) childValues
                    , child `LTAGen.satisfying` (.>= literal bound)
                    )
            ]
  where
    leaf = do
        members <- map toInteger <$> sublistOf [0 .. 3 :: Int]
        pure ("elements " <> show members, members, LTAGen.elements members)

-- | Every rank of a finite generator.
ranks :: LTAGen.LTAGen a -> [Rank]
ranks compiled = either (const []) everyRank $ LTAGen.cardinality compiled
