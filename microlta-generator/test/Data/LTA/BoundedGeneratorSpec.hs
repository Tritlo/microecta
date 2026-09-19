{-# LANGUAGE TypeApplications #-}

module Data.LTA.BoundedGeneratorSpec (spec) where

import Control.Monad (forM_, void)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.List (nub, sort)
import Data.Proxy (Proxy (Proxy))
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Data.Typeable (typeRep)
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import Text.Read (readMaybe)

import qualified Data.CFTA.Generic as Datatype
import qualified Data.ECTA as ECTA
import Data.ECTA.Paths (mkEqConstraints)
import Data.LTA (
    Automaton,
    Entailment (Entailment),
    EnumerationError,
    Guard (Bottom, Not, Or, Same, Satisfies, Substitute, Top),
    LiquidConstraint,
    LiquidSymbol (LiquidSymbol),
    PruneError (ResidualLTAConstraint),
    State (State),
    Substitution (Substitution),
    Transition,
    Verdict (Unknown, Yes),
    accepts,
    automatonStates,
    denotationAtMost,
    equalityConstraint,
    mkAutomaton,
    path,
    semanticConstraint,
    unconstrainedConstraint,
    pattern Transition,
 )
import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.LiquidFixpoint (withZ3)
import Data.LTA.Refinement (integer, true, (.==.), (.>.))
import qualified Data.LTA.Refinement as Refinement
import qualified Language.Fixpoint.Types as Fixpoint

-- | Fail if an unconstrained fixture unexpectedly calls the solver.
unusedEntailment :: Entailment
unusedEntailment = Entailment $ \_ _ -> fail "unexpected solver call"

-- | Build a checked fixture from transition rows.
automatonFrom :: [(State, [Transition])] -> IO Automaton
automatonFrom = either (fail . show) pure . mkAutomaton (State 0)

-- | Compile a bounded language or report the compiler error.
compileBounded :: Entailment -> Int -> Automaton -> IO (LTA.Compiled (Tree.Tree LiquidSymbol))
compileBounded solver depth automaton =
    LTA.compileAutomatonUpToDepth solver depth automaton >>= either (fail . show) pure

-- | Read the complete accepted language in replay order.
termsOf :: LTA.Compiled a -> [Tree.Tree LiquidSymbol]
termsOf compiled =
    [ LTA.generatedTerm generated
    | rank <- [0 .. LTA.cardinality compiled - 1]
    , Right generated <- [LTA.unrank compiled rank]
    ]

-- | Count all tree nodes with no machine-integer bound.
nodeCount :: Tree.Tree LiquidSymbol -> Integer
nodeCount = Tree.foldTree $ \_ counts -> 1 + sum counts

-- | Check shrink membership, strict decrease, and finite reachability.
checkShrinks :: Entailment -> Automaton -> LTA.Compiled a -> IO ()
checkShrinks solver automaton compiled =
    forM_ [0 .. LTA.cardinality compiled - 1] $ \rank -> do
        source <- either (fail . show) pure $ LTA.unrank compiled rank
        let targets = LTA.shrinkRank compiled rank
        targets `shouldBe` nub targets
        forM_ targets $ \target -> do
            generated <- either (fail . show) pure $ LTA.unrank compiled target
            accepts solver automaton (LTA.generatedTerm generated) >>= (`shouldBe` Yes)
            nodeCount (LTA.generatedTerm generated)
                `shouldSatisfy` (< nodeCount (LTA.generatedTerm source))
        toInteger (length $ LTA.smallerMembers compiled rank)
            `shouldSatisfy` (< LTA.cardinality compiled)

-- | Recursive lists with two distinct atoms.
recursiveLists :: IO Automaton
recursiveLists =
    automatonFrom
        [ (State 0, [plain "nil" [], plain "cons" [State 1, State 0]])
        , (State 1, [plain "a" [], plain "b" []])
        ]
  where
    plain symbol children = Transition symbol true children unconstrainedConstraint

-- | Independent pairs with two leaves and one compound alternative.
pairsWith :: LiquidConstraint -> IO Automaton
pairsWith constraint =
    automatonFrom
        [ (State 0, [Transition "pair" true [State 1, State 1] constraint])
        , (State 1, [plain "a" [], plain "b" [], plain "wrap" [State 2]])
        , (State 2, [plain "a" []])
        ]
  where
    plain symbol children = Transition symbol true children unconstrainedConstraint

-- | Two boxed list languages with a shared finite graph and a nested guard.
largeBoxedLists :: LiquidConstraint -> IO Automaton
largeBoxedLists constraint =
    automatonFrom $
        [ (State 0, [Transition "pair" true [State 1, State 1] constraint])
        , (State 1, [plain "box" [State 71]])
        , (State 2, [plain "nil" []])
        , (State 72, [plain "a" [], plain "b" []])
        ]
            <> [(State level, [plain "nil" [], plain "cons" [State 72, State $ level - 1]]) | level <- [3 .. 71]]
  where
    plain symbol children = Transition symbol true children unconstrainedConstraint

-- | Three terms with two runs that accept the same wrapped leaf.
ambiguousTerms :: IO Automaton
ambiguousTerms =
    automatonFrom
        [ (State 0, [plain "a" [], plain "wrap" [State 1], plain "wrap" [State 2]])
        , (State 1, [plain "a" [], plain "b" []])
        , (State 2, [plain "a" []])
        ]
  where
    plain symbol children = Transition symbol true children unconstrainedConstraint

-- | One term with a shared graph and more than 2^70 tree nodes.
sharedBinaryTerm :: LiquidConstraint -> IO Automaton
sharedBinaryTerm constraint =
    automatonFrom $
        [ (State 0, [Transition "root" true [state 70, state 70] constraint])
        , (state 0, [plain "a" []])
        ]
            <> [(state level, [plain "fork" [state (level - 1), state (level - 1)]]) | level <- [1 .. 70]]
  where
    state level = State $ level + 1
    plain symbol children = Transition symbol true children unconstrainedConstraint

-- | Force the retained support graph without inspecting generated values.
supportNodes :: LTA.Compiled a -> Int
supportNodes compiled = case LTA.compiledSupport compiled of
    LTA.EqualitySupport automaton -> Set.size $ automatonStates automaton
    LTA.SymbolicSupport automaton -> Set.size $ automatonStates automaton
    LTA.RelationalSupport support -> ECTA.nodeCount support

spec :: Spec
spec = do
    describe "liquid annotations on a derived datatype" $ do
        it "keeps the datatype codec and shrinks within the guarded language" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver -> do
                datatype <- either (fail . show) pure $ Datatype.deriveFTAWith @(Maybe (Int, Int)) $ Datatype.domain @Int [0, 1, 2]
                let annotate constructor
                        | Datatype.constructorType constructor == typeRep (Proxy @Int) =
                            ( maybe true (\literal -> Refinement.value .==. integer literal) $ readMaybe $ Datatype.constructorName constructor
                            , unconstrainedConstraint
                            )
                        | Datatype.constructorName constructor == "(,)" =
                            (true, semanticConstraint $ Satisfies (path [1]) (Refinement.value .>. integer 0))
                        | otherwise = (true, unconstrainedConstraint)
                    source = LTA.fromDatatypeUpToDepth 2 $ Datatype.annotateDatatype annotate datatype
                    expected = Nothing : [Just (numerator, denominator) | numerator <- [0, 1, 2], denominator <- [1, 2]]
                compiled <- LTA.compile solver source >>= either (fail . show) pure
                LTA.cardinality compiled `shouldBe` 7
                members <- traverse (either (fail . show) pure . (LTA.unrank compiled)) [0 .. 6]
                sort (map LTA.generatedValue members) `shouldBe` expected
                forM_ [0 .. 6] $ \rank -> do
                    generated <- either (fail . show) pure $ LTA.unrank compiled rank
                    forM_ (LTA.shrinkRank compiled rank) $ \target -> do
                        smaller <- either (fail . show) pure $ LTA.unrank compiled target
                        LTA.generatedValue smaller `shouldSatisfy` (`elem` expected)
                        nodeCount (LTA.generatedTerm smaller) `shouldSatisfy` (< nodeCount (LTA.generatedTerm generated))

    describe "bounded LTA sources in ordinary generators" $ do
        it "defers support inspection and preserves the bounded term language" $ do
            recursive <- recursiveLists
            ambiguous <- ambiguousTerms
            boolean <- pairsWith $ semanticConstraint $ Not same
            forM_ [(2, recursive), (1, ambiguous), (2, boolean)] $ \(depth, automaton) -> do
                let source = LTA.fromLTA depth automaton
                void (LTA.support source) `shouldBe` Left LTA.SourceRequiresCompilation
                compiled <- LTA.compile unusedEntailment source >>= either (fail . show) pure
                baseline <- compileBounded unusedEntailment depth automaton
                LTA.cardinality compiled `shouldBe` LTA.cardinality baseline
                termsOf compiled `shouldBe` termsOf baseline
                denotationAtMost unusedEntailment depth automaton `shouldDenote` (termsOf compiled)
                forM_ [0 .. LTA.cardinality compiled - 1] $ \rank -> do
                    generated <- either (fail . show) pure $ LTA.unrank compiled rank
                    LTA.generatedValue generated `shouldBe` LTA.generatedTerm generated

        it "keeps unique imported terms and repeated pool draws with their weights" $ do
            automaton <- ambiguousTerms
            imported <- compileBounded unusedEntailment 1 automaton
            weighted <-
                either (fail . show) pure $
                    LTA.frequency
                        [ (2, LTA.pool [LTA.refined (7 :: Int) "draw" true, LTA.refined 7 "draw" true])
                        , (5, LTA.leaf 7 "other" true)
                        ]
            let source = fmap (const (7 :: Int)) $ LTA.fromLTA 1 automaton
                generator =
                    LTA.node "combined" unconstrainedConstraint $
                        (,) <$> LTA.children source <*> LTA.children weighted
            compiled <- LTA.compile unusedEntailment generator >>= either (fail . show) pure
            members <- traverse (either (fail . show) pure . (LTA.unrank compiled)) [0 .. 8]
            LTA.cardinality compiled `shouldBe` 9
            map LTA.generatedValue members `shouldBe` replicate 9 (7, 7)
            map LTA.generatedWeight members `shouldBe` concat (replicate 3 [2, 2, 5])
            termsOf compiled
                `shouldBe` [ Tree.Node (LiquidSymbol "combined" true) [term, Tree.Node (LiquidSymbol symbol true) []]
                           | term <- termsOf imported
                           , symbol <- ["draw", "draw", "other"]
                           ]
            length (nub $ termsOf compiled) `shouldBe` 6

        it "retains an ordinary alternative when an imported bound is empty" $ do
            empty <- automatonFrom [(State 0, [])]
            recursive <- recursiveLists
            forM_ [LTA.fromLTA 0 empty, LTA.fromLTA (-1) recursive] $ \source -> do
                emptyResult <- LTA.compile unusedEntailment source
                fmap LTA.cardinality emptyResult `shouldBe` Left LTA.EmptyGenerator
                alternatives <-
                    either (fail . show) pure $
                        LTA.oneof [fmap (const (7 :: Int)) source, LTA.leaf 9 "ordinary" true]
                compiled <- LTA.compile unusedEntailment alternatives >>= either (fail . show) pure
                LTA.cardinality compiled `shouldBe` 1
                fmap LTA.generatedValue (LTA.unrank compiled 0) `shouldBe` Right 9

        it "skips a rejected deferred import before compiling its source" $ do
            automaton <- ambiguousTerms
            let rejected =
                    LTA.node "dead" Bottom
                        $ fmap (const (7 :: Int))
                        $ LTA.fromLTA 1 automaton
            alternatives <-
                either (fail . show) pure $
                    LTA.frequency
                        [ (3, LTA.leaf 9 "ordinary" true)
                        , (11, rejected)
                        , (5, LTA.leaf 8 "later" true)
                        ]
            compiled <-
                LTA.compile unusedEntailment alternatives
                    >>= either (fail . show) pure
            members <- traverse (either (fail . show) pure . (LTA.unrank compiled)) [0, 1]
            LTA.cardinality compiled `shouldBe` 2
            map LTA.generatedValue members `shouldBe` [9, 8]
            map LTA.generatedWeight members `shouldBe` [3, 5]

        it "skips deferred imports beside a known-empty child in either position" $ do
            automaton <- ambiguousTerms
            let deferred = LTA.fromLTA 1 automaton
            forM_ [LTA.pool [], LTA.fromLTA (-1) automaton] $ \emptySource ->
                forM_ [(deferred, emptySource), (emptySource, deferred)] $ \(left, right) -> do
                    let generator =
                            LTA.node "empty-pair" Top $
                                (,) <$> LTA.children left <*> LTA.children right
                    result <- LTA.compile unusedEntailment generator
                    fmap LTA.cardinality result `shouldBe` Left LTA.EmptyGenerator

        it "checks root, nested, and missing observations across an imported boundary" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver -> do
                let zero = variable "v" .==. (0 :: Int)
                    rows =
                        [ (State 1, [Transition "a" zero [] unconstrainedConstraint, plain "box" [State 2]])
                        ,
                            ( State 2
                            ,
                                [ Transition "a" zero [] unconstrainedConstraint
                                , Transition "a" (variable "v" .==. (1 :: Int)) [] unconstrainedConstraint
                                ]
                            )
                        ]
                    absent = Satisfies (path [0, 0]) true
                    guards =
                        [ (Satisfies (path [0]) zero, 1)
                        , (Satisfies (path [0, 0]) zero, 1)
                        , (Not absent, 1)
                        , (Or [Top, absent], 3)
                        ]
                imported <- either (fail . show) pure $ mkAutomaton (State 1) rows
                forM_ guards $ \(guard, count) -> do
                    let generator = LTA.node "host" (semanticConstraint guard) $ LTA.fromLTA 1 imported
                    compiled <- LTA.compile solver generator >>= either (fail . show) pure
                    oracle <- automatonFrom $ (State 0, [Transition "host" true [State 1] $ semanticConstraint guard]) : rows
                    LTA.cardinality compiled `shouldBe` count
                    denotationAtMost solver 2 oracle `shouldDenote` (termsOf compiled)

        it "reports unsupported scoped equality while retaining the core denotation" $ do
            let a = Tree.Node (LiquidSymbol "a" true) []
                b = Tree.Node (LiquidSymbol "b" true) []
                wrapped = Tree.Node (LiquidSymbol "wrap" true) [a]
                positive = [(a, a), (a, b), (b, a), (b, b), (wrapped, wrapped)]
                negative = [(a, wrapped), (b, wrapped), (wrapped, a), (wrapped, b)]
                allPairs = [(left, right) | left <- [a, b, wrapped], right <- [a, b, wrapped]]
            forM_ [(same, positive), (Not same, negative), (Or [same, Not same], allPairs)] $ \(guard, pairs) -> do
                let scoped = Substitute [Substitution (path [0]) (path [1])] guard
                    expected = [Tree.Node (LiquidSymbol "pair" true) [left, right] | (left, right) <- pairs]
                automaton <- pairsWith $ semanticConstraint scoped
                let source = LTA.fromLTA 2 automaton
                denotationAtMost unusedEntailment 2 automaton `shouldDenote` expected
                result <- LTA.compile unusedEntailment source
                case result of
                    Left (LTA.InvalidPruning (ResidualLTAConstraint _ residual)) ->
                        residual `shouldBe` scoped
                    Left err -> expectationFailure $ "unexpected scoped equality failure: " <> show err
                    Right _ -> expectationFailure "an unsupported scoped equality was silently compiled"

        it "keeps a large imported language compact without forcing source values" $ do
            result <- timeout 60000000 $ do
                automaton <- recursiveLists
                let source = fmap (const $ error "imported value was forced") $ LTA.fromLTA 70 automaton
                    ordinary = fmap (const $ error "ordinary value was forced") $ LTA.leaf () "ordinary" true
                    generator =
                        LTA.node "combined" unconstrainedConstraint $
                            (\_ _ -> (42 :: Int)) <$> LTA.children source <*> LTA.children ordinary
                    total = 2 ^ (71 :: Int) - 1
                compiled <- LTA.compile unusedEntailment generator >>= either (fail . show) pure
                LTA.cardinality compiled `shouldBe` total
                supportNodes compiled `shouldSatisfy` (\count -> count > 0 && count < 500)
                fmap LTA.generatedValue (LTA.unrank compiled 0) `shouldBe` Right 42
                fmap LTA.generatedValue (LTA.unrank compiled (total - 1)) `shouldBe` Right 42
            result `shouldBe` Just ()

        it "maps a shared depth-70 singleton beside an ordinary child without expanding its witness" $ do
            result <- timeout 60000000 $ do
                automaton <- sharedBinaryTerm unconstrainedConstraint
                let rootSymbol (Tree.Node (LiquidSymbol symbol _) _) = symbol
                    source = fmap rootSymbol $ LTA.fromLTA 71 automaton
                    generator =
                        LTA.node "combined" unconstrainedConstraint $
                            (,) <$> LTA.children source <*> LTA.children (LTA.leaf (7 :: Int) "ordinary" true)
                compiled <- LTA.compile unusedEntailment generator >>= either (fail . show) pure
                LTA.cardinality compiled `shouldBe` 1
                supportNodes compiled `shouldSatisfy` (\count -> count > 0 && count < 500)
                fmap LTA.generatedValue (LTA.unrank compiled 0) `shouldBe` Right ("root", 7)
            result `shouldBe` Just ()

        it "counts positive and negative equality without expanding huge terms" $ do
            forM_
                [ (equalityConstraint $ mkEqConstraints [[path [0], path [1]]], Right 1)
                , (semanticConstraint $ Not same, Left LTA.EmptyGenerator)
                ]
                $ \(constraint, expected) -> do
                    result <- timeout 60000000 $ do
                        automaton <- sharedBinaryTerm constraint
                        LTA.compile unusedEntailment $ LTA.fromLTA 71 automaton
                    fmap (fmap LTA.cardinality) result `shouldBe` Just expected

    describe "bounded symbolic automaton compilation" $ do
        it "counts and replays exponential nested equality and disequality languages" $ do
            let nested = Same (path [0, 0]) (path [1, 0])
                count = 2 ^ (70 :: Int) - 1
            forM_ [(nested, count), (Not nested, count * (count - 1)), (Or [nested, Not nested], count * count)] $ \(guard, expected) -> do
                completed <- timeout 20000000 $ do
                    automaton <- largeBoxedLists $ semanticConstraint guard
                    compiled <- compileBounded unusedEntailment 71 automaton
                    LTA.cardinality compiled `shouldBe` expected
                    forM_ [0, expected - 1] $ \rank -> do
                        generated <- either (fail . show) pure $ LTA.unrank compiled rank
                        accepts unusedEntailment automaton (LTA.generatedTerm generated) >>= (`shouldBe` Yes)
                completed `shouldBe` Just ()

        it "groups nested observations of an exponential equality import without decoding values" $ do
            completed <- timeout 20000000 $ do
                automaton <- largeBoxedLists $ equalityConstraint $ mkEqConstraints [[path [0, 0], path [1, 0]]]
                let source = fmap (const $ error "symbolic grouping decoded a source value") $ LTA.fromLTA 71 automaton
                    generator = LTA.node "host" (semanticConstraint $ Satisfies (path [0, 0, 0, 0]) true) $ fmap (const (42 :: Int)) source
                    solver = Entailment $ \_ _ -> pure Yes
                compiled <- LTA.compile solver generator >>= either (fail . show) pure
                LTA.cardinality compiled `shouldBe` 2 ^ (70 :: Int) - 2
                forM_ [0, LTA.cardinality compiled - 1] $ \rank ->
                    fmap LTA.generatedValue (LTA.unrank compiled rank) `shouldBe` Right 42
            completed `shouldBe` Just ()

        it "preserves missing-path semantics in reflexive Boolean equality" $ do
            let reflexive = Same (path [0, 0]) (path [0, 0])
            forM_ [reflexive, Not reflexive] $ \guard -> do
                automaton <-
                    automatonFrom
                        [ (State 0, [Transition "root" true [State 1] $ semanticConstraint guard])
                        , (State 1, [plain "a" [], plain "wrap" [State 2]])
                        , (State 2, [plain "a" []])
                        ]
                compiled <- compileBounded unusedEntailment 2 automaton
                LTA.cardinality compiled `shouldBe` 1
                denotationAtMost unusedEntailment 2 automaton `shouldDenote` (termsOf compiled)

        it "matches the bounded denotation of recursive two-atom lists" $ do
            automaton <- recursiveLists
            forM_ [(0, 1), (1, 3), (2, 7)] $ \(depth, count) -> do
                compiled <- compileBounded unusedEntailment depth automaton
                LTA.cardinality compiled `shouldBe` count
                denotationAtMost unusedEntailment depth automaton `shouldDenote` (termsOf compiled)
                repeated <- compileBounded unusedEntailment depth automaton
                termsOf repeated `shouldBe` termsOf compiled
                checkShrinks unusedEntailment automaton compiled

        it "counts mutually recursive and unproductive states at the bound" $ do
            productive <-
                automatonFrom
                    [ (State 0, [plain "nil" [], plain "left" [State 1]])
                    , (State 1, [plain "right" [State 0]])
                    ]
            compiled <- compileBounded unusedEntailment 2 productive
            LTA.cardinality compiled `shouldBe` 2
            unproductive <- automatonFrom [(State 0, [plain "loop" [State 0]])]
            result <- LTA.compileAutomatonUpToDepth unusedEntailment 3 unproductive
            fmap LTA.cardinality result `shouldBe` Left LTA.EmptyGenerator

        it "treats a negative bound as an empty language" $ do
            automaton <- recursiveLists
            result <- LTA.compileAutomatonUpToDepth unusedEntailment (-1) automaton
            fmap LTA.cardinality result `shouldBe` Left LTA.EmptyGenerator

        it "deduplicates accepting runs and preserves replay order" $ do
            automaton <- ambiguousTerms
            compiled <- compileBounded unusedEntailment 1 automaton
            LTA.cardinality compiled `shouldBe` 3
            denotationAtMost unusedEntailment 1 automaton `shouldDenote` (termsOf compiled)
            checkShrinks unusedEntailment automaton compiled
            LTA.shrinkRank compiled 2 `shouldBe` [0]
            mapped <- LTA.compileAutomatonUpToDepthWith unusedEntailment (\_ _ _ -> ()) 1 automaton
            fmap LTA.cardinality mapped `shouldBe` Right 3
            fmap termsOf mapped `shouldBe` Right (termsOf compiled)

        it "retains distinct refinements when symbols and values coincide" $ do
            automaton <-
                automatonFrom
                    [(State 0, [plain "a" [], Transition "a" (variable "v" .==. (0 :: Int)) [] unconstrainedConstraint])]
            result <- LTA.compileAutomatonUpToDepthWith unusedEntailment (\_ _ _ -> ()) 0 automaton
            fmap LTA.cardinality result `shouldBe` Right 2

        it "handles negated and disjunctive equality symbolically" $ do
            forM_ [Not same, Or [same, Not same]] $ \guard -> do
                automaton <- pairsWith $ semanticConstraint guard
                compiled <- compileBounded unusedEntailment 2 automaton
                denotationAtMost unusedEntailment 2 automaton `shouldDenote` (termsOf compiled)
                checkShrinks unusedEntailment automaton compiled
                concatMap (LTA.shrinkRank compiled) [0 .. LTA.cardinality compiled - 1]
                    `shouldSatisfy` (not . null)

        it "keeps both siblings equal when shrinking positive equality" $ do
            automaton <- pairsWith $ equalityConstraint $ mkEqConstraints [[path [0], path [1]]]
            compiled <- compileBounded unusedEntailment 2 automaton
            LTA.cardinality compiled `shouldBe` 3
            checkShrinks unusedEntailment automaton compiled
            length (LTA.shrinkRank compiled 2) `shouldBe` 2

        it "evaluates absent paths inside negation and disjunction" $ do
            forM_ [(Not missing, 1), (Or [Top, missing], 2)] $ \(guard, count) -> do
                automaton <-
                    automatonFrom
                        [ (State 0, [Transition "root" true [State 1] $ semanticConstraint guard])
                        , (State 1, [plain "a" [], plain "wrap" [State 2]])
                        , (State 2, [plain "a" []])
                        ]
                let solver = Entailment $ \_ _ -> pure Yes
                compiled <- compileBounded solver 2 automaton
                LTA.cardinality compiled `shouldBe` count
                denotationAtMost solver 2 automaton `shouldDenote` (termsOf compiled)

        it "reports unavailable compound actual identities without changing the core language" $
            withZ3 [(Fixpoint.symbol name, Fixpoint.FInt) | name <- ["v", "x", "y", "app", "known"] :: [String]] $ \solver -> do
                let guard =
                        Substitute
                            [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
                            (Satisfies (path []) $ variable "x" .==. variable "y")
                automaton <-
                    automatonFrom
                        [ (State 0, [Transition "pair" true [State 1, State 1, State 2, State 3] $ semanticConstraint guard])
                        , (State 1, [Transition "known" (variable "v" .==. (0 :: Int)) [] unconstrainedConstraint, plain "app" [State 4]])
                        , (State 2, [plain "x" []])
                        , (State 3, [plain "y" []])
                        , (State 4, [plain "a" [], plain "b" []])
                        ]
                denotationAtMost solver 2 automaton >>= (\result -> fmap length result `shouldBe` Right 3)
                result <- LTA.compileAutomatonUpToDepth solver 2 automaton
                case result of
                    Left (LTA.InvalidPruning (ResidualLTAConstraint _ residual)) -> residual `shouldBe` guard
                    Left err -> expectationFailure $ show err
                    Right _ -> expectationFailure "unavailable compound identity was silently compiled"

        it "reports an undecidable full-term guard" $ do
            automaton <- pairsWith $ semanticConstraint $ Satisfies (path [0]) true
            result <- LTA.compileAutomatonUpToDepth (Entailment $ \_ _ -> pure Unknown) 2 automaton
            fmap LTA.cardinality result `shouldBe` Left LTA.SolverUnknown

        it "uses the solver only during compilation" $ do
            calls <- newIORef (0 :: Int)
            let solver = Entailment $ \_ _ -> modifyIORef' calls (+ 1) >> pure Yes
            automaton <- pairsWith $ semanticConstraint $ Satisfies (path [0]) true
            compiled <- compileBounded solver 2 automaton
            before <- readIORef calls
            before `shouldSatisfy` (> 0)
            length (termsOf compiled) `shouldBe` 9
            length (concatMap (LTA.shrinkRank compiled) [0 .. 8]) `shouldSatisfy` (> 0)
            readIORef calls >>= (`shouldBe` before)

        it "keeps bounded shared graphs compact without forcing a huge witness" $ do
            let state level = State $ level + 1
            automaton <-
                automatonFrom $
                    [(State 0, [plain "root" [state 70]]), (state 0, [plain "a" []])]
                        <> [(state level, [plain "fork" [state (level - 1), state (level - 1)]]) | level <- [1 .. 70]]
            compiled <-
                LTA.compileAutomatonUpToDepthWith unusedEntailment (\symbol _ _ -> symbol) 71 automaton
                    >>= either (fail . show) pure
            LTA.cardinality compiled `shouldBe` 1
            fmap LTA.generatedValue (LTA.unrank compiled 0) `shouldBe` Right "root"
            LTA.shrinkRank compiled 0 `shouldBe` []
  where
    plain symbol children = Transition symbol true children unconstrainedConstraint
    same = Same (path [0]) (path [1])
    missing = Satisfies (path [0, 0]) true
    variable :: String -> Fixpoint.Expr
    variable name = Fixpoint.EVar $ Fixpoint.symbol (name :: String)

{- | Compare a bounded denotation with the terms it should contain. The
denotation is a set, so order is not compared.
-}
shouldDenote :: IO (Either EnumerationError [Tree.Tree LiquidSymbol]) -> [Tree.Tree LiquidSymbol] -> IO ()
shouldDenote denotation expected = denotation >>= \result -> fmap sort result `shouldBe` Right (sort expected)
