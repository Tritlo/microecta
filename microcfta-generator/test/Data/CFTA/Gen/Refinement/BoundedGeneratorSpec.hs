{-# LANGUAGE TypeApplications #-}

module Data.CFTA.Gen.Refinement.BoundedGeneratorSpec (spec) where

import Control.Monad (forM_, void)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.List (elemIndex, nub, sort)
import Data.Proxy (Proxy (Proxy))
import Data.Ratio ((%))
import qualified Data.Tree as Tree
import Data.Typeable (typeRep)
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldMatchList, shouldSatisfy)
import Text.Read (readMaybe)

import qualified Data.CFTA.Equality as ECTA
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTA
import Data.CFTA.Gen.Refinement.TestSupport (massesByRank, ranks, termsOf, values)
import qualified Data.CFTA.Generic as Datatype
import Data.CFTA.Refinement (
    Automaton,
    DenotationError,
    Entailment (Entailment),
    Guard (Bottom, Not, Or, Same, Satisfies, Substitute, Top),
    LiquidConstraint,
    LiquidSymbol (LiquidSymbol),
    Node (EmptyNode, Mu, Node),
    Refinement,
    Substitution (Substitution),
    Symbol,
    Transition,
    Verdict (Unknown, Yes),
    accepts,
    denotationAtMost,
    equalityConstraint,
    path,
    semanticConstraint,
    unconstrainedConstraint,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (integer, true, (.==.), (.>.))
import qualified Data.CFTA.Refinement.Expression as Refinement
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import qualified Language.Fixpoint.Types as Fixpoint

-- | Fail if an unconstrained fixture unexpectedly calls the solver.
unusedEntailment :: Entailment
unusedEntailment = Entailment $ \_ _ -> fail "unexpected solver call"

-- | Compile a bounded language or report the compiler error.
compileBounded :: Entailment -> Int -> Automaton -> IO (LTA.LTAGen (Tree.Tree LiquidSymbol))
compileBounded solver depth automaton =
    LTA.compile solver (LTA.fromAutomatonUpToDepth depth automaton) >>= either (fail . show) pure

-- | Compile a bounded language and fold each selected term into a value.
compileBoundedWith ::
    Entailment -> (Symbol -> Refinement -> [a] -> a) -> Int -> Automaton -> IO (Either LTA.GenError (LTA.LTAGen a))
compileBoundedWith solver build depth automaton =
    LTA.compile solver $
        Tree.foldTree (\(LiquidSymbol symbol refinement) -> build symbol refinement)
            <$> LTA.fromAutomatonUpToDepth depth automaton

-- | The replay rank of one accepted term.
rankOf :: LTA.LTAGen a -> Tree.Tree LiquidSymbol -> IO Integer
rankOf compiled term = case elemIndex term (termsOf compiled) of
    Just rank -> pure $ toInteger rank
    Nothing -> fail $ "term is not in the compiled language: " <> show term

-- | The number of nodes of a term.
termSize :: Tree.Tree LiquidSymbol -> Int
termSize = length . Tree.flatten

{- | Check that structural shrinks stay in the language at smaller ranks, and
that every member of smaller size is accepted and strictly smaller.
-}
checkShrinks :: Entailment -> Automaton -> LTA.LTAGen a -> IO ()
checkShrinks solver automaton compiled =
    forM_ (zip (ranks compiled) (termsOf compiled)) $ \(rank, source) -> do
        let targets = LTA.shrinkRank compiled rank
        targets `shouldBe` nub targets
        targets `shouldSatisfy` all (\target -> target >= 0 && target < rank)
        forM_ (LTA.smallerMembers compiled rank) $ \(target, _) -> do
            let term = termsOf compiled !! fromInteger target
            accepts solver automaton term >>= (`shouldBe` Yes)
            termSize term `shouldSatisfy` (< termSize source)
        length (LTA.smallerMembers compiled rank) `shouldSatisfy` (< length (ranks compiled))

-- | An unrefined, unconstrained transition.
plain :: Symbol -> [Automaton] -> Transition
plain symbol children = Transition symbol true children unconstrainedConstraint

-- | The two atoms @a@ and @b@.
atoms :: Automaton
atoms = Node [plain "a" [], plain "b" []]

-- | Recursive lists with two distinct atoms.
recursiveLists :: Automaton
recursiveLists = Mu $ \list -> Node [plain "nil" [], plain "cons" [atoms, list]]

-- | Independent pairs with two leaves and one compound alternative.
pairsWith :: LiquidConstraint -> Automaton
pairsWith constraint = Node [Transition "pair" true [choice, choice] constraint]
  where
    choice = Node [plain "a" [], plain "b" [], plain "wrap" [Node [plain "a" []]]]

-- | Two boxed list languages with a shared finite graph and a nested guard.
largeBoxedLists :: LiquidConstraint -> Automaton
largeBoxedLists constraint = Node [Transition "pair" true [boxed, boxed] constraint]
  where
    boxed = Node [plain "box" [lists !! 69]]
    lists = Node [plain "nil" []] : [Node [plain "nil" [], plain "cons" [atoms, shorter]] | shorter <- lists]

-- | Three terms with two runs that accept the same wrapped leaf.
ambiguousTerms :: Automaton
ambiguousTerms = Node [plain "a" [], plain "wrap" [atoms], plain "wrap" [Node [plain "a" []]]]

-- | Complete binary fork trees over one atom, by height.
forks :: [Automaton]
forks = Node [plain "a" []] : [Node [plain "fork" [shorter, shorter]] | shorter <- forks]

-- | One term with a shared graph and more than 2^70 tree nodes.
sharedBinaryTerm :: LiquidConstraint -> Automaton
sharedBinaryTerm constraint = Node [Transition "root" true [forks !! 70, forks !! 70] constraint]

-- | A choice below a root, with a nested optional descendant.
optionalDescendant :: Guard -> Automaton
optionalDescendant guard =
    Node [Transition "root" true [Node [plain "a" [], plain "wrap" [Node [plain "a" []]]]] $ semanticConstraint guard]

-- | Force the retained support graph without inspecting generated values.
supportNodes :: LTA.LTAGen a -> Int
supportNodes = either (const 0) ECTA.nodeCount . LTA.support

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
                LTA.cardinality compiled `shouldBe` Right 7
                sort (values compiled) `shouldBe` expected
                forM_ (zip (ranks compiled) (termsOf compiled)) $ \(rank, term) ->
                    forM_ (LTA.smallerMembers compiled rank) $ \(target, smaller) -> do
                        smaller `shouldSatisfy` (`elem` expected)
                        termSize (termsOf compiled !! fromInteger target) `shouldSatisfy` (< termSize term)

    describe "bounded LTA sources in ordinary generators" $ do
        it "reads an automaton the engine can count without the solver" $ do
            let boolean = pairsWith $ semanticConstraint $ Not same
            forM_ [(2, recursiveLists), (1, ambiguousTerms), (2, boolean)] $ \(depth, automaton) -> do
                let source = LTA.fromAutomatonUpToDepth depth automaton
                void (LTA.support source) `shouldBe` Right ()
                compiled <- LTA.compile unusedEntailment source >>= either (fail . show) pure
                termsOf compiled `shouldBe` termsOf source
                denotationAtMost unusedEntailment depth automaton `shouldDenote` termsOf compiled
                values compiled `shouldBe` termsOf compiled

        it "defers an automaton whose guards need the solver" $ do
            let source = LTA.fromAutomatonUpToDepth 2 $ pairsWith $ semanticConstraint $ Satisfies (path [0]) true
            void (LTA.support source) `shouldBe` Left LTA.SourceRequiresCompilation
            LTA.cardinality source `shouldBe` Left LTA.SourceRequiresCompilation
            compiled <- LTA.compile (Entailment $ \_ _ -> pure Yes) source >>= either (fail . show) pure
            LTA.cardinality compiled `shouldBe` Right 9

        it "keeps unique imported terms and repeated pool draws with their weights" $ do
            imported <- compileBounded unusedEntailment 1 ambiguousTerms
            let weighted =
                    LTA.frequency
                        [ (2, LTA.pool [LTA.Refined (7 :: Int) "draw" true, LTA.Refined 7 "draw" true])
                        , (5, LTA.leaf 7 "other" true)
                        ]
            let source = fmap (const (7 :: Int)) $ LTA.fromAutomatonUpToDepth 1 ambiguousTerms
                generator =
                    LTA.node "combined" unconstrainedConstraint $
                        (,) <$> source <*> weighted
            compiled <- LTA.compile unusedEntailment generator >>= either (fail . show) pure
            LTA.cardinality compiled `shouldBe` Right 9
            values compiled `shouldBe` replicate 9 (7, 7)
            map snd (massesByRank compiled) `shouldBe` concat (replicate 3 [1 % 21, 1 % 21, 5 % 21])
            termsOf compiled
                `shouldBe` [ Tree.Node (LiquidSymbol "combined" true) [term, Tree.Node (LiquidSymbol symbol true) []]
                           | term <- termsOf imported
                           , symbol <- ["draw", "draw", "other"]
                           ]
            length (nub $ termsOf compiled) `shouldBe` 6

        it "retains an ordinary alternative when an imported bound is empty" $
            forM_ [LTA.fromAutomatonUpToDepth 0 EmptyNode, LTA.fromAutomatonUpToDepth (-1) recursiveLists] $ \source -> do
                emptyResult <- LTA.compile unusedEntailment source
                (emptyResult >>= LTA.cardinality) `shouldBe` Left LTA.EmptyGenerator
                let alternatives =
                        LTA.oneof [fmap (const (7 :: Int)) source, LTA.leaf 9 "ordinary" true]
                compiled <- LTA.compile unusedEntailment alternatives >>= either (fail . show) pure
                LTA.cardinality compiled `shouldBe` Right 1
                LTA.unrank compiled 0 `shouldBe` Right 9

        it "skips a rejected deferred import and keeps the branch weights" $ do
            let rejected =
                    LTA.node "dead" Bottom
                        $ fmap (const (7 :: Int))
                        $ LTA.fromAutomatonUpToDepth 1 ambiguousTerms
            let alternatives =
                    LTA.frequency
                        [ (3, LTA.leaf 9 "ordinary" true)
                        , (11, rejected)
                        , (5, LTA.leaf 8 "later" true)
                        ]
            compiled <-
                LTA.compile unusedEntailment alternatives
                    >>= either (fail . show) pure
            LTA.cardinality compiled `shouldBe` Right 2
            values compiled `shouldBe` [9, 8]
            massesByRank compiled `shouldBe` [(0, 3 % 8), (1, 5 % 8)]

        it "skips deferred imports beside a known-empty child in either position" $ do
            let deferred = LTA.fromAutomatonUpToDepth 1 ambiguousTerms
            forM_ [LTA.pool [], LTA.fromAutomatonUpToDepth (-1) ambiguousTerms] $ \emptySource ->
                forM_ [(deferred, emptySource), (emptySource, deferred)] $ \(left, right) -> do
                    let generator =
                            LTA.node "empty-pair" Top $
                                (,) <$> left <*> right
                    result <- LTA.compile unusedEntailment generator
                    (result >>= LTA.cardinality) `shouldBe` Left LTA.EmptyGenerator

        it "checks root, nested, and missing observations across an imported boundary" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver -> do
                let zero = variable "v" .==. (0 :: Int)
                    boxed =
                        Node
                            [ Transition "a" zero [] unconstrainedConstraint
                            , Transition "a" (variable "v" .==. (1 :: Int)) [] unconstrainedConstraint
                            ]
                    imported = Node [Transition "a" zero [] unconstrainedConstraint, plain "box" [boxed]]
                    absent = Satisfies (path [0, 0]) true
                    guards =
                        [ (Satisfies (path [0]) zero, 1)
                        , (Satisfies (path [0, 0]) zero, 1)
                        , (Not absent, 1)
                        , (Or [Top, absent], 3)
                        ]
                forM_ guards $ \(guard, count) -> do
                    let generator = LTA.node "host" (semanticConstraint guard) $ LTA.fromAutomatonUpToDepth 1 imported
                        oracle = Node [Transition "host" true [imported] $ semanticConstraint guard]
                    compiled <- LTA.compile solver generator >>= either (fail . show) pure
                    LTA.cardinality compiled `shouldBe` Right count
                    denotationAtMost solver 2 oracle `shouldDenote` termsOf compiled

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
                    automaton = pairsWith $ semanticConstraint scoped
                    source = LTA.fromAutomatonUpToDepth 2 automaton
                denotationAtMost unusedEntailment 2 automaton `shouldDenote` expected
                result <- LTA.compile unusedEntailment source
                case result of
                    Left (LTA.ResidualGuard residual) -> residual `shouldBe` scoped
                    Left err -> expectationFailure $ "unexpected scoped equality failure: " <> show err
                    Right _ -> expectationFailure "an unsupported scoped equality was silently compiled"

        it "keeps a large imported language compact without forcing source values" $ do
            result <- timeout 60000000 $ do
                let source = fmap (const $ error "imported value was forced") $ LTA.fromAutomatonUpToDepth 70 recursiveLists
                    ordinary = fmap (const $ error "ordinary value was forced") $ LTA.leaf () "ordinary" true
                    generator =
                        LTA.node "combined" unconstrainedConstraint $
                            (\_ _ -> (42 :: Int)) <$> source <*> ordinary
                    total = 2 ^ (71 :: Int) - 1
                compiled <- LTA.compile unusedEntailment generator >>= either (fail . show) pure
                LTA.cardinality compiled `shouldBe` Right total
                supportNodes compiled `shouldSatisfy` (\count -> count > 0 && count < 500)
                LTA.unrank compiled 0 `shouldBe` Right 42
                LTA.unrank compiled (total - 1) `shouldBe` Right 42
            result `shouldBe` Just ()

        it "maps a shared depth-70 singleton beside an ordinary child without expanding its witness" $ do
            result <- timeout 60000000 $ do
                let automaton = sharedBinaryTerm unconstrainedConstraint
                    rootSymbol (Tree.Node (LiquidSymbol symbol _) _) = symbol
                    source = fmap rootSymbol $ LTA.fromAutomatonUpToDepth 71 automaton
                    generator =
                        LTA.node "combined" unconstrainedConstraint $
                            (,) <$> source <*> LTA.leaf (7 :: Int) "ordinary" true
                compiled <- LTA.compile unusedEntailment generator >>= either (fail . show) pure
                LTA.cardinality compiled `shouldBe` Right 1
                supportNodes compiled `shouldSatisfy` (\count -> count > 0 && count < 500)
                LTA.unrank compiled 0 `shouldBe` Right ("root", 7)
            result `shouldBe` Just ()

        it "counts positive and negative equality without expanding huge terms" $ do
            forM_
                [ (equalityConstraint $ mkEqConstraints [[path [0], path [1]]], Right 1)
                , (semanticConstraint $ Not same, Left LTA.EmptyGenerator)
                ]
                $ \(constraint, expected) -> do
                    result <- timeout 60000000 $ LTA.compile unusedEntailment $ LTA.fromAutomatonUpToDepth 71 $ sharedBinaryTerm constraint
                    fmap (>>= LTA.cardinality) result `shouldBe` Just expected

    describe "bounded symbolic automaton compilation" $ do
        it "counts and replays exponential nested equality and disequality languages" $ do
            let nested = Same (path [0, 0]) (path [1, 0])
                count = 2 ^ (70 :: Int) - 1
            forM_ [(nested, count), (Not nested, count * (count - 1)), (Or [nested, Not nested], count * count)] $ \(guard, expected) -> do
                completed <- timeout 20000000 $ do
                    let automaton = largeBoxedLists $ semanticConstraint guard
                    compiled <- compileBounded unusedEntailment 71 automaton
                    LTA.cardinality compiled `shouldBe` Right expected
                    forM_ [0, expected - 1] $ \rank -> do
                        generated <- either (fail . show) pure $ LTA.unrank compiled rank
                        accepts unusedEntailment automaton generated >>= (`shouldBe` Yes)
                completed `shouldBe` Just ()

        it "groups nested observations of an exponential equality import without decoding values" $ do
            completed <- timeout 20000000 $ do
                let automaton = largeBoxedLists $ equalityConstraint $ mkEqConstraints [[path [0, 0], path [1, 0]]]
                    source = fmap (const $ error "symbolic grouping decoded a source value") $ LTA.fromAutomatonUpToDepth 71 automaton
                    generator = LTA.node "host" (semanticConstraint $ Satisfies (path [0, 0, 0, 0]) true) $ fmap (const (42 :: Int)) source
                    solver = Entailment $ \_ _ -> pure Yes
                compiled <- LTA.compile solver generator >>= either (fail . show) pure
                LTA.cardinality compiled `shouldBe` Right (2 ^ (70 :: Int) - 2)
                forM_ [0, 2 ^ (70 :: Int) - 3] $ \rank ->
                    LTA.unrank compiled rank `shouldBe` Right 42
            completed `shouldBe` Just ()

        it "preserves missing-path semantics in reflexive Boolean equality" $ do
            let reflexive = Same (path [0, 0]) (path [0, 0])
            forM_ [reflexive, Not reflexive] $ \guard -> do
                let automaton = optionalDescendant guard
                compiled <- compileBounded unusedEntailment 2 automaton
                LTA.cardinality compiled `shouldBe` Right 1
                denotationAtMost unusedEntailment 2 automaton `shouldDenote` termsOf compiled

        it "matches the bounded denotation of recursive two-atom lists" $
            forM_ [(0, 1), (1, 3), (2, 7)] $ \(depth, count) -> do
                compiled <- compileBounded unusedEntailment depth recursiveLists
                LTA.cardinality compiled `shouldBe` Right count
                denotationAtMost unusedEntailment depth recursiveLists `shouldDenote` termsOf compiled
                repeated <- compileBounded unusedEntailment depth recursiveLists
                termsOf repeated `shouldBe` termsOf compiled
                checkShrinks unusedEntailment recursiveLists compiled

        it "counts mutually recursive and unproductive nodes at the bound" $ do
            let productive = Mu $ \outer -> Node [plain "nil" [], plain "left" [Node [plain "right" [outer]]]]
            compiled <- compileBounded unusedEntailment 2 productive
            LTA.cardinality compiled `shouldBe` Right 2
            let unproductive = Mu $ \self -> Node [plain "loop" [self]]
            result <- LTA.compile unusedEntailment $ LTA.fromAutomatonUpToDepth 3 unproductive
            (result >>= LTA.cardinality) `shouldBe` Left LTA.EmptyGenerator

        it "treats a negative bound as an empty language" $ do
            result <- LTA.compile unusedEntailment $ LTA.fromAutomatonUpToDepth (-1) recursiveLists
            (result >>= LTA.cardinality) `shouldBe` Left LTA.EmptyGenerator

        it "deduplicates accepting runs and preserves replay order" $ do
            compiled <- compileBounded unusedEntailment 1 ambiguousTerms
            LTA.cardinality compiled `shouldBe` Right 3
            denotationAtMost unusedEntailment 1 ambiguousTerms `shouldDenote` termsOf compiled
            checkShrinks unusedEntailment ambiguousTerms compiled
            mapped <- compileBoundedWith unusedEntailment (\_ _ _ -> ()) 1 ambiguousTerms
            (mapped >>= LTA.cardinality) `shouldBe` Right 3
            fmap termsOf mapped `shouldBe` Right (termsOf compiled)

        it "retains distinct refinements when symbols and values coincide" $ do
            let automaton = Node [plain "a" [], Transition "a" (variable "v" .==. (0 :: Int)) [] unconstrainedConstraint]
            result <- compileBoundedWith unusedEntailment (\_ _ _ -> ()) 0 automaton
            (result >>= LTA.cardinality) `shouldBe` Right 2

        it "handles negated and disjunctive equality symbolically" $
            forM_ [Not same, Or [same, Not same]] $ \guard -> do
                let automaton = pairsWith $ semanticConstraint guard
                compiled <- compileBounded unusedEntailment 2 automaton
                denotationAtMost unusedEntailment 2 automaton `shouldDenote` termsOf compiled
                checkShrinks unusedEntailment automaton compiled

        it "keeps both siblings equal when shrinking positive equality" $ do
            let automaton = pairsWith $ equalityConstraint $ mkEqConstraints [[path [0], path [1]]]
            compiled <- compileBounded unusedEntailment 2 automaton
            LTA.cardinality compiled `shouldBe` Right 3
            checkShrinks unusedEntailment automaton compiled
            wrappedPair <-
                rankOf compiled
                    $ Tree.Node (LiquidSymbol "pair" true)
                    $ replicate 2
                    $ Tree.Node (LiquidSymbol "wrap" true) [Tree.Node (LiquidSymbol "a" true) []]
            LTA.smallerMembers compiled wrappedPair `shouldSatisfy` (not . null)

        it "evaluates absent paths inside negation and disjunction" $
            forM_ [(Not missing, 1), (Or [Top, missing], 2)] $ \(guard, count) -> do
                let automaton = optionalDescendant guard
                    solver = Entailment $ \_ _ -> pure Yes
                compiled <- compileBounded solver 2 automaton
                LTA.cardinality compiled `shouldBe` Right count
                denotationAtMost solver 2 automaton `shouldDenote` termsOf compiled

        it "reports unavailable compound actual identities without changing the core language" $
            withZ3 [(Fixpoint.symbol name, Fixpoint.FInt) | name <- ["v", "x", "y", "app", "known"] :: [String]] $ \solver -> do
                let guard =
                        Substitute
                            [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
                            (Satisfies (path []) $ variable "x" .==. variable "y")
                    known = Node [Transition "known" (variable "v" .==. (0 :: Int)) [] unconstrainedConstraint, plain "app" [atoms]]
                    automaton =
                        Node
                            [ Transition "pair" true [known, known, Node [plain "x" []], Node [plain "y" []]] $
                                semanticConstraint guard
                            ]
                denotationAtMost solver 2 automaton >>= (\result -> fmap length result `shouldBe` Right 3)
                result <- LTA.compile solver $ LTA.fromAutomatonUpToDepth 2 automaton
                case result of
                    Left (LTA.ResidualGuard residual) -> residual `shouldBe` guard
                    Left err -> expectationFailure $ show err
                    Right _ -> expectationFailure "unavailable compound identity was silently compiled"

        it "reports an undecidable full-term guard" $ do
            let automaton = pairsWith $ semanticConstraint $ Satisfies (path [0]) true
            result <- LTA.compile (Entailment $ \_ _ -> pure Unknown) $ LTA.fromAutomatonUpToDepth 2 automaton
            (result >>= LTA.cardinality) `shouldBe` Left LTA.SolverUnknown

        it "uses the solver only during compilation" $ do
            calls <- newIORef (0 :: Int)
            let solver = Entailment $ \_ _ -> modifyIORef' calls (+ 1) >> pure Yes
                automaton = pairsWith $ semanticConstraint $ Satisfies (path [0]) true
            compiled <- compileBounded solver 2 automaton
            before <- readIORef calls
            before `shouldSatisfy` (> 0)
            length (termsOf compiled) `shouldBe` 9
            length (concatMap (LTA.shrinkRank compiled) [0 .. 8]) `shouldSatisfy` (> 0)
            readIORef calls >>= (`shouldBe` before)

        it "keeps bounded shared graphs compact without forcing a huge witness" $ do
            let automaton = Node [plain "root" [forks !! 70]]
            compiled <-
                compileBoundedWith unusedEntailment (\symbol _ _ -> symbol) 71 automaton
                    >>= either (fail . show) pure
            LTA.cardinality compiled `shouldBe` Right 1
            LTA.unrank compiled 0 `shouldBe` Right "root"
            LTA.shrinkRank compiled 0 `shouldBe` []

        it "orders the ranks of a shared graph by its explicit view" $ do
            let automaton = Node [plain "root" [forks !! 2]]
            compiled <- compileBounded unusedEntailment 3 automaton
            termsOf compiled `shouldMatchList` [Tree.Node (LiquidSymbol "root" true) [fork 2]]
  where
    same = Same (path [0]) (path [1])
    missing = Satisfies (path [0, 0]) true
    variable :: String -> Fixpoint.Expr
    variable name = Fixpoint.EVar $ Fixpoint.symbol (name :: String)
    fork :: Int -> Tree.Tree LiquidSymbol
    fork 0 = Tree.Node (LiquidSymbol "a" true) []
    fork height = Tree.Node (LiquidSymbol "fork" true) [fork (height - 1), fork (height - 1)]

{- | Compare a bounded denotation with the terms it should contain. The
denotation is a set, so order is not compared.
-}
shouldDenote :: IO (Either DenotationError [Tree.Tree LiquidSymbol]) -> [Tree.Tree LiquidSymbol] -> IO ()
shouldDenote denotation expected = denotation >>= \result -> fmap sort result `shouldBe` Right (sort expected)
