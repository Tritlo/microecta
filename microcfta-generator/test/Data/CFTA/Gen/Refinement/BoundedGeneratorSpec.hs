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
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Gen.Refinement.TestSupport (massesByRank, ranks, termsOf, values)
import qualified Data.CFTA.Generic as Datatype
import Data.CFTA.Refinement (
    Automaton,
    DenotationError,
    Entailment (Entailment),
    Formula,
    Guard (Bottom, Not, Or, Same, Satisfies, Substitute, Top),
    LiquidConstraint,
    LiquidSymbol (LiquidSymbol),
    Node (EmptyNode, Mu, Node),
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
import Data.CFTA.Refinement.Expression (Expr, refinementFormula, toExpr, true, (.==), (.>))
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import qualified Language.Fixpoint.Types as Fixpoint

-- | Fail if an unconstrained fixture unexpectedly calls the solver.
unusedEntailment :: Entailment
unusedEntailment = Entailment $ \_ _ -> fail "unexpected solver call"

-- | Compile a bounded language or report the compiler error.
compileBounded :: Entailment -> Int -> Automaton -> IO (LTAGen.LTAGen (Tree.Tree LiquidSymbol))
compileBounded solver depth automaton =
    LTAGen.compileWith solver (LTAGen.fromAutomatonUpToDepth depth automaton) >>= either (fail . show) pure

-- | Compile a bounded language and fold each selected term into a value.
compileBoundedWith ::
    Entailment -> (Symbol -> Formula -> [a] -> a) -> Int -> Automaton -> IO (Either LTAGen.GenError (LTAGen.LTAGen a))
compileBoundedWith solver build depth automaton =
    LTAGen.compileWith solver $
        Tree.foldTree (\(LiquidSymbol symbol refinement) -> build symbol refinement)
            <$> LTAGen.fromAutomatonUpToDepth depth automaton

-- | The replay rank of one accepted term.
rankOf :: LTAGen.LTAGen a -> Tree.Tree LiquidSymbol -> IO Integer
rankOf compiled term = case elemIndex term (termsOf compiled) of
    Just rank -> pure $ toInteger rank
    Nothing -> fail $ "term is not in the compiled language: " <> show term

-- | The number of nodes of a term.
termSize :: Tree.Tree LiquidSymbol -> Int
termSize = length . Tree.flatten

{- | Check that structural shrinks stay in the language at smaller ranks, and
that every member of smaller size is accepted and strictly smaller.
-}
checkShrinks :: Entailment -> Automaton -> LTAGen.LTAGen a -> IO ()
checkShrinks solver automaton compiled =
    forM_ (zip (ranks compiled) (termsOf compiled)) $ \(rank, source) -> do
        let targets = LTAGen.shrinkRank compiled rank
        targets `shouldBe` nub targets
        targets `shouldSatisfy` all (\target -> target >= 0 && target < rank)
        forM_ (LTAGen.smallerMembers compiled rank) $ \(target, _) -> do
            let term = termsOf compiled !! fromInteger target
            accepts solver automaton term >>= (`shouldBe` Yes)
            termSize term `shouldSatisfy` (< termSize source)
        length (LTAGen.smallerMembers compiled rank) `shouldSatisfy` (< length (ranks compiled))

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
supportNodes :: LTAGen.LTAGen a -> Int
supportNodes = either (const 0) ECTA.nodeCount . LTAGen.support

spec :: Spec
spec = do
    describe "liquid annotations on a derived datatype" $ do
        it "keeps the datatype codec and shrinks within the guarded language" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver -> do
                datatype <- either (fail . show) pure $ Datatype.deriveFTAWith @(Maybe (Int, Int)) $ Datatype.domain @Int [0, 1, 2]
                let annotate constructor
                        | Datatype.constructorType constructor == typeRep (Proxy @Int) =
                            ( maybe (const true) (\literal v -> v .== fromIntegral literal)
                                $ readMaybe @Integer
                                $ Datatype.constructorName constructor
                            , unconstrainedConstraint
                            )
                        | Datatype.constructorName constructor == "(,)" =
                            (const true, semanticConstraint $ Satisfies (path [1]) (refinementFormula $ \v -> v .> 0))
                        | otherwise = (const true, unconstrainedConstraint)
                    source = LTAGen.fromDatatypeUpToDepth 2 $ Datatype.annotateDatatype annotate datatype
                    expected = Nothing : [Just (numerator, denominator) | numerator <- [0, 1, 2], denominator <- [1, 2]]
                compiled <- LTAGen.compileWith solver source >>= either (fail . show) pure
                LTAGen.cardinality compiled `shouldBe` Right 7
                sort (values compiled) `shouldBe` expected
                forM_ (zip (ranks compiled) (termsOf compiled)) $ \(rank, term) ->
                    forM_ (LTAGen.smallerMembers compiled rank) $ \(target, smaller) -> do
                        smaller `shouldSatisfy` (`elem` expected)
                        termSize (termsOf compiled !! fromInteger target) `shouldSatisfy` (< termSize term)

    describe "bounded LTA sources in ordinary generators" $ do
        it "reads an automaton the engine can count without the solver" $ do
            let boolean = pairsWith $ semanticConstraint $ Not same
            forM_ [(2, recursiveLists), (1, ambiguousTerms), (2, boolean)] $ \(depth, automaton) -> do
                let source = LTAGen.fromAutomatonUpToDepth depth automaton
                void (LTAGen.support source) `shouldBe` Right ()
                compiled <- LTAGen.compileWith unusedEntailment source >>= either (fail . show) pure
                termsOf compiled `shouldBe` termsOf source
                denotationAtMost unusedEntailment depth automaton `shouldDenote` termsOf compiled
                values compiled `shouldBe` termsOf compiled

        it "defers an automaton whose guards need the solver" $ do
            let source = LTAGen.fromAutomatonUpToDepth 2 $ pairsWith $ semanticConstraint $ Satisfies (path [0]) true
            void (LTAGen.support source) `shouldBe` Left LTAGen.SourceRequiresCompilation
            LTAGen.cardinality source `shouldBe` Left LTAGen.SourceRequiresCompilation
            compiled <- LTAGen.compileWith (Entailment $ \_ _ -> pure Yes) source >>= either (fail . show) pure
            LTAGen.cardinality compiled `shouldBe` Right 9

        it "keeps unique imported terms and repeated pool draws with their weights" $ do
            imported <- compileBounded unusedEntailment 1 ambiguousTerms
            let weighted =
                    LTAGen.frequency
                        [ (2, LTAGen.namedPool [LTAGen.Refined (7 :: Int) "draw" (const true), LTAGen.Refined 7 "draw" (const true)])
                        , (5, LTAGen.leaf 7 "other" (const true))
                        ]
            let source = fmap (const (7 :: Int)) $ LTAGen.fromAutomatonUpToDepth 1 ambiguousTerms
                generator =
                    LTAGen.node "combined" $
                        (,) <$> source <*> weighted
            compiled <- LTAGen.compileWith unusedEntailment generator >>= either (fail . show) pure
            LTAGen.cardinality compiled `shouldBe` Right 9
            values compiled `shouldBe` replicate 9 (7, 7)
            map snd (massesByRank compiled) `shouldBe` concat (replicate 3 [1 % 21, 1 % 21, 5 % 21])
            termsOf compiled
                `shouldBe` [ Tree.Node (LiquidSymbol "combined" true) [term, Tree.Node (LiquidSymbol symbol true) []]
                           | term <- termsOf imported
                           , symbol <- ["draw", "draw", "other"]
                           ]
            length (nub $ termsOf compiled) `shouldBe` 6

        it "retains an ordinary alternative when an imported bound is empty" $
            forM_ [LTAGen.fromAutomatonUpToDepth 0 EmptyNode, LTAGen.fromAutomatonUpToDepth (-1) recursiveLists] $ \source -> do
                emptyResult <- LTAGen.compileWith unusedEntailment source
                (emptyResult >>= LTAGen.cardinality) `shouldBe` Left LTAGen.EmptyGenerator
                let alternatives =
                        LTAGen.oneof [fmap (const (7 :: Int)) source, LTAGen.leaf 9 "ordinary" (const true)]
                compiled <- LTAGen.compileWith unusedEntailment alternatives >>= either (fail . show) pure
                LTAGen.cardinality compiled `shouldBe` Right 1
                LTAGen.unrank compiled 0 `shouldBe` Right 9

        it "skips a rejected deferred import and keeps the branch weights" $ do
            let rejected =
                    LTAGen.refinedNode "dead" (const true) Bottom
                        $ fmap (const (7 :: Int))
                        $ LTAGen.fromAutomatonUpToDepth 1 ambiguousTerms
            let alternatives =
                    LTAGen.frequency
                        [ (3, LTAGen.leaf 9 "ordinary" (const true))
                        , (11, rejected)
                        , (5, LTAGen.leaf 8 "later" (const true))
                        ]
            compiled <-
                LTAGen.compileWith unusedEntailment alternatives
                    >>= either (fail . show) pure
            LTAGen.cardinality compiled `shouldBe` Right 2
            values compiled `shouldBe` [9, 8]
            massesByRank compiled `shouldBe` [(0, 3 % 8), (1, 5 % 8)]

        it "skips deferred imports beside a known-empty child in either position" $ do
            let deferred = LTAGen.fromAutomatonUpToDepth 1 ambiguousTerms
            forM_ [LTAGen.namedPool [], LTAGen.fromAutomatonUpToDepth (-1) ambiguousTerms] $ \emptySource ->
                forM_ [(deferred, emptySource), (emptySource, deferred)] $ \(left, right) -> do
                    let generator =
                            LTAGen.node "empty-pair" $
                                (,) <$> left <*> right
                    result <- LTAGen.compileWith unusedEntailment generator
                    (result >>= LTAGen.cardinality) `shouldBe` Left LTAGen.EmptyGenerator

        it "checks root, nested, and missing observations across an imported boundary" $
            withZ3 [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)] $ \solver -> do
                let zero = variable "v" .== 0
                    boxed =
                        Node
                            [ Transition "a" zero [] unconstrainedConstraint
                            , Transition "a" (variable "v" .== 1) [] unconstrainedConstraint
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
                    let generator = LTAGen.refinedNode "host" (const true) (semanticConstraint guard) $ LTAGen.fromAutomatonUpToDepth 1 imported
                        oracle = Node [Transition "host" true [imported] $ semanticConstraint guard]
                    compiled <- LTAGen.compileWith solver generator >>= either (fail . show) pure
                    LTAGen.cardinality compiled `shouldBe` Right count
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
                    source = LTAGen.fromAutomatonUpToDepth 2 automaton
                denotationAtMost unusedEntailment 2 automaton `shouldDenote` expected
                result <- LTAGen.compileWith unusedEntailment source
                case result of
                    Left (LTAGen.ResidualGuard residual) -> residual `shouldBe` scoped
                    Left err -> expectationFailure $ "unexpected scoped equality failure: " <> show err
                    Right _ -> expectationFailure "an unsupported scoped equality was silently compiled"

        it "keeps a large imported language compact without forcing source values" $ do
            result <- timeout 60000000 $ do
                let source = fmap (const $ error "imported value was forced") $ LTAGen.fromAutomatonUpToDepth 70 recursiveLists
                    ordinary = fmap (const $ error "ordinary value was forced") $ LTAGen.leaf () "ordinary" (const true)
                    generator =
                        LTAGen.node "combined" $
                            (\_ _ -> (42 :: Int)) <$> source <*> ordinary
                    total = 2 ^ (71 :: Int) - 1
                compiled <- LTAGen.compileWith unusedEntailment generator >>= either (fail . show) pure
                LTAGen.cardinality compiled `shouldBe` Right total
                supportNodes compiled `shouldSatisfy` (\count -> count > 0 && count < 500)
                LTAGen.unrank compiled 0 `shouldBe` Right 42
                LTAGen.unrank compiled (total - 1) `shouldBe` Right 42
            result `shouldBe` Just ()

        it "maps a shared depth-70 singleton beside an ordinary child without expanding its witness" $ do
            result <- timeout 60000000 $ do
                let automaton = sharedBinaryTerm unconstrainedConstraint
                    rootSymbol (Tree.Node (LiquidSymbol symbol _) _) = symbol
                    source = fmap rootSymbol $ LTAGen.fromAutomatonUpToDepth 71 automaton
                    generator =
                        LTAGen.node "combined" $
                            (,) <$> source <*> LTAGen.leaf (7 :: Int) "ordinary" (const true)
                compiled <- LTAGen.compileWith unusedEntailment generator >>= either (fail . show) pure
                LTAGen.cardinality compiled `shouldBe` Right 1
                supportNodes compiled `shouldSatisfy` (\count -> count > 0 && count < 500)
                LTAGen.unrank compiled 0 `shouldBe` Right ("root", 7)
            result `shouldBe` Just ()

        it "counts positive and negative equality without expanding huge terms" $ do
            forM_
                [ (equalityConstraint $ mkEqConstraints [[path [0], path [1]]], Right 1)
                , (semanticConstraint $ Not same, Left LTAGen.EmptyGenerator)
                ]
                $ \(constraint, expected) -> do
                    result <-
                        timeout 60000000 $ LTAGen.compileWith unusedEntailment $ LTAGen.fromAutomatonUpToDepth 71 $ sharedBinaryTerm constraint
                    fmap (>>= LTAGen.cardinality) result `shouldBe` Just expected

    describe "bounded symbolic automaton compilation" $ do
        it "counts and replays exponential nested equality and disequality languages" $ do
            let nested = Same (path [0, 0]) (path [1, 0])
                count = 2 ^ (70 :: Int) - 1
            forM_ [(nested, count), (Not nested, count * (count - 1)), (Or [nested, Not nested], count * count)] $ \(guard, expected) -> do
                completed <- timeout 20000000 $ do
                    let automaton = largeBoxedLists $ semanticConstraint guard
                    compiled <- compileBounded unusedEntailment 71 automaton
                    LTAGen.cardinality compiled `shouldBe` Right expected
                    forM_ [0, expected - 1] $ \rank -> do
                        generated <- either (fail . show) pure $ LTAGen.unrank compiled rank
                        accepts unusedEntailment automaton generated >>= (`shouldBe` Yes)
                completed `shouldBe` Just ()

        it "groups nested observations of an exponential equality import without decoding values" $ do
            completed <- timeout 20000000 $ do
                let automaton = largeBoxedLists $ equalityConstraint $ mkEqConstraints [[path [0, 0], path [1, 0]]]
                    source = fmap (const $ error "symbolic grouping decoded a source value") $ LTAGen.fromAutomatonUpToDepth 71 automaton
                    generator =
                        LTAGen.refinedNode "host" (const true) (semanticConstraint $ Satisfies (path [0, 0, 0, 0]) true) $
                            fmap (const (42 :: Int)) source
                    solver = Entailment $ \_ _ -> pure Yes
                compiled <- LTAGen.compileWith solver generator >>= either (fail . show) pure
                LTAGen.cardinality compiled `shouldBe` Right (2 ^ (70 :: Int) - 2)
                forM_ [0, 2 ^ (70 :: Int) - 3] $ \rank ->
                    LTAGen.unrank compiled rank `shouldBe` Right 42
            completed `shouldBe` Just ()

        it "preserves missing-path semantics in reflexive Boolean equality" $ do
            let reflexive = Same (path [0, 0]) (path [0, 0])
            forM_ [reflexive, Not reflexive] $ \guard -> do
                let automaton = optionalDescendant guard
                compiled <- compileBounded unusedEntailment 2 automaton
                LTAGen.cardinality compiled `shouldBe` Right 1
                denotationAtMost unusedEntailment 2 automaton `shouldDenote` termsOf compiled

        it "matches the bounded denotation of recursive two-atom lists" $
            forM_ [(0, 1), (1, 3), (2, 7)] $ \(depth, count) -> do
                compiled <- compileBounded unusedEntailment depth recursiveLists
                LTAGen.cardinality compiled `shouldBe` Right count
                denotationAtMost unusedEntailment depth recursiveLists `shouldDenote` termsOf compiled
                repeated <- compileBounded unusedEntailment depth recursiveLists
                termsOf repeated `shouldBe` termsOf compiled
                checkShrinks unusedEntailment recursiveLists compiled

        it "counts mutually recursive and unproductive nodes at the bound" $ do
            let productive = Mu $ \outer -> Node [plain "nil" [], plain "left" [Node [plain "right" [outer]]]]
            compiled <- compileBounded unusedEntailment 2 productive
            LTAGen.cardinality compiled `shouldBe` Right 2
            let unproductive = Mu $ \self -> Node [plain "loop" [self]]
            result <- LTAGen.compileWith unusedEntailment $ LTAGen.fromAutomatonUpToDepth 3 unproductive
            (result >>= LTAGen.cardinality) `shouldBe` Left LTAGen.EmptyGenerator

        it "treats a negative bound as an empty language" $ do
            result <- LTAGen.compileWith unusedEntailment $ LTAGen.fromAutomatonUpToDepth (-1) recursiveLists
            (result >>= LTAGen.cardinality) `shouldBe` Left LTAGen.EmptyGenerator

        it "deduplicates accepting runs and preserves replay order" $ do
            compiled <- compileBounded unusedEntailment 1 ambiguousTerms
            LTAGen.cardinality compiled `shouldBe` Right 3
            denotationAtMost unusedEntailment 1 ambiguousTerms `shouldDenote` termsOf compiled
            checkShrinks unusedEntailment ambiguousTerms compiled
            mapped <- compileBoundedWith unusedEntailment (\_ _ _ -> ()) 1 ambiguousTerms
            (mapped >>= LTAGen.cardinality) `shouldBe` Right 3
            fmap termsOf mapped `shouldBe` Right (termsOf compiled)

        it "retains distinct refinements when symbols and values coincide" $ do
            let automaton = Node [plain "a" [], Transition "a" (variable "v" .== 0) [] unconstrainedConstraint]
            result <- compileBoundedWith unusedEntailment (\_ _ _ -> ()) 0 automaton
            (result >>= LTAGen.cardinality) `shouldBe` Right 2

        it "handles negated and disjunctive equality symbolically" $
            forM_ [Not same, Or [same, Not same]] $ \guard -> do
                let automaton = pairsWith $ semanticConstraint guard
                compiled <- compileBounded unusedEntailment 2 automaton
                denotationAtMost unusedEntailment 2 automaton `shouldDenote` termsOf compiled
                checkShrinks unusedEntailment automaton compiled

        it "keeps both siblings equal when shrinking positive equality" $ do
            let automaton = pairsWith $ equalityConstraint $ mkEqConstraints [[path [0], path [1]]]
            compiled <- compileBounded unusedEntailment 2 automaton
            LTAGen.cardinality compiled `shouldBe` Right 3
            checkShrinks unusedEntailment automaton compiled
            wrappedPair <-
                rankOf compiled
                    $ Tree.Node (LiquidSymbol "pair" true)
                    $ replicate 2
                    $ Tree.Node (LiquidSymbol "wrap" true) [Tree.Node (LiquidSymbol "a" true) []]
            LTAGen.smallerMembers compiled wrappedPair `shouldSatisfy` (not . null)

        it "evaluates absent paths inside negation and disjunction" $
            forM_ [(Not missing, 1), (Or [Top, missing], 2)] $ \(guard, count) -> do
                let automaton = optionalDescendant guard
                    solver = Entailment $ \_ _ -> pure Yes
                compiled <- compileBounded solver 2 automaton
                LTAGen.cardinality compiled `shouldBe` Right count
                denotationAtMost solver 2 automaton `shouldDenote` termsOf compiled

        it "reports unavailable compound actual identities without changing the core language" $
            withZ3 [(Fixpoint.symbol name, Fixpoint.FInt) | name <- ["v", "x", "y", "app", "known"] :: [String]] $ \solver -> do
                let guard =
                        Substitute
                            [Substitution (path [0]) (path [2]), Substitution (path [1]) (path [3])]
                            (Satisfies (path []) $ variable "x" .== variable "y")
                    known = Node [Transition "known" (variable "v" .== 0) [] unconstrainedConstraint, plain "app" [atoms]]
                    automaton =
                        Node
                            [ Transition "pair" true [known, known, Node [plain "x" []], Node [plain "y" []]] $
                                semanticConstraint guard
                            ]
                denotationAtMost solver 2 automaton >>= (\result -> fmap length result `shouldBe` Right 3)
                result <- LTAGen.compileWith solver $ LTAGen.fromAutomatonUpToDepth 2 automaton
                case result of
                    Left (LTAGen.ResidualGuard residual) -> residual `shouldBe` guard
                    Left err -> expectationFailure $ show err
                    Right _ -> expectationFailure "unavailable compound identity was silently compiled"

        it "reports an undecidable full-term guard" $ do
            let automaton = pairsWith $ semanticConstraint $ Satisfies (path [0]) true
            result <- LTAGen.compileWith (Entailment $ \_ _ -> pure Unknown) $ LTAGen.fromAutomatonUpToDepth 2 automaton
            (result >>= LTAGen.cardinality) `shouldBe` Left LTAGen.SolverUnknown

        it "uses the solver only during compilation" $ do
            calls <- newIORef (0 :: Int)
            let solver = Entailment $ \_ _ -> modifyIORef' calls (+ 1) >> pure Yes
                automaton = pairsWith $ semanticConstraint $ Satisfies (path [0]) true
            compiled <- compileBounded solver 2 automaton
            before <- readIORef calls
            before `shouldSatisfy` (> 0)
            length (termsOf compiled) `shouldBe` 9
            length (concatMap (LTAGen.shrinkRank compiled) [0 .. 8]) `shouldSatisfy` (> 0)
            readIORef calls >>= (`shouldBe` before)

        it "keeps bounded shared graphs compact without forcing a huge witness" $ do
            let automaton = Node [plain "root" [forks !! 70]]
            compiled <-
                compileBoundedWith unusedEntailment (\symbol _ _ -> symbol) 71 automaton
                    >>= either (fail . show) pure
            LTAGen.cardinality compiled `shouldBe` Right 1
            LTAGen.unrank compiled 0 `shouldBe` Right "root"
            LTAGen.shrinkRank compiled 0 `shouldBe` []

        it "orders the ranks of a shared graph by its explicit view" $ do
            let automaton = Node [plain "root" [forks !! 2]]
            compiled <- compileBounded unusedEntailment 3 automaton
            termsOf compiled `shouldMatchList` [Tree.Node (LiquidSymbol "root" true) [fork 2]]
  where
    same = Same (path [0]) (path [1])
    missing = Satisfies (path [0, 0]) true
    variable :: String -> Expr
    variable name = toExpr $ Fixpoint.EVar $ Fixpoint.symbol (name :: String)
    fork :: Int -> Tree.Tree LiquidSymbol
    fork 0 = Tree.Node (LiquidSymbol "a" true) []
    fork height = Tree.Node (LiquidSymbol "fork" true) [fork (height - 1), fork (height - 1)]

{- | Compare a bounded denotation with the terms it should contain. The
denotation is a set, so order is not compared.
-}
shouldDenote :: IO (Either DenotationError [Tree.Tree LiquidSymbol]) -> [Tree.Tree LiquidSymbol] -> IO ()
shouldDenote denotation expected = denotation >>= \result -> fmap sort result `shouldBe` Right (sort expected)
