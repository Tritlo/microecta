{-# LANGUAGE TypeApplications #-}

module Data.CFTA.Gen.Refinement.RecursiveGeneratorSpec (spec) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import Data.List (elemIndex)
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldMatchList, shouldReturn)

import Data.CFTA.Equality.Constraint (mkEqConstraints)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Gen.Refinement.TestSupport (ranks, termsOf, values)
import qualified Data.CFTA.Generic as Datatype
import Data.CFTA.Refinement (
    Automaton,
    Entailment (Entailment),
    LiquidSymbol (LiquidSymbol),
    Node (EmptyNode, Node),
    Symbol,
    Transition,
    Verdict (Unknown, Yes),
    accepts,
    equalityConstraint,
    path,
    unconstrainedConstraint,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (true)

-- | An unrefined, unconstrained transition.
plain :: Symbol -> [Automaton] -> Transition
plain symbol children = Transition symbol true children unconstrainedConstraint

-- | Complete binary fork trees over one atom, by height.
forks :: [Automaton]
forks = Node [plain "atom" []] : [Node [plain "fork" [shorter, shorter]] | shorter <- forks]

-- | Two compact shared subtrees with equal languages and distinct tags.
sharedSubtreeAutomaton :: Int -> Symbol -> Automaton
sharedSubtreeAutomaton depth rightLeaf =
    Node
        [ plain "pair" [forks !! depth, Node [plain "wrap" [Node [plain "a" []]]]]
        , plain "pair" [forks !! depth, Node [plain "wrap" [Node [plain rightLeaf []]]]]
        ]

-- | A large shared tree followed by a smaller term in the same rank space.
largeOrSmallAutomaton :: Int -> Automaton
largeOrSmallAutomaton depth = Node [plain "large" [forks !! depth], plain "small" []]

-- | Two independently ranked child choices and one dead root alternative.
variablePairAutomaton :: Automaton
variablePairAutomaton = Node [plain "missing" [EmptyNode], plain "pair" [choice, choice]]
  where
    choice = Node [plain "wrap" [Node [plain "x" [], plain "y" []]], plain "atom" []]

-- | Count the physical nodes of one small test term.
termSize :: Tree.Tree LiquidSymbol -> Int
termSize = length . Tree.flatten

unusedEntailment :: Entailment
unusedEntailment = Entailment $ \_ _ -> pure Unknown

-- | Compile the derived list grammar with unconstrained liquid annotations.
compileAtDepth :: Int -> IO (LTAGen.LTAGen [()])
compileAtDepth depth = do
    datatype <- either (fail . show) pure $ Datatype.deriveFTA @[()]
    let annotated = Datatype.annotateDatatype (const (true, unconstrainedConstraint)) datatype
    LTAGen.compile unusedEntailment (LTAGen.fromDatatypeUpToDepth depth annotated)
        >>= either (fail . show) pure

spec :: Spec
spec = do
    describe "bounded generation from recursive LTAs" $ do
        it "contains only the base transition at depth zero" $ do
            compiled <- compileAtDepth 0
            values compiled `shouldBe` [[]]

        it "unfolds every recursive list through the requested depth" $ do
            compiled <- compileAtDepth 2
            values compiled `shouldBe` [[], [()], [(), ()]]

        it "keeps deterministic replay ranks after unfolding" $ do
            compiled <- compileAtDepth 2
            LTAGen.cardinality compiled `shouldBe` Right 3
            LTAGen.unrank compiled 2
                `shouldBe` Right (last $ values compiled)

        it "counts a residual equality symbolically instead of as an FTA product" $ do
            let items = Node [plain "item-a" [], plain "item-b" []]
                automaton = Node [Transition "pair" true [items, items] (equalityConstraint sameChildren)]
            result <- compileAutomaton automaton
            case result of
                Left err -> expectationFailure $ show err
                Right compiled -> do
                    LTAGen.cardinality compiled `shouldBe` Right 2
                    values compiled `shouldMatchList` [pair itemA, pair itemB]

    describe "structural automaton shrinking" $ do
        it "lists the members with fewer nodes than a rank's member" $ do
            compiled <- compileAutomaton (largeOrSmallAutomaton 0) >>= either (fail . show) pure
            large <- rankOf compiled $ Tree.Node (LiquidSymbol "large" true) [Tree.Node (LiquidSymbol "atom" true) []]
            small <- rankOf compiled $ Tree.Node (LiquidSymbol "small" true) []
            map fst (LTAGen.smallerMembers compiled large) `shouldBe` [small]
            LTAGen.smallerMembers compiled small `shouldBe` []
            LTAGen.smallerMembers compiled (-1) `shouldBe` []
            LTAGen.smallerMembers compiled 2 `shouldBe` []

        it "skips dead transitions and lists every smaller pair" $ do
            compiled <- compileAutomaton variablePairAutomaton >>= either (fail . show) pure
            LTAGen.cardinality compiled `shouldBe` Right 9
            let wrap leaf = Tree.Node (LiquidSymbol "wrap" true) [Tree.Node (LiquidSymbol leaf true) []]
                atom = Tree.Node (LiquidSymbol "atom" true) []
                pairOf left right = Tree.Node (LiquidSymbol "pair" true) [left, right]
            source <- rankOf compiled $ pairOf (wrap "x") (wrap "y")
            expected <-
                traverse
                    (rankOf compiled)
                    [pairOf atom atom, pairOf atom (wrap "x"), pairOf atom (wrap "y"), pairOf (wrap "x") atom, pairOf (wrap "y") atom]
            map fst (LTAGen.smallerMembers compiled source) `shouldMatchList` expected
            smallest <- rankOf compiled $ pairOf atom atom
            LTAGen.smallerMembers compiled smallest `shouldBe` []

        it "emits only accepted terms with strictly fewer tree nodes" $ do
            compiled <- compileAutomaton variablePairAutomaton >>= either (fail . show) pure
            forM_ (zip (ranks compiled) (termsOf compiled)) $ \(rank, source) ->
                forM_ (LTAGen.smallerMembers compiled rank) $ \(candidate, term) -> do
                    term `shouldBe` termsOf compiled !! fromInteger candidate
                    (termSize term < termSize source) `shouldBe` True
                    accepts unusedEntailment variablePairAutomaton term `shouldReturn` Yes

        it "keeps shrinks independent of generated and mapped values" $ do
            let unavailableValue _ _ _ = error "shrinking forced a generated value" :: ()
            compiled <-
                compileAutomatonWith unavailableValue (largeOrSmallAutomaton 0)
                    >>= either (fail . show) pure
            large <- rankOf compiled $ Tree.Node (LiquidSymbol "large" true) [Tree.Node (LiquidSymbol "atom" true) []]
            small <- rankOf compiled $ Tree.Node (LiquidSymbol "small" true) []
            map fst (LTAGen.smallerMembers compiled large) `shouldBe` [small]
            map fst (LTAGen.smallerMembers (fmap (const False) compiled) large) `shouldBe` [small]

        it "does not expand huge shared trees with uniform node counts" $ do
            completed <- timeout 60000000 $ do
                compiled <-
                    compileAutomatonWith selectedTag (sharedSubtreeAutomaton 50 "b")
                        >>= either (fail . show) pure
                evaluate $
                    Set.fromList (values compiled) == Set.fromList ["a", "b"]
                        && null (LTAGen.shrinkRank compiled 0)
                        && all (< 1) (LTAGen.shrinkRank compiled 1)
            completed `shouldBe` Just True

        it "counts shared selected runs beyond machine-sized node counts" $ do
            completed <- timeout 60000000 $ do
                compiled <-
                    compileAutomatonWith (\symbol _ _ -> symbol) (largeOrSmallAutomaton 70)
                        >>= either (fail . show) pure
                evaluate $
                    Set.fromList (values compiled) == Set.fromList ["large", "small"]
                        && null (LTAGen.shrinkRank compiled 0)
            completed `shouldBe` Just True

    describe "finite automaton overlap checks" $ do
        it "counts shared subtrees without expanding their repeated node pairs" $ do
            result <- compileAutomatonWith selectedTag (sharedSubtreeAutomaton 50 "b")
            case result of
                Left err -> expectationFailure $ show err
                Right compiled -> do
                    LTAGen.cardinality compiled `shouldBe` Right 2
                    values compiled `shouldMatchList` ["a", "b"]

        it "keeps the term ranks of a small shared automaton" $ do
            let automaton = sharedSubtreeAutomaton 3 "b"
            complete <- LTAGen.compile unusedEntailment $ LTAGen.fromAutomatonUpToDepth 5 automaton
            counted <- compileAutomaton automaton
            (counted >>= LTAGen.cardinality) `shouldBe` Right 2
            fmap values counted `shouldBe` fmap values complete

        it "deduplicates overlapping alternatives without expanding their shared subtrees" $ do
            result <- compileAutomatonWith selectedTag (sharedSubtreeAutomaton 50 "a")
            (result >>= LTAGen.cardinality) `shouldBe` Right 1

        it "does not count an alternative with an empty child node" $ do
            let automaton = Node [plain "wrap" [EmptyNode], plain "wrap" [Node [plain "item-a" []]]]
            result <- compileAutomaton automaton
            (result >>= LTAGen.cardinality) `shouldBe` Right 1
            fmap values result `shouldBe` Right [Tree.Node (LiquidSymbol "wrap" true) [itemA]]

        it "reports an empty root without an overlap" $ do
            result <- compileAutomaton EmptyNode
            (result >>= LTAGen.cardinality) `shouldBe` Left LTAGen.EmptyGenerator
  where
    sameChildren = mkEqConstraints [[path [0], path [1]]]
    itemA = Tree.Node (LiquidSymbol "item-a" true) []
    itemB = Tree.Node (LiquidSymbol "item-b" true) []
    pair item = Tree.Node (LiquidSymbol "pair" true) [item, item]

    selectedTag symbol _ children = case (symbol, children) of
        ("pair", [_, tag]) -> tag
        ("wrap", [tag]) -> tag
        _ -> symbol

    compileAutomaton = LTAGen.compile unusedEntailment . LTAGen.fromAutomaton

    -- Fold each accepted term into a value as it is selected.
    compileAutomatonWith build =
        LTAGen.compile unusedEntailment
            . fmap (Tree.foldTree $ \(LiquidSymbol symbol refinement) -> build symbol refinement)
            . LTAGen.fromAutomaton

    rankOf compiled term =
        case elemIndex term (termsOf compiled) of
            Just rank -> pure $ toInteger rank
            Nothing -> fail $ "term is not in the compiled language: " <> show term
