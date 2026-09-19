{-# LANGUAGE TypeApplications #-}

module Data.CFTA.Gen.Refinement.RecursiveGeneratorSpec (spec) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import Data.List (elemIndex)
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldMatchList, shouldReturn)

import Data.CFTA.Constraint.Equality (mkEqConstraints)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTA
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
termNodes :: Tree.Tree LiquidSymbol -> Integer
termNodes = Tree.foldTree $ \_ counts -> 1 + sum counts

unusedEntailment :: Entailment
unusedEntailment = Entailment $ \_ _ -> pure Unknown

-- | Compile the derived list grammar with unconstrained liquid annotations.
compileAtDepth :: Int -> IO (LTA.Compiled [()])
compileAtDepth depth = do
    datatype <- either (fail . show) pure $ Datatype.deriveFTA @[()]
    let annotated = Datatype.annotateDatatype (const (true, unconstrainedConstraint)) datatype
    LTA.compile unusedEntailment (LTA.fromDatatypeUpToDepth depth annotated)
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
            LTA.cardinality compiled `shouldBe` 3
            fmap LTA.generatedValue (LTA.unrank compiled 2)
                `shouldBe` Right (last $ values compiled)

        it "routes a residual equality through the symbolic ranker instead of an FTA product" $ do
            let items = Node [plain "item-a" [], plain "item-b" []]
                automaton = Node [Transition "pair" true [items, items] (equalityConstraint sameChildren)]
            result <- LTA.compileAutomaton unusedEntailment automaton
            case result of
                Left err -> expectationFailure $ show err
                Right compiled -> do
                    LTA.cardinality compiled `shouldBe` 2
                    values compiled `shouldMatchList` [pair itemA, pair itemB]

    describe "structural automaton shrinking" $ do
        it "shrinks a large rank to a later smaller transition" $ do
            compiled <- LTA.compileAutomaton unusedEntailment (largeOrSmallAutomaton 0) >>= either (fail . show) pure
            large <- rankOf compiled $ Tree.Node (LiquidSymbol "large" true) [Tree.Node (LiquidSymbol "atom" true) []]
            small <- rankOf compiled $ Tree.Node (LiquidSymbol "small" true) []
            LTA.shrinkRank compiled large `shouldBe` [small]
            LTA.shrinkRank compiled small `shouldBe` []
            LTA.shrinkRank compiled (-1) `shouldBe` []
            LTA.shrinkRank compiled 2 `shouldBe` []

        it "skips dead transitions and preserves sibling decisions in child shrinks" $ do
            compiled <- LTA.compileAutomaton unusedEntailment variablePairAutomaton >>= either (fail . show) pure
            LTA.cardinality compiled `shouldBe` 9
            let wrap leaf = Tree.Node (LiquidSymbol "wrap" true) [Tree.Node (LiquidSymbol leaf true) []]
                atom = Tree.Node (LiquidSymbol "atom" true) []
                pairOf left right = Tree.Node (LiquidSymbol "pair" true) [left, right]
            forM_ [(wrap "x", wrap "y"), (wrap "y", wrap "y")] $ \(left, right) -> do
                source <- rankOf compiled $ pairOf left right
                expected <- traverse (rankOf compiled) [pairOf atom atom, pairOf atom right, pairOf left atom]
                LTA.shrinkRank compiled source `shouldMatchList` expected
            smallest <- rankOf compiled $ pairOf atom atom
            LTA.shrinkRank compiled smallest `shouldBe` []

        it "emits only accepted terms with strictly fewer tree nodes" $ do
            compiled <- LTA.compileAutomaton unusedEntailment variablePairAutomaton >>= either (fail . show) pure
            forM_ [0 .. LTA.cardinality compiled - 1] $ \rank -> do
                source <- either (fail . show) pure $ LTA.unrank compiled rank
                forM_ (LTA.shrinkRank compiled rank) $ \candidate -> do
                    target <- either (fail . show) pure $ LTA.unrank compiled candidate
                    let term = LTA.generatedTerm target
                    (termNodes term < termNodes (LTA.generatedTerm source)) `shouldBe` True
                    accepts unusedEntailment variablePairAutomaton term `shouldReturn` Yes

        it "keeps graph shrinks independent of generated and mapped values" $ do
            let unavailableValue _ _ _ = error "shrinking forced a generated value" :: ()
            compiled <-
                LTA.compileAutomatonWith unusedEntailment unavailableValue (largeOrSmallAutomaton 0)
                    >>= either (fail . show) pure
            large <- rankOf compiled $ Tree.Node (LiquidSymbol "large" true) [Tree.Node (LiquidSymbol "atom" true) []]
            small <- rankOf compiled $ Tree.Node (LiquidSymbol "small" true) []
            LTA.shrinkRank compiled large `shouldBe` [small]
            LTA.shrinkRank (LTA.mapCompiled (const False) compiled) large `shouldBe` [small]

        it "does not expand huge shared trees with uniform node counts" $ do
            completed <- timeout 60000000 $ do
                compiled <-
                    LTA.compileAutomatonWith unusedEntailment selectedTag (sharedSubtreeAutomaton 50 "b")
                        >>= either (fail . show) pure
                evaluate $
                    Set.fromList (values compiled) == Set.fromList ["a", "b"]
                        && null (LTA.shrinkRank compiled 0)
                        && null (LTA.shrinkRank compiled 1)
            completed `shouldBe` Just True

        it "counts shared selected runs beyond machine-sized node counts" $ do
            completed <- timeout 60000000 $ do
                compiled <-
                    LTA.compileAutomatonWith unusedEntailment (\symbol _ _ -> symbol) (largeOrSmallAutomaton 70)
                        >>= either (fail . show) pure
                let large = maybe (-1) toInteger $ elemIndex "large" $ values compiled
                    small = maybe (-1) toInteger $ elemIndex "small" $ values compiled
                evaluate $
                    Set.fromList (values compiled) == Set.fromList ["large", "small"]
                        && LTA.shrinkRank compiled large == [small]
                        && null (LTA.shrinkRank compiled small)
            completed `shouldBe` Just True

    describe "finite automaton overlap checks" $ do
        it "counts shared subtrees without expanding their repeated node pairs" $ do
            result <- LTA.compileAutomatonWith unusedEntailment selectedTag (sharedSubtreeAutomaton 50 "b")
            case result of
                Left err -> expectationFailure $ show err
                Right compiled -> do
                    LTA.cardinality compiled `shouldBe` 2
                    values compiled `shouldMatchList` ["a", "b"]

        it "keeps the term ranks of a small shared automaton" $ do
            let automaton = sharedSubtreeAutomaton 3 "b"
            complete <- LTA.compile unusedEntailment $ LTA.fromLTA 5 automaton
            counted <- LTA.compileAutomaton unusedEntailment automaton
            fmap LTA.cardinality counted `shouldBe` Right 2
            fmap values counted `shouldBe` fmap values complete

        it "deduplicates overlapping alternatives without expanding their shared subtrees" $ do
            result <- LTA.compileAutomatonWith unusedEntailment selectedTag (sharedSubtreeAutomaton 50 "a")
            fmap LTA.cardinality result `shouldBe` Right 1

        it "does not count an alternative with an empty child node" $ do
            let automaton = Node [plain "wrap" [EmptyNode], plain "wrap" [Node [plain "item-a" []]]]
            result <- LTA.compileAutomaton unusedEntailment automaton
            fmap LTA.cardinality result `shouldBe` Right 1
            fmap values result `shouldBe` Right [Tree.Node (LiquidSymbol "wrap" true) [itemA]]

        it "reports an empty root without an overlap" $ do
            result <- LTA.compileAutomaton unusedEntailment EmptyNode
            fmap LTA.cardinality result `shouldBe` Left LTA.EmptyGenerator
  where
    sameChildren = mkEqConstraints [[path [0], path [1]]]
    itemA = Tree.Node (LiquidSymbol "item-a" true) []
    itemB = Tree.Node (LiquidSymbol "item-b" true) []
    pair item = Tree.Node (LiquidSymbol "pair" true) [item, item]

    selectedTag symbol _ children = case (symbol, children) of
        ("pair", [_, tag]) -> tag
        ("wrap", [tag]) -> tag
        _ -> symbol

    values compiled =
        [ LTA.generatedValue generated
        | rank <- [0 .. LTA.cardinality compiled - 1]
        , Right generated <- [LTA.unrank compiled rank]
        ]

    rankOf compiled term =
        case elemIndex
            term
            [ LTA.generatedTerm generated | rank <- [0 .. LTA.cardinality compiled - 1], Right generated <- [LTA.unrank compiled rank]
            ] of
            Just rank -> pure $ toInteger rank
            Nothing -> fail $ "term is not in the compiled language: " <> show term
