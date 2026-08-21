{-# LANGUAGE OverloadedStrings #-}

-- | Recursive generators and generators read from an existing automaton.
module Data.ECTA.RecursiveGenSpec (spec) where

import Control.Exception (evaluate)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Ratio ((%))
import qualified Data.Set as Set
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Gen as QCGen
import qualified Test.QuickCheck.Random as QCRandom

import Data.ECTA (
    Edge (Edge),
    Node (Node),
    createMu,
    getAllTerms,
    mkEdge,
    nodeCount,
    nodeRepresents,
    numNestedMu,
 )
import Data.ECTA.Gen.QuickCheck (Args (..), ECTAGen, ECTAGenError (..), Sig (..))
import qualified Data.ECTA.Gen.QuickCheck as ECTAGen
import Data.ECTA.Paths (mkEqConstraints, path)
import Data.ECTA.Term (Term)

-- | A binary tree over three leaf values, defined by its own language.
data Tree = Leaf Int | Branch Tree Tree
    deriving (Eq, Ord, Show)

data Coin = Heads | Tails
    deriving (Eq, Ord, Show)

trees :: ECTAGen Tree
trees = ECTAGen.recur $ \self ->
    ECTAGen.oneof
        [ Leaf <$> ECTAGen.elements [0 .. 2]
        , Branch <$> self <*> self
        ]

-- | The size of a tree member: its number of source choices.
leaves :: Tree -> Int
leaves (Leaf _) = 1
leaves (Branch left right) = leaves left + leaves right

-- | Members of size at most four, the bound used throughout.
boundedTrees :: ECTAGen Tree
boundedTrees = ECTAGen.upToSize 4 trees

-- | Number of tree members of size at most four.
boundedTreeCount :: Integer
boundedTreeCount = 471

-- | A finite automaton whose language is easy to state independently.
finiteAutomaton :: Node
finiteAutomaton =
    Node
        [ Edge "a" []
        , Edge "b" []
        , Edge "f" [Node [Edge "a" [], Edge "b" []]]
        ]

-- | A recursive automaton: ground types under one type constructor and one arrow.
typeAutomaton :: Node
typeAutomaton =
    createMu $ \recursive ->
        Node
            [ Edge "baseType" []
            , Edge "->" [recursive, recursive]
            , Edge "Maybe" [recursive]
            ]

-- | An automaton whose edge carries an equality constraint.
constrainedAutomaton :: Node
constrainedAutomaton =
    Node
        [ mkEdge
            "pair"
            [finiteAutomaton, finiteAutomaton]
            (mkEqConstraints [[path [0], path [1]]])
        ]

spec :: Spec
spec = do
    describe "recursive generators" $ do
        it "counts every size class of an unbounded language" $ do
            traverse (ECTAGen.countAtSize trees) [1 .. 5]
                `shouldBe` Right [3, 9, 54, 405, 3402]
            ECTAGen.cardinality trees `shouldBe` Left UnboundedGenerator

        it "declares one key for an unbounded language without enumerating it" $ do
            let family = ECTAGen.keyed True trees
                selected = ECTAGen.atKey True family
            ECTAGen.sizes (ECTAGen.groupBy leaves trees)
                `shouldBe` Left UnboundedGenerator
            ECTAGen.sizes family `shouldBe` Left UnboundedGenerator
            traverse (ECTAGen.countAtSize selected) [1 .. 5]
                `shouldBe` Right [3, 9, 54, 405, 3402]
            traverse (ECTAGen.unrank selected) [0 .. 50]
                `shouldBe` traverse (ECTAGen.unrank trees) [0 .. 50]
            fmap numNestedMu (ECTAGen.support selected) `shouldBe` Right 1
            ECTAGen.countAtSize (ECTAGen.atKey False family) 1
                `shouldBe` Left EmptyGenerator
            ECTAGen.smallest selected `shouldBe` Right (Just $ Leaf 0)
            ECTAGen.smallest (ECTAGen.atKey False family) `shouldBe` Right Nothing

        it "reports exact retained-key masses at one recursive size" $ do
            let oneLeafTree = ECTAGen.recur $ \self ->
                    ECTAGen.oneof
                        [ Leaf <$> ECTAGen.elements [0]
                        , Branch <$> self <*> self
                        ]
                family :: ECTAGen.Grouped String Tree
                family =
                    ECTAGen.oneofGrouped
                        [ ECTAGen.keyed "three leaves" trees
                        , ECTAGen.keyed "one leaf" oneLeafTree
                        ]
            ECTAGen.massesAtSize family 0 `shouldBe` Right mempty
            ECTAGen.countsAtSize family 1
                `shouldBe` Right
                    ( Map.fromList
                        [ ("one leaf", 1)
                        , ("three leaves", 3)
                        ]
                    )
            ECTAGen.massesAtSize family 1
                `shouldBe` Right
                    ( Map.fromList
                        [ ("one leaf", 1 % 4)
                        , ("three leaves", 3 % 4)
                        ]
                    )
            ECTAGen.massesAtSize family 2
                `shouldBe` Right
                    ( Map.fromList
                        [ ("one leaf", 1 % 10)
                        , ("three leaves", 9 % 10)
                        ]
                    )
            ECTAGen.countsAtSize family 2
                `shouldBe` Right
                    ( Map.fromList
                        [ ("one leaf", 1)
                        , ("three leaves", 9)
                        ]
                    )

        it "bounds the language to its members of at most one size" $ do
            ECTAGen.cardinality boundedTrees `shouldBe` Right boundedTreeCount
            ECTAGen.unrank boundedTrees boundedTreeCount
                `shouldBe` Left (SelectionOutOfRange boundedTreeCount boundedTreeCount)

        it "keeps every rank when the language is bounded" $
            [ECTAGen.unrank trees rank | rank <- [0 .. boundedTreeCount - 1]]
                `shouldBe` [ECTAGen.unrank boundedTrees rank | rank <- [0 .. boundedTreeCount - 1]]

        it "ranks members in size order, smallest first" $ do
            traverse (ECTAGen.unrank trees) [0 .. 3]
                `shouldBe` Right
                    [ Leaf 0
                    , Leaf 1
                    , Leaf 2
                    , Branch (Leaf 0) (Leaf 0)
                    ]
            [ECTAGen.sizeOfRank trees rank | rank <- [0 .. boundedTreeCount - 1]]
                `shouldBe` [ Just (leaves member)
                           | rank <- [0 .. boundedTreeCount - 1]
                           , Right member <- [ECTAGen.unrank trees rank]
                           ]

        it "decodes every rank of the bounded language to a distinct member" $
            traverse (ECTAGen.unrank trees) [0 .. boundedTreeCount - 1]
                `shouldSatisfy` either (const False) ((== fromInteger boundedTreeCount) . Set.size . Set.fromList)

        it "rejects negative recursive ranks without scanning the language" $ do
            result <- timeout 1000000 $ evaluate $ ECTAGen.unrank trees (-1)
            result `shouldBe` Just (Left $ NegativeRank (-1))

        it "supports the language with one recursive automaton" $
            fmap numNestedMu (ECTAGen.support trees) `shouldBe` Right 1

        modifyMaxSuccess (const 200) $
            it "samples within the size parameter" $
                QC.forAll (QC.resize 4 $ ECTAGen.toGen trees) $ \member ->
                    QC.counterexample (show member) $ QC.property $ leaves member <= 4

        it "reports the exact atomic distribution inside one recursive size" $ do
            let coin = ECTAGen.atomic $ ECTAGen.frequency [(9, pure Heads), (1, pure Tails)]
                words_ = ECTAGen.recur $ \rest ->
                    ECTAGen.oneof
                        [ (: []) <$> coin
                        , (:) <$> coin <*> rest
                        ]
            ECTAGen.pmfAtSize words_ 0 `shouldBe` Right []
            ECTAGen.pmfAtSize words_ 2
                `shouldBe` Right
                    [ ([Heads, Heads], 81 % 100)
                    , ([Heads, Tails], 9 % 100)
                    , ([Tails, Heads], 9 % 100)
                    , ([Tails, Tails], 1 % 100)
                    ]
            ECTAGen.pmfAtSize (length <$> words_) 2
                `shouldBe` Right [(2, 1)]

        it "rejects weighted alternatives around a recursive occurrence" $
            let weighted =
                    ECTAGen.recur $ \self ->
                        ECTAGen.frequency
                            [ (1, Leaf <$> ECTAGen.elements [0 .. 2])
                            , (3, Branch <$> self <*> self)
                            ]
             in ECTAGen.cardinality (ECTAGen.upToSize 2 weighted)
                    `shouldBe` Left WeightedRecursiveAlternatives

        it "rejects a recursion that never passes through an application" $ do
            let unguarded = ECTAGen.recur $ \self ->
                    ECTAGen.oneof [Leaf <$> ECTAGen.elements [0 .. 2], self]
                mapped = ECTAGen.recur (fmap id)
            ECTAGen.countAtSize unguarded 1 `shouldBe` Left UnguardedRecursion
            ECTAGen.countAtSize (mapped :: ECTAGen Tree) 1
                `shouldBe` Left UnguardedRecursion

        it "reports a guarded recursion with no base as empty" $ do
            let empty = ECTAGen.recur $ \self -> pure id <*> self
            smallestResult <- timeout 1000000 $ evaluate $ ECTAGen.smallest (empty :: ECTAGen Tree)
            unrankResult <- timeout 1000000 $ evaluate $ ECTAGen.unrank (empty :: ECTAGen Tree) 0
            smallestResult `shouldBe` Just (Right Nothing)
            unrankResult `shouldBe` Just (Left EmptyGenerator)

        it "reports a guarded grouped recursion with no base as empty" $ do
            let operations = ECTAGen.keyed (() :-> ()) $ pure id
                family :: ECTAGen.Grouped () ()
                family = ECTAGen.recurGrouped $ \self ->
                    ECTAGen.apply operations (self :& ANil)
            result <- timeout 1000000 $ evaluate $ ECTAGen.smallest $ ECTAGen.ungroup family
            result `shouldBe` Just (Right Nothing)

        it "starts QuickCheck at the first live recursive size" $ do
            let minimumTwo = ECTAGen.recur $ \self ->
                    ECTAGen.oneof
                        [ (\_ _ -> Leaf 0) <$> ECTAGen.elements [()] <*> ECTAGen.elements [()]
                        , Branch <$> self <*> self
                        ]
                sampled =
                    QCGen.unGen
                        (ECTAGen.toGen minimumTwo)
                        (QCRandom.mkQCGen 20260821)
                        0
            ECTAGen.minimumSize minimumTwo `shouldBe` Right (Just 2)
            sampled `shouldBe` Leaf 0

        it "hands back a body that never uses the argument" $ do
            let notRecursive = ECTAGen.recur $ \_self -> Leaf <$> ECTAGen.elements [0 .. 2]
            ECTAGen.cardinality notRecursive `shouldBe` Right 3
            fmap numNestedMu (ECTAGen.support notRecursive) `shouldBe` Right 0
            fmap length (ECTAGen.pmf notRecursive) `shouldBe` Right 3

        it "shrinks a failing member to the smallest of its size" $ do
            let containsOne (Leaf value) = value == 1
                containsOne (Branch left right) = containsOne left || containsOne right
                failing member = leaves member >= 3 && containsOne member
            result <-
                QC.quickCheckWithResult QC.stdArgs{QC.chatty = False, QC.maxSize = 6, QC.maxSuccess = 500} $
                    ECTAGen.forAll trees (not . failing)
            case result of
                QC.Failure{QC.failingTestCase = [shown]} ->
                    let rank = read (takeWhile (/= ':') (drop 5 shown)) :: Integer
                     in case ECTAGen.unrank trees rank of
                            Right shrunk -> do
                                failing shrunk `shouldBe` True
                                leaves shrunk `shouldBe` 3
                            Left err -> expectationFailure $ show err
                _ -> expectationFailure "expected the property to fail"

    describe "generators read from an automaton" $ do
        it "accepts exactly the language of a finite automaton" $
            let generator = ECTAGen.fromECTA finiteAutomaton
             in case ECTAGen.cardinality (ECTAGen.upToSize 2 generator) of
                    Right total ->
                        sort [term | rank <- [0 .. total - 1], Right term <- [ECTAGen.unrank generator rank]]
                            `shouldBe` sort (getAllTerms finiteAutomaton)
                    Left err -> expectationFailure $ show err

        it "treats every term of a finite automaton as one atomic choice" $ do
            let structured = ECTAGen.fromECTA finiteAutomaton
                atomic = ECTAGen.atomic structured
                ranks = [0 .. 3]
            ECTAGen.cardinality atomic `shouldBe` Right 4
            traverse (ECTAGen.unrank atomic) ranks
                `shouldBe` traverse (ECTAGen.unrank structured) ranks
            fmap sort (traverse (ECTAGen.unrank atomic) ranks)
                `shouldBe` Right (sort $ getAllTerms finiteAutomaton)
            map (ECTAGen.sizeOfRank atomic) ranks
                `shouldBe` replicate 4 (Just 1)
            fmap (== finiteAutomaton) (ECTAGen.support atomic)
                `shouldBe` Right True

        it "keeps a large atomic automaton compact" $ do
            let bit = Node [Edge "zero" [], Edge "one" []]
                compact = Node [Edge "command" (replicate 40 bit)]
                atomic = ECTAGen.atomic $ ECTAGen.fromECTA compact
            ECTAGen.cardinality atomic `shouldBe` Right (2 ^ (40 :: Int))
            ECTAGen.sizeOfRank atomic (2 ^ (40 :: Int) - 1)
                `shouldBe` Just 1
            fmap nodeCount (ECTAGen.support atomic) `shouldBe` Right 2

        it "makes recursive size count complete atomic commands" $ do
            let commands = ECTAGen.atomic $ ECTAGen.fromECTA finiteAutomaton
                traces = ECTAGen.recur $ \rest ->
                    ECTAGen.oneof
                        [ (: []) <$> commands
                        , (:) <$> commands <*> rest
                        ]
            traverse (ECTAGen.countAtSize traces) [1 .. 3]
                `shouldBe` Right [4, 16, 64]

        it "requires a recursive or opaque language to cross a finite boundary" $ do
            let recursive = ECTAGen.fromECTA typeAutomaton
                bounded = ECTAGen.atomic $ ECTAGen.upToSize 2 recursive
                opaque = ECTAGen.atomic $ ECTAGen.fromGen (pure True)
            ECTAGen.cardinality (ECTAGen.atomic recursive)
                `shouldBe` Left UnboundedGenerator
            ECTAGen.cardinality bounded `shouldBe` Right 2
            map (ECTAGen.sizeOfRank bounded) [0, 1]
                `shouldBe` replicate 2 (Just 1)
            ECTAGen.cardinality opaque
                `shouldBe` Left CannotInspectOpaqueGenerator

        it "counts the size classes of a recursive automaton" $
            traverse (ECTAGen.countAtSize $ ECTAGen.fromECTA typeAutomaton) [1 .. 5]
                `shouldBe` Right [1, 1, 2, 4, 9]

        modifyMaxSuccess (const 200) $
            it "samples only terms the automaton accepts" $
                QC.forAll (QC.resize 6 $ ECTAGen.toGen $ ECTAGen.fromECTA typeAutomaton) $
                    \term -> QC.counterexample (show term) $ QC.property $ nodeRepresents typeAutomaton term

        it "retains the term of every member, so a bounded language is inspectable" $ do
            let bounded = ECTAGen.upToSize 2 $ ECTAGen.fromECTA typeAutomaton
            fmap (map fst) (ECTAGen.pmf bounded)
                `shouldSatisfy` either (const False) ((== 2) . length)
            fmap sum (ECTAGen.countBy termSymbol bounded) `shouldBe` Right 2

        it "keeps aggregate inspection behind a finite recursive bound" $
            ECTAGen.pmf boundedTrees `shouldBe` Left CannotInspectRecursiveGenerator

        it "reports a recursive automaton without finite terms as empty" $ do
            let emptyAutomaton = createMu $ \self -> Node [Edge "loop" [self]]
                generator = ECTAGen.fromECTA emptyAutomaton
            smallestResult <- timeout 1000000 $ evaluate $ ECTAGen.smallest generator
            unrankResult <- timeout 1000000 $ evaluate $ ECTAGen.unrank generator 0
            ECTAGen.minimumSize generator `shouldBe` Right Nothing
            smallestResult `shouldBe` Just (Right Nothing)
            unrankResult `shouldBe` Just (Left $ SelectionOutOfRange 0 0)

        it "rejects an automaton whose edges carry equality constraints" $
            ECTAGen.cardinality (ECTAGen.upToSize 3 $ ECTAGen.fromECTA constrainedAutomaton)
                `shouldBe` Left CannotCountConstrainedEdges

-- | The head symbol of a term, as a coverage key.
termSymbol :: Term -> String
termSymbol = show
