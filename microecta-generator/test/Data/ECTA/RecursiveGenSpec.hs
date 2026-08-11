{-# LANGUAGE OverloadedStrings #-}

-- | Recursive generators and generators read from an existing automaton.
module Data.ECTA.RecursiveGenSpec (spec) where

import Data.List (nub, sort)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import qualified Test.QuickCheck as QC

import Data.ECTA (
    Edge (Edge),
    Node (Node),
    createMu,
    getAllTerms,
    mkEdge,
    nodeRepresents,
    numNestedMu,
 )
import Data.ECTA.Gen.QuickCheck (ECTAGen, ECTAGenError (..))
import qualified Data.ECTA.Gen.QuickCheck as ECTAGen
import Data.ECTA.Paths (mkEqConstraints, path)
import Data.ECTA.Term (Term)

-- | A binary tree over three leaf values, defined by its own language.
data Tree = Leaf Int | Branch Tree Tree
    deriving (Eq, Ord, Show)

trees :: ECTAGen Tree
trees = ECTAGen.mu $ \self ->
    ECTAGen.frequency
        [ (1, Leaf <$> ECTAGen.elements [0 .. 2])
        , (1, Branch <$> self <*> self)
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
            length (nub [ECTAGen.unrank trees rank | rank <- [0 .. boundedTreeCount - 1]])
                `shouldBe` fromInteger boundedTreeCount

        it "supports the language with one recursive automaton" $
            fmap numNestedMu (ECTAGen.support trees) `shouldBe` Right 1

        it "samples within the size parameter" $
            QC.withNumTests 200 $
                QC.forAll (QC.resize 4 $ ECTAGen.toGen trees) $ \member ->
                    QC.counterexample (show member) $ QC.property $ leaves member <= 4

        it "rejects weighted alternatives around a recursive occurrence" $
            let weighted =
                    ECTAGen.mu $ \self ->
                        ECTAGen.frequency
                            [ (1, Leaf <$> ECTAGen.elements [0 .. 2])
                            , (3, Branch <$> self <*> self)
                            ]
             in ECTAGen.cardinality (ECTAGen.upToSize 2 weighted)
                    `shouldBe` Left WeightedRecursiveAlternatives

        it "shrinks a failing member to the smallest of its size" $ do
            let containsOne (Leaf value) = value == 1
                containsOne (Branch left right) = containsOne left || containsOne right
                failing member = leaves member >= 3 && containsOne member
            result <-
                QC.quickCheckWithResult QC.stdArgs{QC.chatty = False, QC.maxSize = 6} $
                    QC.withNumTests 500 $
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

        it "counts the size classes of a recursive automaton" $
            traverse (ECTAGen.countAtSize $ ECTAGen.fromECTA typeAutomaton) [1 .. 5]
                `shouldBe` Right [1, 1, 2, 4, 9]

        it "samples only terms the automaton accepts" $
            QC.withNumTests 200 $
                QC.forAll (QC.resize 6 $ ECTAGen.toGen $ ECTAGen.fromECTA typeAutomaton) $
                    \term -> QC.counterexample (show term) $ QC.property $ nodeRepresents typeAutomaton term

        it "retains the term of every member, so a bounded language is inspectable" $ do
            let bounded = ECTAGen.upToSize 2 $ ECTAGen.fromECTA typeAutomaton
            fmap (map fst) (ECTAGen.pmf bounded)
                `shouldSatisfy` either (const False) ((== 2) . length)
            fmap sum (ECTAGen.countBy termSymbol bounded) `shouldBe` Right 2

        it "rejects an automaton whose edges carry equality constraints" $
            ECTAGen.cardinality (ECTAGen.upToSize 3 $ ECTAGen.fromECTA constrainedAutomaton)
                `shouldBe` Left CannotCountConstrainedEdges

-- | The head symbol of a term, as a coverage key.
termSymbol :: Term -> String
termSymbol = show
