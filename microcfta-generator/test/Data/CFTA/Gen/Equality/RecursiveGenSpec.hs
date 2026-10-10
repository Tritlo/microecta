{-# LANGUAGE OverloadedStrings #-}

-- | Recursive generators and generators read from an existing automaton.
module Data.CFTA.Gen.Equality.RecursiveGenSpec (spec) where

import Control.Exception (evaluate)
import Data.List (mapAccumL, sort)
import qualified Data.Map.Strict as Map
import Data.Ratio ((%))
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Gen as QCGen
import qualified Test.QuickCheck.Random as QCRandom

import Data.CFTA.Constraint (equalityConstraint)
import Data.CFTA.Equality (
    Edge (Edge),
    Node (Node),
    accepts,
    createMu,
    mkEdge,
    nodeCount,
    numNestedMu,
    terms,
 )
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import Data.CFTA.Gen.Equality.QuickCheck (Args (..), ECTAGen, GenError (..), On (..), Sig (..))
import qualified Data.CFTA.Gen.Equality.QuickCheck as ECTAGen
import Data.CFTA.Gen.Equality.TestSupport (aggregateRights, renameSymbols)
import Data.CFTA.Index (Cardinality (..), Rank (..), everyRank)
import Data.CFTA.Path (path)
import Data.CFTA.Ranked.Internal.Sampler (Exact (..))
import Data.CFTA.Symbol (Symbol)

-- | A binary tree over three leaf values, defined by its own language.
data Tree = Leaf Int | Branch Tree Tree
    deriving (Eq, Ord, Show)

data Coin = Heads | Tails
    deriving (Eq, Ord, Show)

-- | A call with a list of arguments, for a recursion nested in a family.
data Call = NoCall | Call [Call]
    deriving (Eq, Show)

-- | States used to check weighted operation keys inside recursive grouping.
data CoinPhase = Initial | SawHeads | SawTails | Unreachable
    deriving (Eq, Ord, Show)

trees :: ECTAGen Tree
trees = ECTAGen.recur $ \self ->
    ECTAGen.oneof
        [ Leaf <$> ECTAGen.elements [0 .. 2]
        , Branch <$> self <*> self
        ]

-- | The number of leaves of a tree.
leafCount :: Tree -> Int
leafCount (Leaf _) = 1
leafCount (Branch left right) = leafCount left + leafCount right

-- | Members of size at most four, the bound used throughout.
boundedTrees :: ECTAGen Tree
boundedTrees = ECTAGen.upToSize 4 trees

-- | Number of tree members of size at most four.
boundedTreeCount :: Cardinality
boundedTreeCount = 471

-- | A finite automaton whose language is easy to state independently.
finiteAutomaton :: Node Symbol
finiteAutomaton =
    Node
        [ Edge "a" []
        , Edge "b" []
        , Edge "f" [Node [Edge "a" [], Edge "b" []]]
        ]

-- | A recursive automaton: ground types under one type constructor and one arrow.
typeAutomaton :: Node Symbol
typeAutomaton =
    createMu $ \recursive ->
        Node
            [ Edge "baseType" []
            , Edge "->" [recursive, recursive]
            , Edge "Maybe" [recursive]
            ]

-- | An automaton whose edge carries an equality constraint.
constrainedAutomaton :: Node Symbol
constrainedAutomaton =
    Node
        [ mkEdge
            "pair"
            [finiteAutomaton, finiteAutomaton]
            (equalityConstraint $ mkEqConstraints [[path [0], path [1]]])
        ]

-- | Force a value through its 'Show' instance so a hang is caught by 'timeout'.
evaluateFully :: (Show a) => a -> IO a
evaluateFully value = evaluate (length $ show value) >> pure value

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
            ECTAGen.sizes (ECTAGen.groupOn leafCount trees)
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
            ECTAGen.unrank boundedTrees 471
                `shouldBe` Left (SelectionOutOfRange 471 boundedTreeCount)

        it "keeps every rank when the language is bounded" $
            [ECTAGen.unrank trees rank | rank <- everyRank boundedTreeCount]
                `shouldBe` [ECTAGen.unrank boundedTrees rank | rank <- everyRank boundedTreeCount]

        it "ranks members in size order, smallest first" $ do
            traverse (ECTAGen.unrank trees) [0 .. 3]
                `shouldBe` Right
                    [ Leaf 0
                    , Leaf 1
                    , Leaf 2
                    , Branch (Leaf 0) (Leaf 0)
                    ]
            [ECTAGen.sizeOfRank trees rank | rank <- everyRank boundedTreeCount]
                `shouldBe` [ Just (toEnum $ leafCount member)
                           | rank <- everyRank boundedTreeCount
                           , Right member <- [ECTAGen.unrank trees rank]
                           ]

        it "decodes every rank of the bounded language to a distinct member" $
            traverse (ECTAGen.unrank trees) (everyRank boundedTreeCount)
                `shouldSatisfy` either (const False) ((== 471) . Set.size . Set.fromList)

        it "rejects negative recursive ranks without scanning the language" $ do
            result <- timeout 60000000 $ evaluateFully $ ECTAGen.unrank trees (-1)
            result `shouldBe` Just (Left $ NegativeRank (-1))

        it "supports the language with one recursive automaton" $
            fmap numNestedMu (ECTAGen.support trees) `shouldBe` Right 1

        modifyMaxSuccess (const 200) $
            it "samples within the size parameter" $
                QC.forAll (QC.resize 4 $ ECTAGen.toGen trees) $ \member ->
                    QC.counterexample (show member) $ QC.property $ leafCount member <= 4

        it "reports the exact atomic distribution inside one recursive size" $ do
            let coin :: ECTAGen.ECTAGen _
                coin = ECTAGen.atomic $ ECTAGen.frequency [(9, pure Heads), (1, pure Tails)]
                words_ :: ECTAGen.ECTAGen _
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
            let weighted :: ECTAGen.ECTAGen _
                weighted =
                    ECTAGen.recur $ \self ->
                        ECTAGen.frequency
                            [ (1, Leaf <$> ECTAGen.elements [0 .. 2])
                            , (3, Branch <$> self <*> self)
                            ]
             in ECTAGen.cardinality (ECTAGen.upToSize 2 weighted)
                    `shouldBe` Left WeightedRecursiveAlternatives

        it "rejects a recursion that never passes through an application" $ do
            let unguarded :: ECTAGen.ECTAGen _
                unguarded = ECTAGen.recur $ \self ->
                    ECTAGen.oneof [Leaf <$> ECTAGen.elements [0 .. 2], self]
                mapped = ECTAGen.recur (id)
            ECTAGen.countAtSize unguarded 1 `shouldBe` Left UnguardedRecursion
            ECTAGen.countAtSize (mapped :: ECTAGen Tree) 1
                `shouldBe` Left UnguardedRecursion

        it "rejects a recursion whose pays add no term node" $ do
            -- Each member is one larger, but its term is the term of the
            -- smaller member under choice wrappers, which a constructor removes.
            let paid :: ECTAGen.ECTAGen Tree
                paid = ECTAGen.recur $ \self -> ECTAGen.oneof [Leaf <$> ECTAGen.elements [0], ECTAGen.pay self]
                counted :: ECTAGen.ECTAGen Tree
                counted = ECTAGen.recur $ \self -> ECTAGen.oneof [Leaf <$> ECTAGen.elements [0], ECTAGen.node "s" self]
            ECTAGen.countAtSize paid 1 `shouldBe` Left UnguardedRecursion
            map (ECTAGen.countAtSize counted) [1 .. 3] `shouldBe` [Right 1, Right 1, Right 1]

        it "reports a guarded recursion with no base as empty" $ do
            let empty = ECTAGen.recur $ \self -> ECTAGen.pay $ pure id <*> self
            smallestResult <- timeout 60000000 $ evaluateFully $ ECTAGen.smallest (empty :: ECTAGen Tree)
            unrankResult <- timeout 60000000 $ evaluateFully $ ECTAGen.unrank (empty :: ECTAGen Tree) 0
            smallestResult `shouldBe` Just (Right Nothing)
            unrankResult `shouldBe` Just (Left EmptyGenerator)

        it "reports a guarded grouped recursion with no base as empty" $ do
            let operations = ECTAGen.keyed (() :-> ()) $ pure id
                family :: ECTAGen.Grouped () ()
                family = ECTAGen.recurGrouped $ \self ->
                    ECTAGen.apply operations (self :& ANil)
            result <- timeout 60000000 $ evaluateFully $ ECTAGen.smallest $ ECTAGen.ungroup family
            result `shouldBe` Just (Right Nothing)

        it "keeps a family whose nested finite members all use one of its keys" $ do
            let family :: ECTAGen.Grouped () Call
                family = ECTAGen.recurGrouped $ \self ->
                    ECTAGen.keyed () $
                        ECTAGen.oneof
                            [ pure NoCall
                            , ECTAGen.pay $
                                pure Call
                                    <*> ECTAGen.recur
                                        ( \rest ->
                                            ECTAGen.oneof [pure (: []) <*> ECTAGen.atKey () self, ECTAGen.pay $ (:) <$> ECTAGen.atKey () self <*> rest]
                                        )
                            ]
                calls = ECTAGen.ungroup family
            ECTAGen.isRecursive calls `shouldBe` True
            map (ECTAGen.countAtSize calls) [1 .. 4] `shouldBe` [Right 1, Right 2, Right 5, Right 14]

        it "finds a key that the body reaches only through a nested recursion over another key" $ do
            -- Every member of key 1 reads key 0, so a pass around empty groups
            -- finds no member. A pay guards the read of the family.
            let family :: ECTAGen.Grouped Int Int
                family = ECTAGen.recurGrouped $ \self ->
                    ECTAGen.oneofGrouped
                        [ ECTAGen.keyed 0 (pure 0)
                        , ECTAGen.keyed 1 $
                            ECTAGen.recur $ \n ->
                                ECTAGen.oneof [ECTAGen.pay $ (+) <$> ECTAGen.atKey 0 self <*> pure 1, ECTAGen.pay $ (+) <$> n <*> n]
                        ]
            ECTAGen.smallest (ECTAGen.atKey 1 family) `shouldBe` Right (Just 1)

        it "keeps an enclosing recursion that a family reaches only through another key" $ do
            -- Key 1 reads key 2, which reads the enclosing recursion.
            let family :: ECTAGen Int -> ECTAGen.Grouped Int Int
                family enclosing = ECTAGen.recurGrouped $ \self ->
                    ECTAGen.oneofGrouped
                        [ ECTAGen.keyed 2 $ ECTAGen.oneof [enclosing, ECTAGen.elements [3]]
                        , ECTAGen.apply (ECTAGen.keyed (2 :-> 1) $ ECTAGen.elements [(+ 10)]) (self :& ANil)
                        ]
                outer = ECTAGen.recur $ \enclosing ->
                    ECTAGen.ungroup $
                        ECTAGen.apply (ECTAGen.keyed (1 :-> (2 :: Int)) $ ECTAGen.elements [(+ 100)]) (family enclosing :& ANil)
            result <- timeout 60000000 $ evaluateFully (ECTAGen.isRecursive outer, ECTAGen.smallest outer)
            result `shouldBe` Just (True, Right (Just 113))

        it "starts QuickCheck at the first live recursive size" $ do
            let minimumTwo :: ECTAGen.ECTAGen _
                minimumTwo = ECTAGen.recur $ \self ->
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
            let notRecursive :: ECTAGen.ECTAGen _
                notRecursive = ECTAGen.recur $ \_self -> Leaf <$> ECTAGen.elements [0 .. 2]
            ECTAGen.cardinality notRecursive `shouldBe` Right 3
            fmap numNestedMu (ECTAGen.support notRecursive) `shouldBe` Right 0
            fmap length (ECTAGen.pmf notRecursive) `shouldBe` Right 3

        it "shrinks a failing member to the smallest of its size" $ do
            let containsOne (Leaf value) = value == 1
                containsOne (Branch left right) = containsOne left || containsOne right
                failing member = leafCount member >= 3 && containsOne member
            result <-
                QC.quickCheckWithResult
                    QC.stdArgs{QC.replay = Just (QCRandom.mkQCGen 20260912, 0), QC.chatty = False, QC.maxSize = 6, QC.maxSuccess = 500}
                    $ ECTAGen.forAll trees (not . failing)
            case result of
                QC.Failure{QC.failingTestCase = [shown]} ->
                    let rank = Rank $ read (takeWhile (/= ':') (drop 5 shown))
                     in case ECTAGen.unrank trees rank of
                            Right shrunk -> do
                                failing shrunk `shouldBe` True
                                leafCount shrunk `shouldBe` 3
                            Left err -> expectationFailure $ show err
                _ -> expectationFailure "expected the property to fail"

        it "shrinks a finite generator to its smallest counterexample" $ do
            -- Rank 0 is the one member of size three. Bounding at size one
            -- would rank the members of size one again, from zero.
            let generator :: ECTAGen Int
                generator =
                    ECTAGen.oneof
                        [ (\a b c -> a + b + c) <$> ECTAGen.elements [1000] <*> ECTAGen.elements [0] <*> ECTAGen.elements [0]
                        , ECTAGen.elements [1 .. 100]
                        ]
            result <-
                timeout 10000000
                    $ QC.quickCheckWithResult
                        QC.stdArgs{QC.replay = Just (QCRandom.mkQCGen 20260925, 0), QC.chatty = False}
                    $ ECTAGen.forAll generator (< 0)
            case result of
                Just QC.Failure{QC.failingTestCase = shown} -> shown `shouldBe` ["rank 1: 1"]
                Just _ -> expectationFailure "expected the property to fail"
                Nothing -> expectationFailure "shrinking did not end"

    describe "generators read from an automaton" $ do
        it "accepts exactly the language of a finite automaton" $
            let generator = ECTAGen.fromAutomaton finiteAutomaton
             in case ECTAGen.cardinality (ECTAGen.upToSize 2 generator) of
                    Right total ->
                        sort [term | rank <- everyRank total, Right term <- [ECTAGen.unrank generator rank]]
                            `shouldBe` sort (terms finiteAutomaton)
                    Left err -> expectationFailure $ show err

        it "treats every term of a finite automaton as one atomic choice" $ do
            let structured = ECTAGen.fromAutomaton finiteAutomaton
                atomic = ECTAGen.atomic structured
                ranks = [0 .. 3]
            ECTAGen.cardinality atomic `shouldBe` Right 4
            traverse (ECTAGen.unrank atomic) ranks
                `shouldBe` traverse (ECTAGen.unrank structured) ranks
            fmap sort (traverse (ECTAGen.unrank atomic) ranks)
                `shouldBe` Right (sort $ terms finiteAutomaton)
            map (ECTAGen.sizeOfRank atomic) ranks
                `shouldBe` replicate 4 (Just 1)
            fmap (== renameSymbols ECTAGen.Label finiteAutomaton) (ECTAGen.support atomic)
                `shouldBe` Right True

        it "keeps a large atomic automaton compact" $ do
            let bit = Node [Edge "zero" [], Edge "one" []]
                compact = Node [Edge "command" (replicate 40 bit)]
                atomic = ECTAGen.atomic $ ECTAGen.fromAutomaton compact
            ECTAGen.cardinality atomic `shouldBe` Right (2 ^ (40 :: Int))
            ECTAGen.sizeOfRank atomic (2 ^ (40 :: Int) - 1)
                `shouldBe` Just 1
            fmap nodeCount (ECTAGen.support atomic) `shouldBe` Right 2

        it "makes recursive size count complete atomic commands" $ do
            let commands = ECTAGen.atomic $ ECTAGen.fromAutomaton finiteAutomaton
                traces = ECTAGen.recur $ \rest ->
                    ECTAGen.oneof
                        [ (: []) <$> commands
                        , (:) <$> commands <*> rest
                        ]
            traverse (ECTAGen.countAtSize traces) [1 .. 3]
                `shouldBe` Right [4, 16, 64]

        it "requires a recursive or opaque language to cross a finite boundary" $ do
            let recursive = ECTAGen.fromAutomaton typeAutomaton
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
            traverse (ECTAGen.countAtSize $ ECTAGen.fromAutomaton typeAutomaton) [1 .. 5]
                `shouldBe` Right [1, 1, 2, 4, 9]

        modifyMaxSuccess (const 200) $
            it "samples only terms the automaton accepts" $
                QC.forAll (QC.resize 6 $ ECTAGen.toGen $ ECTAGen.fromAutomaton typeAutomaton) $
                    \term -> QC.counterexample (show term) $ QC.property $ accepts typeAutomaton term

        it "retains the term of every member, so a bounded language is inspectable" $ do
            let bounded = ECTAGen.upToSize 2 $ ECTAGen.fromAutomaton typeAutomaton
            fmap (map fst) (ECTAGen.pmf bounded)
                `shouldSatisfy` either (const False) ((== 2) . length)
            fmap sum (ECTAGen.countOn termSymbol bounded) `shouldBe` Right 2

        it "inspects the members of a finite recursive bound by their terms" $ do
            -- A bounded recursive language keeps a term for every member, so
            -- aggregate inspection reads its members as for a finite language.
            let distribution = ECTAGen.pmf boundedTrees
            fmap (toEnum . length) distribution `shouldBe` ECTAGen.cardinality boundedTrees
            fmap (sum . map snd) distribution `shouldBe` Right 1

        it "reports a recursive automaton without finite terms as empty" $ do
            let emptyAutomaton = createMu $ \self -> Node [Edge "loop" [self]]
                generator = ECTAGen.fromAutomaton emptyAutomaton
            smallestResult <- timeout 60000000 $ evaluateFully $ ECTAGen.smallest generator
            unrankResult <- timeout 60000000 $ evaluateFully $ ECTAGen.unrank generator 0
            ECTAGen.minimumSize generator `shouldBe` Right Nothing
            smallestResult `shouldBe` Just (Right Nothing)
            unrankResult `shouldBe` Just (Left $ SelectionOutOfRange 0 0)

        it "counts a finite constrained automaton and rejects a recursive one" $ do
            ECTAGen.cardinality (ECTAGen.fromAutomaton constrainedAutomaton)
                `shouldBe` Right 4
            let recursivePairs = createMu $ \self ->
                    Node
                        [ Edge "a" []
                        , mkEdge "pair" [self, self] (equalityConstraint $ mkEqConstraints [[path [0], path [1]]])
                        ]
            ECTAGen.cardinality (ECTAGen.upToSize 3 $ ECTAGen.fromAutomaton recursivePairs)
                `shouldBe` Left CannotCountConstrainedEdges

    describe "recursive sampling" $ do
        it "preserves an atomic finite distribution and its stable ranks" $ do
            let coin :: ECTAGen.ECTAGen Bool
                coin =
                    ECTAGen.atomic $
                        ECTAGen.frequency
                            [ (3, ECTAGen.elements [True])
                            , (1, ECTAGen.elements [False])
                            ]
                traces =
                    ECTAGen.recur $ \rest ->
                        ECTAGen.oneof
                            [ (: []) <$> coin
                            , (:) <$> coin <*> rest
                            ]
                bounded = ECTAGen.upToSize 2 traces
            let sampled = runExact $ ECTAGen.lowerWithRankVia bounded
            [() | (_, Left _) <- sampled] `shouldBe` []
            aggregateRights sampled
                `shouldBe` [ (1 % 4, ECTAGen.RankedValue 0 [True])
                           , (1 % 12, ECTAGen.RankedValue 1 [False])
                           , (3 % 8, ECTAGen.RankedValue 2 [True, True])
                           , (1 % 8, ECTAGen.RankedValue 3 [True, False])
                           , (1 % 8, ECTAGen.RankedValue 4 [False, True])
                           , (1 % 24, ECTAGen.RankedValue 5 [False, False])
                           ]
            traverse (ECTAGen.unrank bounded) [0 .. 5]
                `shouldBe` Right
                    [ [True]
                    , [False]
                    , [True, True]
                    , [True, False]
                    , [False, True]
                    , [False, False]
                    ]

        it "keeps an atomic distribution beside a finite sibling" $ do
            let coin :: ECTAGen.ECTAGen Coin
                coin = ECTAGen.atomic $ ECTAGen.frequency [(1, pure Heads), (9, pure Tails)]
                words_ :: ECTAGen.ECTAGen [Coin]
                words_ = ECTAGen.recur $ \rest ->
                    ECTAGen.oneof
                        [ (\first second -> [first, second]) <$> coin <*> ECTAGen.elements [Heads]
                        , (:) <$> coin <*> rest
                        ]
            ECTAGen.pmfAtSize words_ 2
                `shouldBe` Right [([Heads, Heads], 1 % 10), ([Tails, Heads], 9 % 10)]

        it "keeps the exact distribution when a finite generator is bounded" $ do
            let coin :: ECTAGen.ECTAGen Coin
                coin = ECTAGen.atomic $ ECTAGen.frequency [(1, pure Heads), (9, pure Tails)]
            ECTAGen.pmf (ECTAGen.upToSize 5 coin) `shouldBe` Right [(Heads, 1 % 10), (Tails, 9 % 10)]
            ECTAGen.pmf (ECTAGen.upToSize 5 coin) `shouldBe` ECTAGen.pmf coin

        it "keeps an atomic distribution through a nested bound and a recursion" $ do
            let coin :: ECTAGen.ECTAGen Coin
                coin = ECTAGen.atomic $ ECTAGen.frequency [(1, pure Heads), (9, pure Tails)]
                pair = (\first second -> [first, second]) <$> coin <*> ECTAGen.elements [Heads]
                words_ :: ECTAGen.ECTAGen [Coin]
                words_ = ECTAGen.recur $ \rest ->
                    ECTAGen.oneof [(: []) <$> coin, (:) <$> coin <*> rest]
                -- A bounded recursive language inside another recursion.
                sentences :: ECTAGen.ECTAGen [Coin]
                sentences = ECTAGen.recur $ \rest ->
                    ECTAGen.oneof
                        [ ECTAGen.upToSize 1 words_
                        , (<>) <$> ECTAGen.upToSize 1 words_ <*> rest
                        ]
            ECTAGen.pmf (ECTAGen.upToSize 3 $ ECTAGen.upToSize 2 pair)
                `shouldBe` Right [([Heads, Heads], 1 % 10), ([Tails, Heads], 9 % 10)]
            ECTAGen.pmfAtSize sentences 1
                `shouldBe` Right [([Heads], 1 % 10), ([Tails], 9 % 10)]

        it "keeps an atomic distribution inside a grouped bucket" $ do
            let coin :: ECTAGen.ECTAGen Coin
                coin = ECTAGen.atomic $ ECTAGen.frequency [(1, pure Heads), (9, pure Tails)]
                pairs =
                    ECTAGen.groupOn (const ()) $
                        (\first second -> [first, second]) <$> coin <*> ECTAGen.elements [Heads]
                family :: ECTAGen.Grouped () [Coin]
                family = ECTAGen.recurGrouped $ \self ->
                    ECTAGen.oneofGrouped
                        [ pairs
                        , ECTAGen.apply (ECTAGen.keyed (() :-> ()) $ ECTAGen.elements [(Heads :)]) (self :& ANil)
                        ]
            ECTAGen.pmfAtSize (ECTAGen.ungroup family) 1
                `shouldBe` Right [([Heads, Heads], 1 % 10), ([Tails, Heads], 9 % 10)]

        it "keeps an atomic distribution through a bounded join" $ do
            let coin :: ECTAGen.ECTAGen Coin
                coin = ECTAGen.atomic $ ECTAGen.frequency [(1, pure Heads), (9, pure Tails)]
                matched = ECTAGen.match (id :==: id) coin (ECTAGen.elements [Heads, Tails])
                operations =
                    snd
                        <$> ECTAGen.groupOn
                            fst
                            ( ECTAGen.atomic $
                                ECTAGen.frequency
                                    [ (1, pure (() :-> (), (Heads :)))
                                    , (9, pure (() :-> (), (Tails :)))
                                    ]
                            )
                applied :: ECTAGen.ECTAGen [Coin]
                applied =
                    ECTAGen.ungroup $
                        ECTAGen.apply operations (ECTAGen.groupOn (const ()) (ECTAGen.elements [[]]) :& ANil)
            ECTAGen.pmf (ECTAGen.upToSize 2 matched)
                `shouldBe` Right [((Heads, Heads), 1 % 10), ((Tails, Tails), 9 % 10)]
            ECTAGen.pmf (ECTAGen.upToSize 2 applied)
                `shouldBe` Right [([Heads], 1 % 10), ([Tails], 9 % 10)]

        it "keeps finite weights out of recursion without an atomic boundary" $ do
            let coin :: ECTAGen.ECTAGen Bool
                coin =
                    ECTAGen.frequency
                        [ (3, ECTAGen.elements [True])
                        , (1, ECTAGen.elements [False])
                        ]
                traces =
                    ECTAGen.recur $ \rest ->
                        ECTAGen.oneof
                            [ (: []) <$> coin
                            , (:) <$> coin <*> rest
                            ]
            map fst (runExact $ ECTAGen.lowerWithRankVia $ ECTAGen.upToSize 2 traces)
                `shouldBe` replicate 6 (1 % 6)

        it "preserves atomic distributions through recurGrouped and apply" $ do
            let atoms =
                    ECTAGen.keyed ()
                        $ ECTAGen.atomic
                        $ ECTAGen.frequency
                            [ (3, ECTAGen.elements ["H"])
                            , (1, ECTAGen.elements ["T"])
                            ]
                operators =
                    ECTAGen.keyed (() :-> ()) $
                        ECTAGen.elements [("x" <>)]
                family =
                    ECTAGen.recurGrouped $ \self ->
                        ECTAGen.oneofGrouped
                            [ atoms
                            , ECTAGen.apply operators (self :& ANil)
                            ]
                bounded :: ECTAGen.ECTAGen String
                bounded = ECTAGen.upToSize 2 $ ECTAGen.atKey () family
            let sampled = runExact $ ECTAGen.lowerWithRankVia bounded
            [() | (_, Left _) <- sampled] `shouldBe` []
            aggregateRights sampled
                `shouldBe` [ (3 % 8, ECTAGen.RankedValue 0 "H")
                           , (1 % 8, ECTAGen.RankedValue 1 "T")
                           , (3 % 8, ECTAGen.RankedValue 2 "xH")
                           , (1 % 8, ECTAGen.RankedValue 3 "xT")
                           ]

        it "keeps atomic mass between recursive operation keys" $ do
            let operations =
                    snd
                        <$> ECTAGen.groupOn
                            fst
                            ( ECTAGen.atomic $
                                ECTAGen.frequency
                                    [ (9, pure (Initial :-> SawHeads, (True :)))
                                    , (1, pure (Initial :-> SawTails, (False :)))
                                    ]
                            )
                family :: ECTAGen.Grouped CoinPhase [Bool]
                family =
                    ECTAGen.recurGrouped $ \self ->
                        ECTAGen.oneofGrouped
                            [ ECTAGen.keyed Initial $ pure []
                            , ECTAGen.apply operations (self :& ANil)
                            ]
                traces = ECTAGen.ungroup family
            -- An operation has size one, and the initial empty trace size zero.
            ECTAGen.countsAtSize family 1
                `shouldBe` Right
                    (Map.fromList [(SawHeads, 1), (SawTails, 1)])
            ECTAGen.massesAtSize family 1
                `shouldBe` Right
                    (Map.fromList [(SawHeads, 9 % 10), (SawTails, 1 % 10)])
            (sum <$> ECTAGen.countsAtSize family 1)
                `shouldBe` ECTAGen.countAtSize traces 1
            (sum <$> ECTAGen.massesAtSize family 1)
                `shouldBe` Right 1
            ECTAGen.pmfAtSize traces 1
                `shouldBe` Right [([False], 1 % 10), ([True], 9 % 10)]
            ECTAGen.smallest (ECTAGen.atKey SawHeads family)
                `shouldBe` Right (Just [True])
            ECTAGen.smallest (ECTAGen.atKey Unreachable family)
                `shouldBe` Right Nothing

    describe "engine term ranks" $ do
        it "rank the engine terms of finite generators" $ do
            roundTrips (ECTAGen.node "pair" ((,) <$> ECTAGen.elements [0, 1 :: Int] <*> ECTAGen.elements "ab")) [0 .. 3]
            roundTrips
                ( ECTAGen.oneof
                    [ECTAGen.node "a" (pure (1 :: Int)), ECTAGen.node "b" ((+) <$> ECTAGen.elements [1, 2] <*> ECTAGen.elements [10, 20])]
                )
                [0 .. 4]
            roundTrips
                (ECTAGen.match (even :==: even) (ECTAGen.elements [0 .. 3 :: Int]) (ECTAGen.elements [10 .. 13 :: Int]))
                [0 .. 7]
            roundTrips (ECTAGen.atomic $ ECTAGen.frequency [(1, ECTAGen.elements "a"), (9, ECTAGen.elements "b")]) [0, 1]
            roundTrips (ECTAGen.ungroup $ ECTAGen.apply rankOperators (rankAtoms :& ANil)) [0 .. 3]

        it "give every rank of a term, and reject a term outside the language" $ do
            -- A node label removes the choice wrapper, so ranks 0 and 2 have one term.
            let choiceUnderNode :: ECTAGen Int
                choiceUnderNode = ECTAGen.node "n" (ECTAGen.oneof [ECTAGen.elements [1, 2], ECTAGen.elements [3, 4]])
            (ECTAGen.ranksOf choiceUnderNode =<< ECTAGen.termAt choiceUnderNode 0) `shouldBe` Right [0, 2]
            ECTAGen.rankOf rankTree (Tree.Node (ECTAGen.Label "other") []) `shouldBe` Left TermNotInLanguage

        it "rank a deep term under a choice of labels in time linear in its depth" $ do
            -- An alternative with another label than the term read the whole
            -- term below it, so the work doubled at each level.
            let literal = ECTAGen.node "lit" (ECTAGen.elements [True, False])
                step :: ECTAGen Bool -> ECTAGen Bool
                step smaller =
                    ECTAGen.node "e" $
                        ECTAGen.oneof
                            [literal, ECTAGen.node "and" ((&&) <$> smaller <*> literal), ECTAGen.node "or" ((||) <$> smaller <*> literal)]
                -- A finite twin, built by Haskell recursion.
                nested :: Int -> ECTAGen Bool
                nested depth = if depth == 0 then ECTAGen.node "e" literal else step (nested (depth - 1))
                -- The term e(or(t, lit)), wrapped forty times around t = e(lit).
                deep base =
                    iterate (\term -> Tree.Node (ECTAGen.Label "e") [Tree.Node (ECTAGen.Label "or") (term : Tree.subForest base)]) base
                        !! 40
            mapM_
                ( \generator -> do
                    term <- either (fail . show) (pure . deep) $ ECTAGen.termAt generator 0
                    result <- timeout 10000000 $ evaluateFully $ (== term) <$> (ECTAGen.termAt generator =<< ECTAGen.rankOf generator term)
                    result `shouldBe` Just (Right True)
                )
                [ECTAGen.recur step, nested 40]

        it "rank the size-major terms of recursive generators" $ do
            let labelled = ECTAGen.recur $ \self ->
                    ECTAGen.oneof
                        [ECTAGen.node "leaf" (Leaf <$> ECTAGen.elements [0 .. 2]), ECTAGen.node "branch" (Branch <$> self <*> self)]
                binary = ECTAGen.keyed (() :* () :-> ()) $ ECTAGen.elements [(<>)]
                family = ECTAGen.recurGrouped $ \self -> ECTAGen.oneofGrouped [rankAtoms, ECTAGen.apply rankOperators (self :& ANil)]
                family2 = ECTAGen.recurGrouped $ \self -> ECTAGen.oneofGrouped [rankAtoms, ECTAGen.apply binary (self :& self :& ANil)]
            roundTrips rankTree [0 .. 150]
            roundTrips labelled [0 .. 150]
            roundTrips (show <$> rankTree) [0 .. 50]
            roundTrips (ECTAGen.upToSize 4 rankTree) [0 .. 120]
            roundTrips (ECTAGen.atKey () family) [0 .. 100]
            roundTrips (ECTAGen.ungroup family2) [0 .. 100]

{- | Check that each rank has a term that the support accepts, that the rank is
one of the ranks of its term, and that the least rank of the term gives the
term back. A term with one user symbol changed to a symbol outside the
language has no rank, and neither has a term with an argument key moved.
-}
roundTrips :: ECTAGen a -> [Rank] -> IO ()
roundTrips generator ranks = do
    supportNode <- either (fail . show) pure $ ECTAGen.support generator
    mapM_
        ( \rank -> do
            term <- either (fail . show) pure $ ECTAGen.termAt generator rank
            termRanks <- either (fail . show) pure $ ECTAGen.ranksOf generator term
            (rank, rank `elem` termRanks) `shouldBe` (rank, True)
            (ECTAGen.termAt generator =<< ECTAGen.rankOf generator term) `shouldBe` Right term
            (rank, accepts supportNode term) `shouldBe` (rank, True)
            [(rank, ECTAGen.rankOf generator changed) | changed <- changedAt outside term]
                `shouldBe` [(rank, Left TermNotInLanguage) | _ <- changedAt outside term]
        )
        ranks
  where
    outside label = case label of
        ECTAGen.Label _ -> Just $ ECTAGen.Label "outside"
        ECTAGen.ArgKey component position -> Just $ ECTAGen.ArgKey component (position + 1)
        _ -> Nothing

-- | The term with one label changed, once for each label that the function changes.
changedAt ::
    (ECTAGen.Label symbol -> Maybe (ECTAGen.Label symbol)) ->
    Tree.Tree (ECTAGen.Label symbol) ->
    [Tree.Tree (ECTAGen.Label symbol)]
changedAt change term =
    [ snd $ mapAccumL (\index label -> (index + 1, if index == position then changed else label)) (0 :: Int) term
    | (position, Just changed) <- zip [0 ..] $ map change $ Tree.flatten term
    ]

-- | A recursive language of binary trees.
rankTree :: ECTAGen Tree
rankTree = ECTAGen.recur $ \self -> ECTAGen.oneof [Leaf <$> ECTAGen.elements [0 .. 2], Branch <$> self <*> self]

-- | Two atoms under one key.
rankAtoms :: ECTAGen.Grouped () String
rankAtoms = ECTAGen.keyed () $ ECTAGen.elements ["H", "T"]

-- | Two unary operations under one signature.
rankOperators :: ECTAGen.Grouped (Sig '[()] ()) (String -> String)
rankOperators = ECTAGen.keyed (() :-> ()) $ ECTAGen.elements [("x" <>), ("y" <>)]

-- | The head symbol of a term, as a coverage key.
termSymbol :: Tree.Tree Symbol -> String
termSymbol = show
