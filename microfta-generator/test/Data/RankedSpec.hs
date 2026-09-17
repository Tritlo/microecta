module Data.RankedSpec (spec) where

import qualified Data.Map.Strict as Map
import Data.Ratio ((%))
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)

import qualified Data.Ranked as Tree
import Data.Ranked.Internal.Sampler (Exact (..))

spec :: Spec
spec = do
    describe "structural shrinking" $ do
        it "never offers a member larger than the current one across choice branches" $ do
            let languages = do
                    small <- Tree.fromIndexed (Tree.Indexed 2 ((: []))) :: Either Tree.RankedError (Tree.Ranked [Integer])
                    let big = (\a b c -> a <> b <> c) <$> small <*> small <*> small
                    bigFirst <- Tree.oneof [big, small]
                    smallFirst <- Tree.oneof [small, big]
                    pure (bigFirst, smallFirst)
            case languages of
                Left err -> expectationFailure $ show err
                Right (bigFirst, smallFirst) -> do
                    -- Rank 8 is the size-one member [0] in the second branch.
                    Tree.unrank bigFirst 8 `shouldBe` Right [0]
                    Tree.shrinkRank bigFirst 8 `shouldBe` []
                    Tree.smallerMembers bigFirst 8 `shouldBe` []
                    -- Rank 9 shrinks within its branch, never into the size-three branch.
                    Tree.shrinkRank bigFirst 9 `shouldBe` [8]
                    -- A size-three member shrinks to the size-one branch when that branch comes first.
                    Tree.unrank smallFirst 2 `shouldBe` Right [0, 0, 0]
                    take 1 (Tree.shrinkRank smallFirst 2) `shouldBe` [0]

    describe "weighted indexed rank sources" $ do
        it "preserves exact ticket weights and returns replay ranks" $ do
            let outcomes = [(1, 'a'), (3, 'b'), (2, 'c')] :: [(Integer, Char)]
                ticketRanks = [1, 2, 0, 1, 2, 1] :: [Integer]
                source =
                    Tree.WeightedIndexed
                        3
                        6
                        ((outcomes !!) . fromInteger)
                        ((ticketRanks !!) . fromInteger)
            case Tree.fromWeightedIndexedOnDemand source of
                Left err -> expectationFailure $ show err
                Right ranked -> do
                    Tree.cardinality ranked `shouldBe` 3
                    map (Tree.unrank ranked) [0 .. 2] `shouldBe` map Right outcomes
                    runExact (Tree.lowerWithRank ranked)
                        `shouldBe` [(1 % 6, (rank, outcomes !! fromInteger rank)) | rank <- ticketRanks]
                    Map.fromListWith (+) [(value, mass) | (mass, value) <- runExact $ Tree.lower ranked]
                        `shouldBe` Map.fromList [((1, 'a'), 1 % 6), ((3, 'b'), 3 % 6), ((2, 'c'), 2 % 6)]
                    Tree.unrank ranked (-1) `shouldBe` Left (Tree.NegativeRankedRank (-1))
                    Tree.unrank ranked 3 `shouldBe` Left (Tree.RankedSelectionOutOfRange 3 3)

        it "preserves weighted replay through maps and products" $ do
            let source = Tree.WeightedIndexed 2 3 (\rank -> if rank == 0 then 'a' else 'b') (\ticket -> if ticket == 1 then 0 else 1)
            case Tree.fromWeightedIndexedOnDemand source of
                Left err -> expectationFailure $ show err
                Right ranked -> do
                    let pairs = (,) <$> ranked <*> ranked
                        sampled = runExact $ Tree.lowerWithRank pairs
                    Tree.cardinality pairs `shouldBe` 4
                    map (Tree.unrank pairs) [0 .. 3]
                        `shouldBe` map Right [('a', 'a'), ('a', 'b'), ('b', 'a'), ('b', 'b')]
                    [Tree.unrank pairs rank == Right value | (_, (rank, value)) <- sampled]
                        `shouldSatisfy` and
                    Map.fromListWith (+) [(value, mass) | (mass, (_, value)) <- sampled]
                        `shouldBe` Map.fromList [(('a', 'a'), 1 % 9), (('a', 'b'), 2 % 9), (('b', 'a'), 2 % 9), (('b', 'b'), 4 % 9)]

        it "checks source metadata without evaluating callbacks" $ do
            let inspect count mass =
                    fmap Tree.cardinality
                        $ Tree.fromWeightedIndexedOnDemand
                        $ Tree.WeightedIndexed
                            count
                            mass
                            (error "construction decoded an indexed value" :: Integer -> ())
                            (error "construction decoded a sampling ticket")
            inspect 3 6 `shouldBe` Right 3
            inspect 0 0 `shouldBe` Left Tree.EmptyRanked
            inspect (-1) 4 `shouldBe` Left Tree.EmptyRanked
            inspect 3 0 `shouldBe` Left (Tree.NonPositiveRankedWeight 0)
            inspect 3 (-1) `shouldBe` Left (Tree.NonPositiveRankedWeight (-1))
            inspect 3 2 `shouldBe` Left (Tree.InsufficientRankedWeight 3 2)

        it "samples Integer ticket mass beyond the machine Int range" $ do
            let mass = toInteger (maxBound :: Int) + 5
                source =
                    Tree.WeightedIndexed
                        2
                        mass
                        (\rank -> if rank == 0 then 'a' else 'b')
                        (\ticket -> if ticket == 0 then 0 else 1)
            case Tree.fromWeightedIndexedOnDemand source of
                Left err -> expectationFailure $ show err
                Right ranked -> do
                    Tree.cardinality ranked `shouldBe` 2
                    Tree.unrank ranked 1 `shouldBe` Right 'b'
                    take 3 (runExact $ Tree.lowerWithRank ranked)
                        `shouldBe` [(1 % mass, (0, 'a')), (1 % mass, (1, 'b')), (1 % mass, (1, 'b'))]
