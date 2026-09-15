-- | The compiled rank decoder, checked against unrank on every rank.
module Data.ECTA.RankDecodingSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import qualified Test.QuickCheck as QC

import qualified Data.ECTA.Gen as Core
import Data.ECTA.Gen.QuickCheck (Args (..), Sig ((:*), (:->)))
import qualified Data.ECTA.Gen.QuickCheck as ECTAGen
import Data.ECTA.TestSupport (decodesEveryRankExactly)
import Data.Tree.Gen.Internal.Sampler (Exact (..))

spec :: Spec
spec = do
    describe "compiled rank decoding" $ do
        it "decodes every rank of a mapped source"
            $ decodesEveryRankExactly
            $ show <$> Core.elements [1 :: Int .. 5]

        it "decodes every rank of nested uniform frequencies"
            $ decodesEveryRankExactly
            $ Core.frequency
                [ (2, Core.elements "ab")
                , (2, Core.frequency [(1, Core.elements "c"), (1, Core.elements "d")])
                ]

        it "decodes every rank of an applicative product"
            $ decodesEveryRankExactly
            $ (,) <$> Core.elements [1 :: Int, 2, 3] <*> Core.elements "ab"

        it "decodes every rank of a grouped ternary application tower" $ do
            let operations =
                    Core.groupBy
                        (\(_, key1, key2, key3, resultKey) -> key1 :* key2 :* key3 :-> resultKey)
                        (Core.elements [("f", 0 :: Int, 0, 1, 0 :: Int), ("g", 0, 1, 1, 1), ("h", 1, 0, 0, 1)])
                family =
                    Core.groupBy fst (Core.elements [(0 :: Int, "a"), (0, "b"), (1, "c")])
                applied =
                    Core.apply
                        ((\(name, _, _, _, _) x y z -> name <> snd x <> snd y <> snd z) <$> operations)
                        (family :& family :& family :& ANil)
            decodesEveryRankExactly
                $ Core.ungroup
                $ Core.mapWithKey (\key value -> (key, value)) applied

        it "decodes every rank of a mixed-depth frequencies tower" $ do
            let atomsFamily =
                    snd <$> Core.groupBy fst (Core.elements [(0 :: Int, "x"), (0, "y"), (1, "z")])
                operations =
                    Core.groupBy
                        (\(_, leftKey, rightKey, resultKey) -> leftKey :* rightKey :-> resultKey)
                        (Core.elements [("f", 0 :: Int, 0, 0), ("g", 0, 1, 1), ("h", 1, 0, 1)])
                layer children =
                    Core.apply
                        ((\(name, _, _, _) left right -> name <> left <> right) <$> operations)
                        (children :& children :& ANil)
                mixed =
                    Core.frequencies
                        [ (3, atomsFamily)
                        , (8, layer atomsFamily)
                        ]
            decodesEveryRankExactly $ Core.ungroup mixed

        it "agrees with unrank on every enumerated non-uniform rank" $ do
            let generator =
                    Core.frequency
                        [ (3, Core.elements [1 :: Int])
                        , (1, Core.elements [2, 3])
                        ]
                sampled = runExact $ Core.lowerWithRank generator
            [() | (_, Left _) <- sampled] `shouldBe` []
            [ Core.unrank generator rank == Right value
              | (_, Right (rank, value)) <- sampled
              ]
                `shouldSatisfy` and

        it "streams exactly the structurally smaller members in size order" $ do
            let atomsFamily =
                    snd <$> Core.groupBy fst (Core.elements [(0 :: Int, "x"), (0, "y"), (1, "z")])
                operations =
                    Core.groupBy
                        (\(_, leftKey, rightKey, resultKey) -> leftKey :* rightKey :-> resultKey)
                        (Core.elements [("f", 0 :: Int, 0, 0), ("g", 0, 1, 1), ("h", 1, 0, 1)])
                mixed :: Core.ECTAGen Exact String
                mixed =
                    Core.ungroup $
                        Core.frequencies
                            [ (3, atomsFamily)
                            ,
                                ( 8
                                , Core.apply
                                    ((\(name, _, _, _) left right -> name <> left <> right) <$> operations)
                                    (atomsFamily :& atomsFamily :& ANil)
                                )
                            ]
            case Core.cardinality mixed of
                Left err -> expectationFailure $ show err
                Right total -> do
                    let applicationRanks =
                            [ rank
                            | rank <- [0 .. total - 1]
                            , Right value <- [Core.unrank mixed rank]
                            , length value == 3
                            ]
                    case applicationRanks of
                        (firstApplication : _) -> do
                            map snd (Core.smallerMembers mixed firstApplication)
                                `shouldBe` ["x", "y", "z"]
                            [ Core.unrank mixed rank == Right value
                              | (rank, value) <- Core.smallerMembers mixed firstApplication
                              ]
                                `shouldSatisfy` and
                        [] -> expectationFailure "expected an application member"

        it "produces exactly the structural shrink candidates of a product" $
            let pairs :: Core.ECTAGen Exact (Int, Char)
                pairs = (,) <$> Core.elements [0 .. 3] <*> Core.elements "abcd"
             in Core.shrinkRank pairs 15 `shouldBe` [3, 11, 12, 14]

        modifyMaxSuccess (const 200)
            $ it "replays sampled ranks below the Int cardinality boundary"
            $ let chunk = ECTAGen.elements [0 :: Int .. 199]
                  wide =
                    (,,,,,,,)
                        <$> chunk
                        <*> chunk
                        <*> chunk
                        <*> chunk
                        <*> chunk
                        <*> chunk
                        <*> chunk
                        <*> chunk
               in ECTAGen.cardinality wide QC.=== Right (200 ^ (8 :: Int))
                    QC..&&. QC.forAll
                        (ECTAGen.toGenWithRank wide)
                        ( \(rank, value) ->
                            ECTAGen.unrank wide rank QC.=== Right value
                        )

        modifyMaxSuccess (const 200)
            $ it "replays sampled ranks beyond the Int cardinality boundary"
            $ let chunk = ECTAGen.elements [0 :: Int .. 255]
                  wide =
                    (,,,,,,,)
                        <$> chunk
                        <*> chunk
                        <*> chunk
                        <*> chunk
                        <*> chunk
                        <*> chunk
                        <*> chunk
                        <*> chunk
               in ECTAGen.cardinality wide QC.=== Right (256 ^ (8 :: Int))
                    QC..&&. QC.forAll
                        (ECTAGen.toGenWithRank wide)
                        ( \(rank, value) ->
                            ECTAGen.unrank wide rank QC.=== Right value
                        )
