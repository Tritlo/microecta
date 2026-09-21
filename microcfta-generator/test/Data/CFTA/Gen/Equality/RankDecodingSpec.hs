-- | The compiled rank decoder, checked against unrank on every rank.
module Data.CFTA.Gen.Equality.RankDecodingSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import qualified Test.QuickCheck as QC

import Data.CFTA.Gen.Equality.QuickCheck (Args (..), Sig ((:*), (:->)))
import qualified Data.CFTA.Gen.Equality.QuickCheck as ECTAGen
import Data.CFTA.Gen.Equality.TestSupport (decodesEveryRankExactly)
import Data.CFTA.Ranked.Internal.Sampler (Exact (..))

spec :: Spec
spec = do
    describe "compiled rank decoding" $ do
        it "decodes every rank of a mapped source"
            $ decodesEveryRankExactly
            $ show <$> ECTAGen.elements [1 :: Int .. 5]

        it "decodes every rank of nested uniform frequencies"
            $ decodesEveryRankExactly
            $ ECTAGen.frequency
                [ (2, ECTAGen.elements "ab")
                , (2, ECTAGen.frequency [(1, ECTAGen.elements "c"), (1, ECTAGen.elements "d")])
                ]

        it "decodes every rank of an applicative product"
            $ decodesEveryRankExactly
            $ (,) <$> ECTAGen.elements [1 :: Int, 2, 3] <*> ECTAGen.elements "ab"

        it "decodes every rank of a grouped ternary application tower" $ do
            let operations =
                    ECTAGen.groupBy
                        (\(_, key1, key2, key3, resultKey) -> key1 :* key2 :* key3 :-> resultKey)
                        (ECTAGen.elements [("f", 0 :: Int, 0, 1, 0 :: Int), ("g", 0, 1, 1, 1), ("h", 1, 0, 0, 1)])
                family =
                    ECTAGen.groupBy fst (ECTAGen.elements [(0 :: Int, "a"), (0, "b"), (1, "c")])
                applied =
                    ECTAGen.apply
                        ((\(name, _, _, _, _) x y z -> name <> snd x <> snd y <> snd z) <$> operations)
                        (family :& family :& family :& ANil)
            decodesEveryRankExactly
                $ ECTAGen.ungroup
                $ ECTAGen.mapWithKey (,) applied

        it "decodes every rank of a mixed-depth frequencies tower" $ do
            let atomsFamily =
                    snd <$> ECTAGen.groupBy fst (ECTAGen.elements [(0 :: Int, "x"), (0, "y"), (1, "z")])
                operations =
                    ECTAGen.groupBy
                        (\(_, leftKey, rightKey, resultKey) -> leftKey :* rightKey :-> resultKey)
                        (ECTAGen.elements [("f", 0 :: Int, 0, 0), ("g", 0, 1, 1), ("h", 1, 0, 1)])
                layer children =
                    ECTAGen.apply
                        ((\(name, _, _, _) left right -> name <> left <> right) <$> operations)
                        (children :& children :& ANil)
                mixed =
                    ECTAGen.frequencies
                        [ (3, atomsFamily)
                        , (8, layer atomsFamily)
                        ]
            decodesEveryRankExactly $ ECTAGen.ungroup mixed

        it "agrees with unrank on every enumerated non-uniform rank" $ do
            let generator :: ECTAGen.ECTAGen _
                generator =
                    ECTAGen.frequency
                        [ (3, ECTAGen.elements [1 :: Int])
                        , (1, ECTAGen.elements [2, 3])
                        ]
                sampled = runExact $ ECTAGen.lowerWithRankVia generator
            [() | (_, Left _) <- sampled] `shouldBe` []
            [ ECTAGen.unrank generator rank == Right value
              | (_, Right (rank, value)) <- sampled
              ]
                `shouldSatisfy` and

        it "streams exactly the structurally smaller members in size order" $ do
            let atomsFamily =
                    snd <$> ECTAGen.groupBy fst (ECTAGen.elements [(0 :: Int, "x"), (0, "y"), (1, "z")])
                operations =
                    ECTAGen.groupBy
                        (\(_, leftKey, rightKey, resultKey) -> leftKey :* rightKey :-> resultKey)
                        (ECTAGen.elements [("f", 0 :: Int, 0, 0), ("g", 0, 1, 1), ("h", 1, 0, 1)])
                mixed :: ECTAGen.ECTAGen String
                mixed =
                    ECTAGen.ungroup $
                        ECTAGen.frequencies
                            [ (3, atomsFamily)
                            ,
                                ( 8
                                , ECTAGen.apply
                                    ((\(name, _, _, _) left right -> name <> left <> right) <$> operations)
                                    (atomsFamily :& atomsFamily :& ANil)
                                )
                            ]
            case ECTAGen.cardinality mixed of
                Left err -> expectationFailure $ show err
                Right total -> do
                    let applicationRanks =
                            [ rank
                            | rank <- [0 .. total - 1]
                            , Right value <- [ECTAGen.unrank mixed rank]
                            , length value == 3
                            ]
                    case applicationRanks of
                        (firstApplication : _) -> do
                            map snd (ECTAGen.smallerMembers mixed firstApplication)
                                `shouldBe` ["x", "y", "z"]
                            [ ECTAGen.unrank mixed rank == Right value
                              | (rank, value) <- ECTAGen.smallerMembers mixed firstApplication
                              ]
                                `shouldSatisfy` and
                        [] -> expectationFailure "expected an application member"

        it "produces exactly the structural shrink candidates of a product" $
            let pairs :: ECTAGen.ECTAGen (Int, Char)
                pairs = (,) <$> ECTAGen.elements [0 .. 3] <*> ECTAGen.elements "abcd"
             in ECTAGen.shrinkRank pairs 15 `shouldBe` [3, 11, 12, 14]

        modifyMaxSuccess (const 200)
            $ it "replays sampled ranks below the Int cardinality boundary"
            $ let chunk = ECTAGen.elements [0 :: Int .. 199]
                  wide :: ECTAGen.ECTAGen _
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
                  wide :: ECTAGen.ECTAGen _
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
