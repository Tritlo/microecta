{-# LANGUAGE TupleSections #-}

-- | Generators compiled from annotated datatype grammars.
module Data.CFTA.Gen.Equality.DatatypeGenSpec (spec) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import Data.List (sort)
import Data.Ratio ((%))
import qualified Data.Set as Set
import Data.String (fromString)
import qualified Data.Tree as Tree
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)

import qualified Data.CFTA as FTA
import qualified Data.CFTA.Equality as Automaton
import Data.CFTA.Equality.Constraints (EqConstraints (EmptyConstraints))
import qualified Data.CFTA.Equality.Constraints as Paths
import qualified Data.CFTA.Gen.Equality as Core
import qualified Data.CFTA.Gen.Equality.QuickCheck as ECTAGen
import qualified Data.CFTA.Generic as Datatype
import qualified Data.CFTA.Interned as Interned
import Data.CFTA.Ranked.Internal.Sampler (Exact (..))

-- | Annotate the tuple constructor and leave its field datatypes unchanged.
equalFields :: [[Int]] -> Datatype.Constructor -> EqConstraints
equalFields positions constructor
    | Datatype.constructorName constructor == "(,)" = Paths.mkEqConstraints [map Paths.path positions]
    | otherwise = EmptyConstraints

spec :: Spec
spec = do
    describe "annotated datatype grammars" $ do
        it "counts and samples equal fields without rebuilding their datatype" $ do
            datatype <- either (fail . show) pure $ Datatype.deriveFTA @(Bool, Bool)
            let annotated = Datatype.annotateDatatype (equalFields [[0], [1]]) datatype
                generator = Core.fromDatatypeUpToDepth 1 annotated :: Core.ECTAGen Exact (Bool, Bool)
            Core.cardinality generator `shouldBe` Right 2
            fmap sort (traverse (Core.unrank generator) [0, 1])
                `shouldBe` Right [(False, False), (True, True)]
            runExact (Core.lowerWithRank generator)
                `shouldBe` [(1 % 2, fmap (rank,) $ Core.unrank generator rank) | rank <- [0, 1]]
            map (Core.unrank generator) (Core.shrinkRank generator 1)
                `shouldSatisfy` all (`elem` [Right (False, False), Right (True, True)])

        it "combines intersecting equality classes over three fields" $ do
            datatype <- either (fail . show) pure $ Datatype.deriveFTA @(Bool, Bool, Bool)
            let annotate constructor
                    | length (Datatype.constructorFields constructor) == 3 =
                        Paths.mkEqConstraints [map Paths.path [[0], [1]], map Paths.path [[1], [2]]]
                    | otherwise = EmptyConstraints
                generator = ECTAGen.fromDatatypeUpToDepth 1 $ Datatype.annotateDatatype annotate datatype
            ECTAGen.cardinality generator `shouldBe` Right 2
            fmap sort (traverse (ECTAGen.unrank generator) [0, 1])
                `shouldBe` Right [(False, False, False), (True, True, True)]

        it "compiles nested paths symbolically and rejects absent positions" $ do
            datatype <- either (fail . show) pure $ Datatype.deriveFTA @(Maybe Bool, Maybe Bool)
            let generator = ECTAGen.fromDatatypeUpToDepth 2 $ Datatype.annotateDatatype (equalFields [[0, 0], [1, 0]]) datatype
            ECTAGen.cardinality generator `shouldBe` Right 2
            fmap sort (traverse (ECTAGen.unrank generator) [0, 1])
                `shouldBe` Right [(Just False, Just False), (Just True, Just True)]

        it "keeps an exponential equal-list language compact" $ do
            datatype <- either (fail . show) pure $ Datatype.deriveFTA @([Bool], [Bool])
            let generator = ECTAGen.fromDatatypeUpToDepth 70 $ Datatype.annotateDatatype (equalFields [[0], [1]]) datatype
                count = 2 ^ (70 :: Int) - 1
            completed <- timeout 60000000 $ evaluate $ ECTAGen.cardinality generator == Right count
            completed `shouldBe` Just True
            case ECTAGen.unrank generator (count - 1) of
                Left err -> expectationFailure $ show err
                Right (left, right) -> do
                    left `shouldBe` right
                    length left `shouldBe` 69

        it "keeps an exponential nested-equality language compact" $ do
            datatype <- either (fail . show) pure $ Datatype.deriveFTA @(Maybe [Bool], Maybe [Bool])
            let generator = ECTAGen.fromDatatypeUpToDepth 71 $ Datatype.annotateDatatype (equalFields [[0, 0], [1, 0]]) datatype
                count = 2 ^ (70 :: Int) - 1
            completed <- timeout 10000000 $ evaluate $ ECTAGen.cardinality generator == Right count
            completed `shouldBe` Just True
            forM_ [0, count `div` 2, count - 1] $ \rank -> do
                selected <- timeout 10000000 $ evaluate $ case ECTAGen.unrank generator rank of
                    Right (Just left, Just right) -> left == right && length left <= 69
                    _ -> False
                selected `shouldBe` Just True

        it "counts overlapping exponential languages without enumerating either one" $ do
            let transition label children = FTA.Transition (fromString label) children EmptyConstraints
            graph <-
                either (fail . show) pure $
                    FTA.mkFTA
                        (0 :: Int)
                        [ (0, [transition "wrap" [1], transition "wrap" [2]])
                        , (1, [transition "nil" [], transition "cons" [3, 1]])
                        , (2, [transition "nil" [], transition "cons" [4, 2]])
                        , (3, [transition "a" [], transition "b" []])
                        , (4, [transition "b" [], transition "c" []])
                        ]
            let generator = ECTAGen.fromFTAUpToDepth 70 graph
                count = 2 * (2 ^ (70 :: Int) - 1) - 70
            completed <- timeout 10000000 $ evaluate $ ECTAGen.cardinality generator == Right count
            completed `shouldBe` Just True
            support <- either (fail . show) pure $ ECTAGen.support generator
            forM_ [0, count `div` 2, count - 1] $ \rank -> do
                selected <- timeout 10000000 $ evaluate $ case ECTAGen.unrank generator rank of
                    Right term -> Automaton.nodeRepresents support term
                    _ -> False
                selected `shouldBe` Just True

        it "agrees with bounded enumeration for intersecting nested constraints" $ do
            let transition label children guard = FTA.Transition (fromString label) children guard
                plain label children = transition label children EmptyConstraints
                equal = Paths.mkEqConstraints . map (map Paths.path)
                constraints =
                    map
                        equal
                        [ []
                        , [[[0], [1]]]
                        , [[[0, 0], [1, 0]]]
                        , [[[0], [1, 0]]]
                        , [[[0, 0], [1]]]
                        , [[[0, 0], [1, 1]], [[0, 1], [1, 0]]]
                        , [[[0], [1]], [[0, 0], [1, 1]]]
                        , [[[0], [0, 0]]]
                        ]
            forM_ constraints $ \guard -> do
                graph <-
                    either (fail . show) pure $
                        FTA.mkFTA
                            (0 :: Int)
                            [ (0, [transition "pair" [1, 1] guard, transition "pair" [2, 1] guard])
                            , (1, [plain "a" [], plain "b" [], plain "fork" [2, 2], transition "fork" [2, 2] $ equal [[[0], [1]]]])
                            , (2, [plain "a" [], plain "b" []])
                            ]
                let generator = ECTAGen.fromFTAUpToDepth 2 graph
                support <- either (fail . show) pure (Interned.fromFTA graph)
                let expected = Set.toAscList $ Set.fromList $ Automaton.getAllTerms support
                case expected of
                    [] -> ECTAGen.cardinality generator `shouldBe` Left ECTAGen.EmptyGenerator
                    _ -> do
                        ECTAGen.cardinality generator `shouldBe` Right (toInteger $ length expected)
                        fmap sort (traverse (ECTAGen.unrank generator) [0 .. toInteger (length expected) - 1]) `shouldBe` Right expected

        it "leaves unobserved descendants of a symbolic selection lazy" $ do
            let transition label children = FTA.Transition (fromString label) children EmptyConstraints
                equal = Paths.mkEqConstraints [map Paths.path [[0, 0], [1, 0]]]
            graph <-
                either (fail . show) pure
                    $ FTA.mkFTA (0 :: Int)
                    $ [ (0, [FTA.Transition (fromString "pair") [1, 1] equal])
                      , (1, [transition "box" [72]])
                      , (2, [transition "leaf" []])
                      ]
                        <> [(level, [transition "fork" [level - 1, level - 1]]) | level <- [3 .. 72]]
            let generator = ECTAGen.fromFTAUpToDepth 72 graph
            completed <-
                timeout 10000000 $
                    evaluate $
                        ECTAGen.cardinality generator == Right 1
                            && case ECTAGen.unrank generator 0 of
                                Right (Tree.Node symbol _) -> symbol == fromString "pair"
                                Left _ -> False
            completed `shouldBe` Just True

        it "shares deep equality contexts across irrelevant constructor choices" $ do
            let transition label children = FTA.Transition (fromString label) children EmptyConstraints
                equal = Paths.mkEqConstraints [map Paths.path [0 : replicate 70 0, 1 : replicate 70 0]]
            graph <-
                either (fail . show) pure
                    $ FTA.mkFTA (0 :: Int)
                    $ [ (0, [FTA.Transition (fromString "pair") [71, 71] equal])
                      , (1, [transition "a" [], transition "b" []])
                      ]
                        <> [(level, [transition "f" [level - 1], transition "g" [level - 1]]) | level <- [2 .. 71]]
            let generator = ECTAGen.fromFTAUpToDepth 71 graph
            completed <- timeout 10000000 $ evaluate $ ECTAGen.cardinality generator == Right (2 ^ (141 :: Int))
            completed `shouldBe` Just True

        it "retains one term rank for overlapping handwritten alternatives" $ do
            let transition label children = FTA.Transition (fromString label) children EmptyConstraints
            graph <-
                either (fail . show) pure $
                    FTA.mkFTA
                        (0 :: Int)
                        [ (0, [transition "wrap" [1], transition "wrap" [2]])
                        , (1, [transition "a" []])
                        , (2, [transition "a" [], transition "b" []])
                        ]
            ECTAGen.cardinality (ECTAGen.fromFTAUpToDepth 1 graph) `shouldBe` Right 2
            let equal = Paths.mkEqConstraints [map Paths.path [[0], [1]]]
            intersection <-
                either (fail . show) pure $
                    FTA.mkFTA
                        (0 :: Int)
                        [ (0, [FTA.Transition (fromString "pair") [1, 2] equal])
                        , (1, [transition "a" [], transition "b" []])
                        , (2, [transition "b" [], transition "c" []])
                        ]
            let generator = ECTAGen.fromFTAUpToDepth 1 intersection
            ECTAGen.cardinality generator `shouldBe` Right 1
            ECTAGen.unrank generator 0
                `shouldBe` Right (Tree.Node (fromString "pair") [Tree.Node (fromString "b") [], Tree.Node (fromString "b") []])
