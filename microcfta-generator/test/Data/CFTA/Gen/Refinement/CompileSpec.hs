module Data.CFTA.Gen.Refinement.CompileSpec (spec) where

import Control.Monad (forM_, void)
import Data.List (sort)
import Data.Ratio ((%))
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Gen.Refinement.ExampleSupport (nonNegative)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTA
import Data.CFTA.Gen.Refinement.TestSupport (compileOrFail, massesByRank, rightOrFail, values)
import Data.CFTA.Refinement (
    Entailment (Entailment),
    Guard (Bottom),
    LiquidSymbol (LiquidSymbol),
    Refinement,
    Verdict (Yes),
 )
import Data.CFTA.Refinement.Expression (value, (./=.), (.==.))
import Data.CFTA.Refinement.Guard (allOf, isSameTermAs, isSubtypeOf, requires, unconstrained)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import qualified Language.Fixpoint.Types as Fixpoint

-- | Exact refinement attached to one integer.
exact :: Int -> Refinement
exact integer = value .==. integer

-- | Refinement used as a division precondition.
nonZero :: Refinement
nonZero = value ./=. (0 :: Int)

spec :: Spec
spec =
    describe "solver compilation" $ do
        it "preserves source order when observation keys have another order" $
            withZ3 declarations $ \solver -> do
                let atoms :: LTA.LTAGen Int
                    atoms =
                        LTA.pool
                            [ LTA.Refined 2 "z" $ exact 2
                            , LTA.Refined 0 "a" $ exact 0
                            , LTA.Refined 1 "m" $ exact 1
                            ]
                    generator =
                        LTA.node
                            "pair"
                            (\left right -> allOf [left `requires` nonNegative, right `requires` nonNegative])
                            $ (,) <$> atoms <*> atoms
                compiled <- compileOrFail solver generator
                expected <- LTA.validOutcomes solver generator
                fmap sort expected `shouldBe` Right (sort $ values compiled)
                values compiled `shouldBe` [(left, right) | left <- [2, 0, 1], right <- [2, 0, 1]]

        it "retains repeated source ranks after mapping their values" $
            withZ3 declarations $ \solver -> do
                let generator =
                        void
                            ( LTA.pool
                                [ LTA.Refined (1 :: Int) "z" $ exact 1
                                , LTA.Refined 1 "z" $ exact 1
                                , LTA.Refined 0 "a" $ exact 0
                                ]
                            )
                compiled <- compileOrFail solver generator
                expected <- LTA.validOutcomes solver generator
                LTA.cardinality compiled `shouldBe` Right 3
                fmap length expected `shouldBe` Right 3
                LTA.unrank compiled 0 `shouldBe` LTA.unrank compiled 1

        it "samples exact source weights across unequal and rejected branches" $
            withZ3 declarations $ \solver -> do
                let atoms =
                        LTA.frequency
                            [
                                ( 3
                                , LTA.pool
                                    [ LTA.Refined (2 :: Int) "z" $ exact 2
                                    , LTA.Refined 0 "m" $ exact 0
                                    ]
                                )
                            , (1, LTA.pool [LTA.Refined 1 "a" $ exact 1])
                            , (7, LTA.pool [LTA.Refined 0 "trailing" $ exact 0])
                            ]
                    generator =
                        LTA.node
                            "pair"
                            (\left right -> allOf [left `requires` nonZero, right `requires` nonZero])
                            $ (,) <$> atoms <*> atoms
                compiled <- compileOrFail solver generator
                expected <- LTA.validOutcomes solver generator
                values compiled `shouldBe` [(2, 2), (2, 1), (1, 2), (1, 1)]
                Right (values compiled) `shouldBe` expected
                -- The retained members keep the weights of their branches: two
                -- is drawn with weight 3 shared by its pool, one with weight 1.
                massesByRank compiled `shouldBe` zip [0 .. 3] [9 % 25, 6 % 25, 6 % 25, 4 % 25]

        it "recognizes a constant-false factor without evaluating either huge product" $ do
            let solver = Entailment $ \_ _ -> error "a constant-empty product queried the solver"
                dead = LTA.node "dead" Bottom (pure ())
                pair left right =
                    void (LTA.node "pair" unconstrained ((,) <$> left <*> right))
            forM_ [pair dead unavailableProduct, pair unavailableProduct dead] $ \generator -> do
                result <- LTA.compile solver generator
                (result >>= LTA.cardinality) `shouldBe` Left LTA.EmptyGenerator

        it "skips a huge right factor after semantic rejection on the left" $
            withZ3 declarations $ \solver -> do
                let dead =
                        LTA.node "dead" (`requires` nonZero) $
                            LTA.leaf () "zero" (exact 0)
                    generator = LTA.node "pair" unconstrained ((,) <$> dead <*> unavailableProduct)
                result <- LTA.compile solver generator
                (result >>= LTA.cardinality) `shouldBe` Left LTA.EmptyGenerator

        it "compiles leaf equality from the observed roots" $
            withZ3 declarations $ \solver -> do
                let equal = LTA.node "pair" isSameTermAs $ bitForest 2
                compiled <- compileOrFail solver equal
                expected <- LTA.validOutcomes solver equal
                Right (values compiled) `shouldBe` expected
                values compiled `shouldBe` [[0, 0], [1, 1]]

        it "compiles a large supported product without materialization" $
            withZ3 declarations $ \solver -> do
                let generator = LTA.node "bits" unconstrained $ bitForest 64
                    total = 2 ^ (64 :: Int)
                compiled <- LTA.compile solver generator >>= rightOrFail
                LTA.cardinality compiled `shouldBe` Right total
                LTA.unrank compiled 0 `shouldBe` Right (replicate 64 0)
                LTA.unrank compiled (total - 1) `shouldBe` Right (replicate 64 1)

        it "finishes shrinking a compact two-member language with 64 binary sources" $
            withZ3 declarations $ \solver -> do
                compiled <- LTA.compile solver (homogeneousBits 64) >>= rightOrFail
                LTA.cardinality compiled `shouldBe` Right 2
                values compiled `shouldBe` [replicate 64 0, replicate 64 1]
                completed <- timeout 60000000 $ pure $! all (< 1) (LTA.shrinkRank compiled 1) && null (LTA.shrinkRank compiled 0)
                completed `shouldBe` Just True

        it "computes a root refinement from the children's roots" $
            withZ3 declarations $ \solver -> do
                compiled <- LTA.compile solver (homogeneousBits 3) >>= rightOrFail
                values compiled `shouldBe` [replicate 3 0, replicate 3 1]
                decided <- LTA.compile (Entailment $ \_ _ -> pure Yes) (homogeneousBits 2)
                (decided >>= LTA.cardinality) `shouldBe` Right 4

-- | Build a product whose candidate count exceeds machine integers at width 64.
bitForest :: Int -> LTA.LTAGen [Int]
bitForest width =
    foldr (\_ rest -> (:) <$> bits <*> rest) (pure []) [1 .. width]
  where
    bits =
        LTA.pool
            [ LTA.Refined 0 "zero" $ exact 0
            , LTA.Refined 1 "one" $ exact 1
            ]

-- | A large fallback whose values must remain unobserved.
unavailableProduct :: LTA.LTAGen [Int]
unavailableProduct =
    LTA.node "computed" unconstrained $ error "an empty product evaluated a generated value" <$ bitForest 64

-- | Retain homogeneous vectors of positive width with small local relations.
homogeneousBits :: Int -> LTA.LTAGen [Int]
homogeneousBits width = foldr (\_ rest -> prepend rest) ((: []) <$> bit) [2 .. width]
  where
    bit = LTA.pool [LTA.Refined (0 :: Int) "zero" nonNegative, LTA.Refined 1 "one" $ exact 1]
    prepend rest =
        LTA.refinedNodeByRoots "cons" firstRefinement equivalent $
            (:) <$> bit <*> rest
    firstRefinement (LiquidSymbol _ refinement : _) = refinement
    firstRefinement [] = error "a homogeneous vector node has no children"
    equivalent left right = allOf [left `isSubtypeOf` right, right `isSubtypeOf` left]

-- | Liquid Fixpoint declarations needed by the exact integer refinements.
declarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
declarations = [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)]
