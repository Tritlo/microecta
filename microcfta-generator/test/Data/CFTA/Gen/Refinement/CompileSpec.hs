module Data.CFTA.Gen.Refinement.CompileSpec (spec) where

import Control.Monad (forM_, void)
import Data.List (sort)
import Data.Ratio ((%))
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Gen.Refinement.ExampleSupport (nonNegative)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
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
                let atoms :: LTAGen.LTAGen Int
                    atoms =
                        LTAGen.pool
                            [ LTAGen.Refined 2 "z" $ exact 2
                            , LTAGen.Refined 0 "a" $ exact 0
                            , LTAGen.Refined 1 "m" $ exact 1
                            ]
                    generator =
                        LTAGen.node
                            "pair"
                            (\left right -> allOf [left `requires` nonNegative, right `requires` nonNegative])
                            $ (,) <$> atoms <*> atoms
                compiled <- compileOrFail solver generator
                expected <- LTAGen.validOutcomes solver generator
                fmap sort expected `shouldBe` Right (sort $ values compiled)
                values compiled `shouldBe` [(left, right) | left <- [2, 0, 1], right <- [2, 0, 1]]

        it "retains repeated source ranks after mapping their values" $
            withZ3 declarations $ \solver -> do
                let generator =
                        void
                            ( LTAGen.pool
                                [ LTAGen.Refined (1 :: Int) "z" $ exact 1
                                , LTAGen.Refined 1 "z" $ exact 1
                                , LTAGen.Refined 0 "a" $ exact 0
                                ]
                            )
                compiled <- compileOrFail solver generator
                expected <- LTAGen.validOutcomes solver generator
                LTAGen.cardinality compiled `shouldBe` Right 3
                fmap length expected `shouldBe` Right 3
                LTAGen.unrank compiled 0 `shouldBe` LTAGen.unrank compiled 1

        it "samples exact source weights across unequal and rejected branches" $
            withZ3 declarations $ \solver -> do
                let atoms =
                        LTAGen.frequency
                            [
                                ( 3
                                , LTAGen.pool
                                    [ LTAGen.Refined (2 :: Int) "z" $ exact 2
                                    , LTAGen.Refined 0 "m" $ exact 0
                                    ]
                                )
                            , (1, LTAGen.pool [LTAGen.Refined 1 "a" $ exact 1])
                            , (7, LTAGen.pool [LTAGen.Refined 0 "trailing" $ exact 0])
                            ]
                    generator =
                        LTAGen.node
                            "pair"
                            (\left right -> allOf [left `requires` nonZero, right `requires` nonZero])
                            $ (,) <$> atoms <*> atoms
                compiled <- compileOrFail solver generator
                expected <- LTAGen.validOutcomes solver generator
                values compiled `shouldBe` [(2, 2), (2, 1), (1, 2), (1, 1)]
                Right (values compiled) `shouldBe` expected
                -- The retained members keep the weights of their branches: two
                -- is drawn with weight 3 shared by its pool, one with weight 1.
                massesByRank compiled `shouldBe` zip [0 .. 3] [9 % 25, 6 % 25, 6 % 25, 4 % 25]

        it "recognizes a constant-false factor without evaluating either huge product" $ do
            let solver = Entailment $ \_ _ -> error "a constant-empty product queried the solver"
                dead = LTAGen.node "dead" Bottom (pure ())
                pair left right =
                    void (LTAGen.node "pair" unconstrained ((,) <$> left <*> right))
            forM_ [pair dead unavailableProduct, pair unavailableProduct dead] $ \generator -> do
                result <- LTAGen.compile solver generator
                (result >>= LTAGen.cardinality) `shouldBe` Left LTAGen.EmptyGenerator

        it "skips a huge right factor after semantic rejection on the left" $
            withZ3 declarations $ \solver -> do
                let dead =
                        LTAGen.node "dead" (`requires` nonZero) $
                            LTAGen.leaf () "zero" (exact 0)
                    generator = LTAGen.node "pair" unconstrained ((,) <$> dead <*> unavailableProduct)
                result <- LTAGen.compile solver generator
                (result >>= LTAGen.cardinality) `shouldBe` Left LTAGen.EmptyGenerator

        it "compiles leaf equality from the observed roots" $
            withZ3 declarations $ \solver -> do
                let equal = LTAGen.node "pair" isSameTermAs $ bitForest 2
                compiled <- compileOrFail solver equal
                expected <- LTAGen.validOutcomes solver equal
                Right (values compiled) `shouldBe` expected
                values compiled `shouldBe` [[0, 0], [1, 1]]

        it "compiles a large supported product without materialization" $
            withZ3 declarations $ \solver -> do
                let generator = LTAGen.node "bits" unconstrained $ bitForest 64
                    total = 2 ^ (64 :: Int)
                compiled <- LTAGen.compile solver generator >>= rightOrFail
                LTAGen.cardinality compiled `shouldBe` Right total
                LTAGen.unrank compiled 0 `shouldBe` Right (replicate 64 0)
                LTAGen.unrank compiled (total - 1) `shouldBe` Right (replicate 64 1)

        it "finishes shrinking a compact two-member language with 64 binary sources" $
            withZ3 declarations $ \solver -> do
                compiled <- LTAGen.compile solver (homogeneousBits 64) >>= rightOrFail
                LTAGen.cardinality compiled `shouldBe` Right 2
                values compiled `shouldBe` [replicate 64 0, replicate 64 1]
                completed <- timeout 60000000 $ pure $! all (< 1) (LTAGen.shrinkRank compiled 1) && null (LTAGen.shrinkRank compiled 0)
                completed `shouldBe` Just True

        it "computes a root refinement from the children's roots" $
            withZ3 declarations $ \solver -> do
                compiled <- LTAGen.compile solver (homogeneousBits 3) >>= rightOrFail
                values compiled `shouldBe` [replicate 3 0, replicate 3 1]
                decided <- LTAGen.compile (Entailment $ \_ _ -> pure Yes) (homogeneousBits 2)
                (decided >>= LTAGen.cardinality) `shouldBe` Right 4

-- | Build a product whose candidate count exceeds machine integers at width 64.
bitForest :: Int -> LTAGen.LTAGen [Int]
bitForest width =
    foldr (\_ rest -> (:) <$> bits <*> rest) (pure []) [1 .. width]
  where
    bits =
        LTAGen.pool
            [ LTAGen.Refined 0 "zero" $ exact 0
            , LTAGen.Refined 1 "one" $ exact 1
            ]

-- | A large fallback whose values must remain unobserved.
unavailableProduct :: LTAGen.LTAGen [Int]
unavailableProduct =
    LTAGen.node "computed" unconstrained $ error "an empty product evaluated a generated value" <$ bitForest 64

-- | Retain homogeneous vectors of positive width with small local relations.
homogeneousBits :: Int -> LTAGen.LTAGen [Int]
homogeneousBits width = foldr (\_ rest -> prepend rest) ((: []) <$> bit) [2 .. width]
  where
    bit = LTAGen.pool [LTAGen.Refined (0 :: Int) "zero" nonNegative, LTAGen.Refined 1 "one" $ exact 1]
    prepend rest =
        LTAGen.refinedNodeByRoots "cons" firstRefinement equivalent $
            (:) <$> bit <*> rest
    firstRefinement (LiquidSymbol _ refinement : _) = refinement
    firstRefinement [] = error "a homogeneous vector node has no children"
    equivalent left right = allOf [left `isSubtypeOf` right, right `isSubtypeOf` left]

-- | Liquid Fixpoint declarations needed by the exact integer refinements.
declarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
declarations = [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)]
