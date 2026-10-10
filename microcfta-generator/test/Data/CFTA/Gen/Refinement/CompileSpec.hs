module Data.CFTA.Gen.Refinement.CompileSpec (spec) where

-- A test reads the product @elements [2] <* pure ()@, which has one term.
{- HLINT ignore "Redundant <*" -}

import Control.Exception (evaluate)
import Control.Monad (forM_, void)
import Data.List (mapAccumL, sort)
import qualified Data.Map.Strict as Map
import Data.Ratio ((%))
import Data.String (fromString)
import qualified Data.Tree as Tree
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Gen.Refinement.ExampleSupport (nonNegative)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Gen.Refinement.TestSupport (compileOrFail, massesByRank, rightOrFail, values)
import Data.CFTA.Index (Cardinality (..), Rank (..), everyRank)
import Data.CFTA.Ranked.Internal.Sampler (Exact (..))
import Data.CFTA.Refinement (
    Entailment (Entailment),
    Guard (Bottom, Satisfies),
    Node (Mu, Node),
    Symbol (RefinedSymbol),
    Verdict (Yes),
    noConstraint,
    nodeCount,
    path,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (
    Refinement,
    literal,
    refinementFormula,
    true,
    (.&&),
    (./=),
    (.<),
    (.<=),
    (.==),
    (.>),
    (.>=),
 )
import Data.CFTA.Refinement.Guard (
    allOf,
    anyOf,
    descendant,
    isSameTermAs,
    isSubtypeOf,
    notGuard,
    requires,
    unconstrained,
 )
import Data.CFTA.Refinement.Lattice (latticeEntailment)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import qualified Language.Fixpoint.Types as Fixpoint

-- | Exact refinement attached to one integer.
exact :: Int -> Refinement
exact integer v = v .== fromIntegral integer

-- | Refinement used as a division precondition.
nonZero :: Refinement
nonZero v = v ./= 0

spec :: Spec
spec = do
    describe "solver compilation" $ do
        it "preserves source order when observation keys have another order" $
            withZ3 declarations $ \solver -> do
                let atoms :: LTAGen.LTAGen Int
                    atoms =
                        LTAGen.namedPool
                            [ LTAGen.Refined 2 "z" $ exact 2
                            , LTAGen.Refined 0 "a" $ exact 0
                            , LTAGen.Refined 1 "m" $ exact 1
                            ]
                    generator =
                        LTAGen.refinedNode
                            "pair"
                            (const true)
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
                            ( LTAGen.namedPool
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
                                , LTAGen.namedPool
                                    [ LTAGen.Refined (2 :: Int) "z" $ exact 2
                                    , LTAGen.Refined 0 "m" $ exact 0
                                    ]
                                )
                            , (1, LTAGen.namedPool [LTAGen.Refined 1 "a" $ exact 1])
                            , (7, LTAGen.namedPool [LTAGen.Refined 0 "trailing" $ exact 0])
                            ]
                    generator =
                        LTAGen.refinedNode
                            "pair"
                            (const true)
                            (\left right -> allOf [left `requires` nonZero, right `requires` nonZero])
                            $ (,) <$> atoms <*> atoms
                compiled <- compileOrFail solver generator
                expected <- LTAGen.validOutcomes solver generator
                values compiled `shouldBe` [(2, 2), (2, 1), (1, 2), (1, 1)]
                Right (values compiled) `shouldBe` expected
                -- The retained members keep the weights of their branches: two
                -- is drawn with weight 3 shared by its pool, one with weight 1.
                massesByRank compiled `shouldBe` zip [0 .. 3] [9 % 25, 6 % 25, 6 % 25, 4 % 25]

        it "keeps the weights of an atomic choice whether or not a guard reads it" $
            withZ3 declarations $ \solver -> do
                let weighted =
                        LTAGen.atomic $
                            LTAGen.frequency [(9, LTAGen.leaf (0 :: Int) "a" (exact 0)), (1, LTAGen.leaf 1 "b" (exact 1))]
                    pair guard = LTAGen.refinedNode "pair" (const true) guard $ (,) <$> weighted <*> LTAGen.elements [7 :: Int]
                forM_ [pair (\left _ -> left `requires` nonNegative), pair (\_ right -> right `requires` nonNegative)] $ \generator -> do
                    compiled <- compileOrFail solver generator
                    massesByRank compiled `shouldBe` [(0, 9 % 10), (1, 1 % 10)]

        it "keeps the sizes of an atomic choice whether or not a guard reads it" $
            withZ3 declarations $ \solver -> do
                -- Each member of the atom has size one, also the member whose
                -- term has two nodes.
                let atom =
                        LTAGen.atomic $
                            LTAGen.oneof [LTAGen.leaf (0 :: Int) "a" (const true), LTAGen.node "wrap" $ LTAGen.leaf 1 "b" (const true)]
                    outer guard = LTAGen.refinedNode "outer" (const true) guard atom
                compiled <- compileOrFail solver $ outer (`requires` const true)
                map (LTAGen.sizeOfRank compiled) [0, 1] `shouldBe` map (LTAGen.sizeOfRank $ outer noConstraint) [0, 1]
                LTAGen.pmf (LTAGen.upToSize 1 compiled) `shouldBe` Right [(0, 1 % 2), (1, 1 % 2)]
                map (LTAGen.smallerMembers compiled) [0, 1] `shouldBe` [[], []]

        it "keeps the sizes of a built source whether or not a guard reads it" $
            withZ3 declarations $ \solver -> do
                -- Behind keyed and ungroup a language is a built source. A node
                -- adds no source choice and a product adds the sizes of its
                -- parts, so a member's size is not the number of its nodes.
                let choice = LTAGen.oneof [LTAGen.leaf (0 :: Int) "a" (const true), LTAGen.node "wrap" $ LTAGen.leaf 1 "b" (const true)]
                    built = LTAGen.ungroup $ LTAGen.keyed () choice
                    outer guard = LTAGen.refinedNode "outer" (const true) guard built
                    paired =
                        LTAGen.ungroup
                            $ LTAGen.keyed ()
                            $ LTAGen.node "pair"
                            $ (,) <$> LTAGen.atomic choice <*> LTAGen.leaf (7 :: Int) "c" (const true)
                    outerPair guard = LTAGen.refinedNode "outer" (const true) guard paired
                compiled <- compileOrFail solver $ outer (`requires` const true)
                map (LTAGen.sizeOfRank compiled) [0, 1] `shouldBe` map (LTAGen.sizeOfRank built) [0, 1]
                LTAGen.pmf (LTAGen.upToSize 1 compiled) `shouldBe` LTAGen.pmf (LTAGen.upToSize 1 $ outer noConstraint)
                map (LTAGen.smallerMembers compiled) [0, 1] `shouldBe` [[], []]
                compiledPair <- compileOrFail solver $ outerPair (`requires` const true)
                map (LTAGen.sizeOfRank compiledPair) [0, 1] `shouldBe` map (LTAGen.sizeOfRank paired) [0, 1]
                LTAGen.pmf (LTAGen.upToSize 2 compiledPair) `shouldBe` LTAGen.pmf (LTAGen.upToSize 2 $ outerPair noConstraint)

        it "keeps the sizes of a node with several children when a guard reads one" $
            withZ3 declarations $ \solver -> do
                -- Pairing the children is not a source choice, so each member
                -- has the size of its children together.
                let choice = LTAGen.oneof [LTAGen.leaf (0 :: Int) "a" (const true), LTAGen.node "w" $ LTAGen.leaf 1 "b" (const true)]
                    leafC = LTAGen.leaf (7 :: Int) "c" (const true)
                    pair = (,) <$> choice <*> leafC
                    triple = (,,) <$> choice <*> leafC <*> leafC
                    readsChild = Satisfies (path [0]) true
                compiledPair <- compileOrFail solver $ LTAGen.refinedNode "n" (const true) readsChild pair
                map (LTAGen.sizeOfRank compiledPair) [0, 1] `shouldBe` map (LTAGen.sizeOfRank $ LTAGen.node "n" pair) [0, 1]
                LTAGen.cardinality (LTAGen.upToSize 2 compiledPair) `shouldBe` Right 2
                compiledTriple <- compileOrFail solver $ LTAGen.refinedNode "n" (const true) readsChild triple
                map (LTAGen.sizeOfRank compiledTriple) [0, 1] `shouldBe` map (LTAGen.sizeOfRank $ LTAGen.node "n" triple) [0, 1]

        it "keeps the weights inside a size class of a built source whether or not a guard reads it" $
            withZ3 declarations $ \solver -> do
                -- The weights of the atomic choice decide inside the size class
                -- two. A guard that reads the child of each member puts a(..)
                -- and wrap(b) into different groups, across p and q, so the
                -- groups have these weights and not their member counts.
                let weighted =
                        LTAGen.atomic $
                            LTAGen.frequency
                                [(1, LTAGen.leaf (0 :: Int) "a" (const true)), (3, LTAGen.node "wrap" $ LTAGen.leaf 1 "b" (const true))]
                    tagged label = LTAGen.node label $ (,) <$> weighted <*> LTAGen.leaf (7 :: Int) "c" (const true)
                    built = LTAGen.ungroup $ LTAGen.keyed () $ LTAGen.oneof [tagged "p", tagged "q"]
                    outer guard = LTAGen.refinedNode "outer" (const true) guard built
                    expected = [((0, 7), 1 % 4), ((1, 7), 3 % 4)]
                    sampled generator = Map.toAscList $ Map.fromListWith (+) [(value, mass) | (mass, Right value) <- runExact $ LTAGen.lowerVia generator]
                LTAGen.pmf (LTAGen.upToSize 2 $ outer noConstraint) `shouldBe` Right expected
                forM_ [Satisfies (path [0]) true, Satisfies (path [0, 0]) true] $ \guard -> do
                    compiled <- compileOrFail solver $ outer guard
                    LTAGen.pmf (LTAGen.upToSize 2 compiled) `shouldBe` Right expected
                    sampled (LTAGen.upToSize 2 compiled) `shouldBe` expected

        it "keeps the weights of each size class when the groups of a built source have several sizes" $
            withZ3 declarations $ \solver -> do
                -- Each group of a(..) and of wrap(b) has one member of size one
                -- and one of size two. The weights of the atom are 1:3 at size
                -- one and 3:1 at size two.
                let atom weightA weightB =
                        LTAGen.atomic $
                            LTAGen.frequency
                                [(weightA, LTAGen.leaf (0 :: Int) "a" (const true)), (weightB, LTAGen.node "wrap" $ LTAGen.leaf 1 "b" (const true))]
                    built =
                        LTAGen.ungroup
                            $ LTAGen.keyed ()
                            $ LTAGen.oneof
                                [ LTAGen.node "p" $ Left <$> atom 1 3
                                , LTAGen.node "q" $ fmap Right $ (,) <$> atom 3 1 <*> LTAGen.leaf (7 :: Int) "c" (const true)
                                ]
                    outer guard = LTAGen.refinedNode "outer" (const true) guard built
                    expected = [(Left 0, 1 % 8), (Left 1, 3 % 8), (Right (0, 7), 3 % 8), (Right (1, 7), 1 % 8)]
                    sampled generator = Map.toAscList $ Map.fromListWith (+) [(value, mass) | (mass, Right value) <- runExact $ LTAGen.lowerVia generator]
                LTAGen.pmf (LTAGen.upToSize 2 $ outer noConstraint) `shouldBe` Right expected
                compiled <- compileOrFail solver $ outer $ Satisfies (path [0, 0]) true
                LTAGen.pmf (LTAGen.upToSize 2 compiled) `shouldBe` Right expected
                sampled (LTAGen.upToSize 2 compiled) `shouldBe` expected

        it "keeps the weights inside a size class when a guard reads one child of a pair" $
            withZ3 declarations $ \solver -> do
                -- A member of size three splits as one and two, or as two and
                -- one. The weights of the left groups differ by size class, so
                -- they choose the split, and each part keeps its weights.
                let atom weightA weightB =
                        LTAGen.atomic $
                            LTAGen.frequency
                                [(weightA, LTAGen.leaf (0 :: Int) "a" (const true)), (weightB, LTAGen.node "wrap" $ LTAGen.leaf 1 "b" (const true))]
                    left =
                        LTAGen.ungroup
                            $ LTAGen.keyed ()
                            $ LTAGen.oneof
                                [ LTAGen.node "p" $ Left <$> atom 1 3
                                , LTAGen.node "q" $ fmap Right $ (,) <$> atom 3 1 <*> LTAGen.leaf (7 :: Int) "c" (const true)
                                ]
                    right =
                        LTAGen.oneof
                            [ LTAGen.leaf (5 :: Int) "x" (const true)
                            , LTAGen.node "y" $ (+) <$> LTAGen.leaf 6 "z" (const true) <*> LTAGen.leaf 0 "o" (const true)
                            ]
                    outer guard = LTAGen.refinedNode "outer" (const true) guard $ (,) <$> left <*> right
                    sampled generator = Map.toAscList $ Map.fromListWith (+) [(value, mass) | (mass, Right value) <- runExact $ LTAGen.lowerVia generator]
                    expected = LTAGen.pmf $ LTAGen.upToSize 3 $ outer noConstraint
                compiled <- compileOrFail solver $ outer $ Satisfies (path [0, 0]) true
                LTAGen.pmf (LTAGen.upToSize 3 compiled) `shouldBe` expected
                Right (sampled $ LTAGen.upToSize 3 compiled) `shouldBe` expected
                LTAGen.pmf compiled `shouldBe` LTAGen.pmf (outer noConstraint)

        it "keeps the weights inside a size class when a node closes an integer leaf beside a guarded child" $
            withZ3 declarations $ \solver -> do
                -- The node closes the integer leaf of each tuple of groups.
                -- The choices of the leaf have two and three points, so each
                -- closed group weighs its points and its own weights.
                let atom weightA weightB =
                        LTAGen.atomic $
                            LTAGen.frequency
                                [(weightA, LTAGen.leaf (0 :: Int) "a" (const true)), (weightB, LTAGen.node "wrap" $ LTAGen.leaf 1 "b" (const true))]
                    left =
                        LTAGen.ungroup
                            $ LTAGen.keyed ()
                            $ LTAGen.oneof
                                [ LTAGen.node "p" $ Left <$> atom 1 3
                                , LTAGen.node "q" $ fmap Right $ (,) <$> atom 3 1 <*> LTAGen.leaf (7 :: Int) "c" (const true)
                                ]
                    digits :: Integer -> Integer -> LTAGen.LTAGen Integer
                    digits low high = LTAGen.every `LTAGen.satisfying` (\v -> literal low .<= v .&& v .<= literal high)
                    right = LTAGen.oneof [digits 8 9, digits 1 3]
                    outer guard = LTAGen.refinedNode "outer" (const true) guard $ (,) <$> left <*> right
                    sampled generator = Map.toAscList $ Map.fromListWith (+) [(value, mass) | (mass, Right value) <- runExact $ LTAGen.lowerVia generator]
                plain <- compileOrFail solver $ outer noConstraint
                compiled <- compileOrFail solver $ outer $ Satisfies (path [0, 0]) true
                let expected = LTAGen.pmf $ LTAGen.upToSize 4 plain
                LTAGen.pmf (LTAGen.upToSize 4 compiled) `shouldBe` expected
                Right (sampled $ LTAGen.upToSize 4 compiled) `shouldBe` expected
                LTAGen.pmf compiled `shouldBe` LTAGen.pmf plain

        it "keeps the weights inside a size class when the top closes the integer leaf of a result" $
            withZ3 declarations $ \solver -> do
                -- The guard keeps the members with the atom a, which weighs 1
                -- against 3. The result of each node is its integer leaf, so
                -- the leaf stays open until the top closes it. The choice must
                -- weigh the kept members as it does for listed integers.
                let atom = LTAGen.atomic $ LTAGen.frequency [(1, LTAGen.leaf (0 :: Int) "a" (.== 0)), (3, LTAGen.leaf 1 "b" (.== 1))]
                    left = LTAGen.ungroup $ LTAGen.keyed () $ LTAGen.oneof [LTAGen.node "p" atom, LTAGen.node "q" $ (+ 10) <$> atom]
                    keepsA = Satisfies (path [0, 0]) (refinementFormula (.== 0))
                    choice :: LTAGen.LTAGen Integer -> LTAGen.LTAGen (Int, Integer)
                    choice digit =
                        LTAGen.oneof
                            [ (LTAGen.refinedNode "outer" (const true) keepsA `LTAGen.ensuring` (\_ d -> d)) $ (,) <$> left <*> digit
                            , (LTAGen.refinedNode "other" (const true) noConstraint `LTAGen.ensuring` (\_ d -> d)) $
                                (,) <$> LTAGen.leaf 5 "x" (const true) <*> digit
                            ]
                    sampled generator = Map.toAscList $ Map.fromListWith (+) [(value, mass) | (mass, Right value) <- runExact $ LTAGen.lowerVia generator]
                open <- compileOrFail solver $ choice $ LTAGen.every `LTAGen.satisfying` (\v -> 8 .<= v .&& v .<= 9)
                closed <- compileOrFail solver $ choice $ LTAGen.elements [8, 9]
                let expected = LTAGen.pmf $ LTAGen.upToSize 4 closed
                LTAGen.pmf (LTAGen.upToSize 4 open) `shouldBe` expected
                Right (sampled $ LTAGen.upToSize 4 open) `shouldBe` expected
                LTAGen.pmf open `shouldBe` LTAGen.pmf closed

        it "refuses a guard that reads the children of a choice of products" $
            withZ3 declarations $ \solver -> do
                let pairs =
                        LTAGen.oneof
                            [ (,) <$> LTAGen.elements [0, 1 :: Int] <*> LTAGen.elements [5 :: Int]
                            , (,) <$> LTAGen.elements [0, 1] <*> LTAGen.elements [6]
                            ]
                    readsChoice = LTAGen.refinedNode "pair" (const true) (`requires` nonNegative) pairs
                    readsLater =
                        LTAGen.refinedNode "pair" (const true) (\_ later -> later `requires` nonNegative) $
                            (,) <$> pairs <*> LTAGen.elements [0 :: Int]
                forM_ [void readsChoice, void readsLater] $ \generator -> do
                    result <- LTAGen.compileWith solver generator
                    (result >>= LTAGen.cardinality) `shouldBe` Left LTAGen.ChildNotOneTerm
                unguarded <- LTAGen.compileWith solver $ LTAGen.node "pair" pairs
                (unguarded >>= LTAGen.cardinality) `shouldBe` Right 4

        it "reads the leafness of a node from its term" $
            -- The child of each node "a" has one position and gives no term,
            -- so the term of the node is a leaf, as the term of the leaf is.
            forM_ [LTAGen.oneof [pure 1, pure 2], LTAGen.fromIndexed (LTAGen.Indexed 2 (\(Rank rank) -> rank + 1))] $ \inner -> do
                let pair :: LTAGen.LTAGen (Integer, Integer)
                    pair = (,) <$> LTAGen.node "a" inner <*> LTAGen.leaf 3 "a" (const true)
                    same = LTAGen.refinedNode "p" (const true) isSameTermAs pair
                    different = LTAGen.refinedNode "p" (const true) (\x y -> notGuard (isSameTermAs x y)) pair
                forM_ [(same, [(1, 3), (2, 3)]), (different, [])] $ \(generator, expected) -> do
                    checked <- LTAGen.validOutcomes latticeEntailment generator
                    checked `shouldBe` Right expected
                    compiled <- LTAGen.compileWith latticeEntailment generator
                    fmap (sort . values) compiled `shouldBe` Right expected

        it "refuses an equality that reads a node whose members are leaves and non-leaves" $ do
            let mixed :: LTAGen.LTAGen (Integer, Integer)
                mixed =
                    LTAGen.refinedNode "p" (const true) isSameTermAs $
                        (,) <$> LTAGen.node "a" (LTAGen.oneof [pure 1, LTAGen.leaf 2 "b" (const true)]) <*> LTAGen.leaf 3 "a" (const true)
            checked <- LTAGen.validOutcomes latticeEntailment mixed
            checked `shouldBe` Right [(1, 3)]
            compiled <- LTAGen.compileWith latticeEntailment mixed
            (compiled >>= LTAGen.cardinality) `shouldBe` Left LTAGen.ChildNotOneTerm

        it "refuses a guard that reads a position after a source without symbols" $
            -- The source gives its constructor no term, so the term of "p" has
            -- one child, and the guard reads the elements at the absent position 1.
            forM_ [LTAGen.fromIndexed (LTAGen.Indexed 3 (\(Rank rank) -> rank)), LTAGen.freeze 0 3 (pure 7)] $ \source -> do
                let generator :: LTAGen.LTAGen (Integer, Integer)
                    generator = LTAGen.guarded "p" (\_ y -> y .> 0) $ (,) <$> source <*> LTAGen.elements [1, 2]
                checked <- LTAGen.validOutcomes latticeEntailment generator
                checked `shouldBe` Right []
                compiled <- LTAGen.compileWith latticeEntailment generator
                (compiled >>= LTAGen.cardinality) `shouldBe` Left LTAGen.ChildNotOneTerm

        it "compiles a guard over, and a choice with, a large source without listing it" $ do
            -- The source knows that its members give no root without listing them.
            let large = LTAGen.fromIndexed (LTAGen.Indexed (2 ^ (40 :: Int)) (\(Rank rank) -> rank)) :: LTAGen.LTAGen Integer
                guarded = LTAGen.refinedNode "w" (.>= 1) noConstraint large `LTAGen.satisfying` (.>= 1)
                chosen = LTAGen.oneof [large, LTAGen.elements [1] `LTAGen.satisfying` (.>= 1)]
            forM_ [(guarded, 2 ^ (40 :: Int)), (chosen, 2 ^ (40 :: Int) + 1)] $ \(generator, expected) -> do
                compiled <- timeout 10000000 $ LTAGen.compileWith latticeEntailment generator >>= evaluate . (>>= LTAGen.cardinality)
                compiled `shouldBe` Just (Right expected)

        it "recognizes a constant-false factor without evaluating either huge product" $ do
            let solver = Entailment $ \_ _ -> error "a constant-empty product queried the solver"
                dead = LTAGen.refinedNode "dead" (const true) Bottom (pure ())
                pair left right =
                    void (LTAGen.node "pair" ((,) <$> left <*> right))
            forM_ [pair dead unavailableProduct, pair unavailableProduct dead] $ \generator -> do
                result <- LTAGen.compileWith solver generator
                (result >>= LTAGen.cardinality) `shouldBe` Left LTAGen.EmptyGenerator

        it "skips a huge right factor after semantic rejection on the left" $
            withZ3 declarations $ \solver -> do
                let dead =
                        LTAGen.refinedNode "dead" (const true) (`requires` nonZero) $
                            LTAGen.leaf () "zero" (exact 0)
                    generator = LTAGen.node "pair" ((,) <$> dead <*> unavailableProduct)
                result <- LTAGen.compileWith solver generator
                (result >>= LTAGen.cardinality) `shouldBe` Left LTAGen.EmptyGenerator

        it "compiles leaf equality from the observed roots" $
            withZ3 declarations $ \solver -> do
                let equal = LTAGen.refinedNode "pair" (const true) isSameTermAs $ bitForest 2
                compiled <- compileOrFail solver equal
                expected <- LTAGen.validOutcomes solver equal
                Right (values compiled) `shouldBe` expected
                values compiled `shouldBe` [[0, 0], [1, 1]]

        it "compiles a large supported product without materialization" $
            withZ3 declarations $ \solver -> do
                let generator = LTAGen.node "bits" $ bitForest 64
                    total = 2 ^ (64 :: Int)
                compiled <- LTAGen.compileWith solver generator >>= rightOrFail
                LTAGen.cardinality compiled `shouldBe` Right (Cardinality total)
                LTAGen.unrank compiled 0 `shouldBe` Right (replicate 64 0)
                LTAGen.unrank compiled (Rank $ total - 1) `shouldBe` Right (replicate 64 1)

        it "finishes shrinking a compact two-member language with 64 binary sources" $
            withZ3 declarations $ \solver -> do
                compiled <- LTAGen.compileWith solver (homogeneousBits 64) >>= rightOrFail
                LTAGen.cardinality compiled `shouldBe` Right 2
                values compiled `shouldBe` [replicate 64 0, replicate 64 1]
                completed <- timeout 60000000 $ pure $! all (< 1) (LTAGen.shrinkRank compiled 1) && null (LTAGen.shrinkRank compiled 0)
                completed `shouldBe` Just True

        it "computes a root refinement from the children's roots" $
            withZ3 declarations $ \solver -> do
                compiled <- LTAGen.compileWith solver (homogeneousBits 3) >>= rightOrFail
                values compiled `shouldBe` [replicate 3 0, replicate 3 1]
                decided <- LTAGen.compileWith (Entailment $ \_ _ -> pure Yes) (homogeneousBits 2)
                (decided >>= LTAGen.cardinality) `shouldBe` Right 4

        it "report an undecided guard beside an equality as SolverUnknown" $ do
            -- The two leaves are equal, so the observations decide Same. The
            -- condition is unbounded, so the lattice cannot decide it.
            let g =
                    LTAGen.refinedNode "p" (const true) (\x y -> allOf [isSameTermAs x y, requires x (.>= 0)]) $
                        (,) <$> LTAGen.leaf () "a" (const true) <*> LTAGen.leaf () "a" (const true)
            compiled <- LTAGen.compileWith latticeEntailment g
            checked <- LTAGen.validOutcomes latticeEntailment g
            (either Just (const Nothing) compiled, either Just (const Nothing) checked)
                `shouldBe` (Just LTAGen.SolverUnknown, Just LTAGen.SolverUnknown)

        it "report an undecided guard with an equality under a disjunction as SolverUnknown" $ do
            -- The leaves differ, so the observations decide Same; the condition
            -- is unbounded, so the lattice cannot decide it.
            let g =
                    LTAGen.refinedNode "p" (const true) (\x y -> anyOf [isSameTermAs x y, requires x (.> 5)]) $
                        (,) <$> LTAGen.leaf () "a" (const true) <*> LTAGen.leaf () "b" (const true)
            compiled <- LTAGen.compileWith latticeEntailment g
            checked <- LTAGen.validOutcomes latticeEntailment g
            (either Just (const Nothing) compiled, either Just (const Nothing) checked)
                `shouldBe` (Just LTAGen.SolverUnknown, Just LTAGen.SolverUnknown)

        it "compile uniformly over a deferred constructor, weighted by the members" $ do
            -- The guard defers the first alternative, so the weights of uniformly wait for compile.
            let positive = LTAGen.guarded "p" (\x -> x .>= 1) ((: []) <$> LTAGen.elements [0, 1, 2 :: Integer])
            compiled <- compileOrFail latticeEntailment $ LTAGen.uniformly [positive, (: []) <$> LTAGen.elements [5]]
            sort (values compiled) `shouldBe` [[1], [2], [5]]
            map snd (massesByRank compiled) `shouldBe` replicate 3 (1 % 3)

        it "read the root of a product with one term inside a choice" $ do
            -- The product gives its constructor the one term of its first part.
            let g =
                    LTAGen.guarded
                        "g"
                        (\x -> x .> 0)
                        (LTAGen.oneof [LTAGen.elements [1 :: Integer], LTAGen.elements [2] <* pure ()])
            compiled <- compileOrFail latticeEntailment g
            checked <- LTAGen.validOutcomes latticeEntailment g
            (sort (values compiled), fmap sort checked) `shouldBe` ([1, 2], Right [1, 2])

        it "rank the parts of a compiled import independently of interning order" $ do
            -- Intern the later alternative first, as the import-order tests of
            -- GenSpec do.
            let first' = Transition "interned-a" (refinementFormula (.== 0)) [] noConstraint
                second' = Transition "interned-b" (refinementFormula (.== 1)) [] noConstraint
            _ <- evaluate $ nodeCount $ Node [second']
            compiled <-
                LTAGen.compileWith
                    latticeEntailment
                    (LTAGen.fromAutomatonUpToDepth 0 (Node [first', second']) `LTAGen.satisfying` (.>= 0))
            fmap (map Tree.rootLabel) (compiled >>= LTAGen.values)
                `shouldBe` Right [RefinedSymbol "interned-a" (refinementFormula (.== 0)), RefinedSymbol "interned-b" (refinementFormula (.== 1))]

        it "give an empty language for an import that its condition empties" $ do
            -- The pruned automaton is empty, and reading it used to throw.
            let zero = Node [Transition "n" (refinementFormula (.== 0)) [] noConstraint]
                emptied = LTAGen.fromAutomatonUpToDepth 1 zero `LTAGen.satisfying` (.>= 1)
            compiled <- LTAGen.compileWith latticeEntailment emptied
            checked <- LTAGen.validOutcomes latticeEntailment emptied
            (LTAGen.cardinality <$> compiled, checked) `shouldBe` (Right (Left LTAGen.EmptyGenerator), Right [])

        it "compile a choice of a recursive import and a deferred node" $ do
            -- The deferred node makes compile read the choice, and the import gives a recursive group.
            let lists =
                    Mu $ \list ->
                        Node
                            [ Transition "nil" (refinementFormula (.== 0)) [] noConstraint
                            , Transition "cons" (refinementFormula (.>= 1)) [list] noConstraint
                            ]
                dead = LTAGen.refinedNode "dead" (const true) Bottom (pure (Tree.Node "x" []))
            compiled <- compileOrFail latticeEntailment $ LTAGen.oneof [LTAGen.fromAutomaton lists, dead]
            map (LTAGen.countAtSize compiled) [1, 2] `shouldBe` [Right 1, Right 1]

    describe "integer leaves" $ do
        it "add no size for a constructor above a closed group of integer leaves" $ do
            -- The guard closes the leaf; the node above it has no point to select.
            let digits = LTAGen.every `LTAGen.satisfying` (\v -> 8 .<= v .&& v .<= 9) :: LTAGen.LTAGen Integer
                closed = (: []) <$> LTAGen.guarded "p" (\x -> x .>= 8) digits
            inner <- compileOrFail latticeEntailment closed
            outer <- compileOrFail latticeEntailment $ LTAGen.node "q" closed
            map (LTAGen.sizeOfRank outer) [0, 1] `shouldBe` map (LTAGen.sizeOfRank inner) [0, 1]

        it "count one source choice for each integer leaf, wherever a constructor closes it" $ do
            -- A node without a result closes its leaf. A result keeps the leaf
            -- open, so the parent closes the two leaves together. Each leaf is
            -- one source choice, as a member of elements is.
            let digit = LTAGen.every `LTAGen.satisfying` (\v -> 8 .<= v .&& v .<= 9) :: LTAGen.LTAGen Integer
                closedAtOnce = LTAGen.node "m"
                keptOpen = LTAGen.refinedNode "m" (const true) noConstraint `LTAGen.ensuring` id
                pair inner leaf = LTAGen.node "n" $ (,) <$> inner leaf <*> inner leaf
                sizes generator = map (LTAGen.sizeOfRank generator) [0 .. 3]
            listed <- compileOrFail latticeEntailment $ pair closedAtOnce $ LTAGen.elements [8, 9]
            atOnce <- compileOrFail latticeEntailment $ pair closedAtOnce digit
            open <- compileOrFail latticeEntailment $ pair keptOpen digit
            sizes atOnce `shouldBe` sizes listed
            sizes open `shouldBe` sizes listed
            LTAGen.pmf (LTAGen.upToSize 2 atOnce) `shouldBe` LTAGen.pmf (LTAGen.upToSize 2 listed)
            LTAGen.pmf (LTAGen.upToSize 2 open) `shouldBe` LTAGen.pmf (LTAGen.upToSize 2 listed)

        it "compile uniformly over integer leaves, weighted by their points" $ do
            let leaves :: Integer -> Integer -> LTAGen.LTAGen Integer
                leaves low high = LTAGen.every `LTAGen.satisfying` (\v -> literal low .<= v .&& v .<= literal high)
            compiled <- compileOrFail latticeEntailment $ LTAGen.uniformly [leaves 0 1, leaves 10 12]
            sort (values compiled) `shouldBe` [0, 1, 10, 11, 12]
            map snd (massesByRank compiled) `shouldBe` replicate 5 (1 % 5)

        it "agree with validOutcomes, weigh their members as pools do, and rank their terms" $
            withZ3 declarations $ \solver ->
                forM_ integerCases $ \(name, integerCase) -> do
                    let symbolic = integerCase $ \low high -> LTAGen.every `LTAGen.satisfying` (\v -> literal low .<= v .&& v .<= literal high)
                        pooled = integerCase $ \low high -> LTAGen.elements [low .. high]
                    compiled <- compileOrFail solver symbolic
                    twin <- compileOrFail solver pooled
                    expected <- LTAGen.validOutcomes solver symbolic
                    (name, fmap sort expected) `shouldBe` (name, Right $ sort $ values compiled)
                    (name, massByValue compiled) `shouldBe` (name, massByValue twin)
                    (name, unranked compiled $ allRanks compiled, unranked twin $ allRanks twin) `shouldBe` (name, [], [])

        it "rank the terms of a language too large to enumerate" $
            withZ3 declarations $ \solver -> do
                let digits :: Integer -> Integer -> LTAGen.LTAGen Integer
                    digits low high = LTAGen.every `LTAGen.satisfying` (\v -> literal low .<= v .&& v .<= literal high)
                    readAt :: Integer -> LTAGen.LTAGen (Integer, Integer)
                    readAt low = LTAGen.guarded "read-at" (\n i -> literal low .<= i .&& i .< n) $ (,) <$> digits 1 1000000 <*> digits (-10) 1000000
                compiled <- compileOrFail solver $ readAt 0
                wider <- compileOrFail solver $ readAt (-10)
                LTAGen.cardinality compiled `shouldBe` Right 500000500000
                unranked compiled [0, 1, 2, 999, 1000, 123456789, 500000499999] `shouldBe` []
                (LTAGen.rankOf compiled =<< LTAGen.termAt wider 0) `shouldBe` Left LTAGen.TermNotInLanguage

        it "compile with the lattice entailment as with Z3" $
            withZ3 declarations $ \solver ->
                forM_ integerCases $ \(name, integerCase) ->
                    forM_
                        [ integerCase $ \low high -> LTAGen.every `LTAGen.satisfying` (\v -> literal low .<= v .&& v .<= literal high)
                        , integerCase $ \low high -> LTAGen.elements [low .. high]
                        ]
                        $ \generator -> do
                            byZ3 <- compileOrFail solver generator
                            counted <- LTAGen.compileWith latticeEntailment generator
                            (name, values <$> counted, massByValue <$> counted)
                                `shouldBe` (name, Right $ values byZ3, Right $ massByValue byZ3)

        it "keep source order in a bare applicative spine" $
            withZ3 declarations $ \solver -> do
                let spine leaf = (,) <$> LTAGen.oneof [leaf, LTAGen.elements [0 :: Integer]] <*> LTAGen.elements "x"
                compiled <- compileOrFail solver $ spine $ LTAGen.every `LTAGen.satisfying` (\v -> 5 .<= v .&& v .<= 6)
                values compiled `shouldBe` [(5, 'x'), (6, 'x'), (0, 'x')]

        it "report a guard below a closed leaf and a root function over one" $
            withZ3 declarations $ \solver -> do
                let digits = LTAGen.every `LTAGen.satisfying` (\v -> 0 .<= v .&& v .<= 9) :: LTAGen.LTAGen Integer
                    below = LTAGen.refinedNode "p" (const true) (\n -> descendant n [0] `requires` (.>= 5)) (LTAGen.node "n" digits)
                    byRoots = LTAGen.refinedNodeByRoots "r" (const $ const true) unconstrained digits
                belowRead <- LTAGen.compileWith solver below
                roots <- LTAGen.compileWith solver byRoots
                either isIntegerLeafRead (const False) belowRead `shouldBe` True
                either isIntegerLeafRead (const False) roots `shouldBe` True

        it "apply to the root of an import with a recursive root only" $
            withZ3 declarations $ \solver -> do
                let lists =
                        Mu $ \list ->
                            Node
                                [ Transition "nil" (refinementFormula (.== 0)) [] noConstraint
                                , Transition "cons" (refinementFormula (.>= 1)) [list] noConstraint
                                ]
                compiled <- compileOrFail solver $ LTAGen.fromAutomaton lists `LTAGen.satisfying` (.>= 1)
                let symbols = foldMap (\(RefinedSymbol symbol _) -> [symbol])
                map symbols <$> traverse (LTAGen.unrank compiled) [0 .. 2]
                    `shouldBe` Right [["cons", "nil"], ["cons", "cons", "nil"], ["cons", "cons", "cons", "nil"]]

        it "give a result through a mapped constructor, and no other generator" $
            withZ3 declarations $ \solver -> do
                let three = LTAGen.elements [3 :: Integer]
                    mapped = (fmap (* 2) . LTAGen.guarded "m" (const true)) `LTAGen.ensuring` id $ three
                compiled <- compileOrFail solver $ mapped `LTAGen.satisfying` (.== 3)
                values compiled `shouldBe` [6]
                LTAGen.cardinality
                    (LTAGen.refinedNodeByRoots "r" (const $ const true) unconstrained `LTAGen.ensuring` id $ three)
                    `shouldBe` Left LTAGen.ResultNeedsConstructor
  where
    isIntegerLeafRead err = case err of
        LTAGen.IntegerLeafRead _ -> True
        _ -> False

{- | Small generators over integer leaves, given a leaf of the integers between
two bounds. Each one is compiled with 'LTAGen.every' and with 'LTAGen.elements'.
-}
integerCases :: [(String, (Integer -> Integer -> LTAGen.LTAGen Integer) -> LTAGen.LTAGen [Integer])]
integerCases =
    [ ("contract", \leaf -> LTAGen.guarded "lt" (\x y -> x .< y) $ (\x y -> [x, y]) <$> leaf 0 4 <*> leaf 0 4)
    ,
        ( "choice under a parent"
        , \leaf -> LTAGen.guarded "p" (\x -> x .>= 8) $ pure <$> LTAGen.oneof [leaf 0 9, LTAGen.elements [100]]
        )
    , ("weighted choice", \leaf -> pure <$> LTAGen.frequency [(3, leaf 0 3), (1, LTAGen.elements [100])])
    ,
        ( "result under a condition"
        , \leaf -> LTAGen.guarded "sum" (\_ _ -> true) `LTAGen.ensuring` (+) $ (\a b -> [a, b]) <$> leaf 0 3 <*> leaf 0 3
        )
    ,
        ( "sorted lists"
        , \leaf -> LTAGen.recurUpTo 2 $ \rest -> LTAGen.oneof [LTAGen.leaf [] "nil" (.== 4), sortedCons (leaf 0 3) rest]
        )
    ]
  where
    sortedCons element rest = LTAGen.guarded "cons" (\x t -> x .<= t) `LTAGen.ensuring` const $ (:) <$> element <*> rest

{- | The ranks whose term does not give the rank back, or whose term with one
user symbol replaced by a symbol outside the language has a rank.
-}
unranked :: LTAGen.LTAGen a -> [Rank] -> [Rank]
unranked generator ranks =
    [ rank
    | rank <- ranks
    , let term = LTAGen.termAt generator rank
    , either (const True) (notElem rank) (LTAGen.ranksOf generator =<< term)
        || (LTAGen.termAt generator =<< LTAGen.rankOf generator =<< term) /= term
        || any ((/= Left LTAGen.TermNotInLanguage) . LTAGen.rankOf generator) (either (const []) relabellings term)
    ]
  where
    outside = LTAGen.Label $ RefinedSymbol (fromString "outside") true
    relabellings term =
        [ snd $ mapAccumL (\index label -> (index + 1, if index == position then outside else label)) (0 :: Int) term
        | (position, LTAGen.Label _) <- zip [0 ..] $ Tree.flatten term
        ]

-- | Every rank of a finite language.
allRanks :: LTAGen.LTAGen a -> [Rank]
allRanks generator = either (const []) everyRank $ LTAGen.cardinality generator

-- | The exact sampling mass of each value of a small compiled language.
massByValue :: (Ord a) => LTAGen.LTAGen a -> Map.Map a Rational
massByValue generator =
    Map.fromListWith
        (+)
        [(value, mass) | (rank, mass) <- massesByRank generator, Right value <- [LTAGen.unrank generator rank]]

-- | Build a product whose candidate count exceeds machine integers at width 64.
bitForest :: Int -> LTAGen.LTAGen [Int]
bitForest width =
    foldr (\_ rest -> (:) <$> bits <*> rest) (pure []) [1 .. width]
  where
    bits =
        LTAGen.namedPool
            [ LTAGen.Refined 0 "zero" $ exact 0
            , LTAGen.Refined 1 "one" $ exact 1
            ]

-- | A large fallback whose values must remain unobserved.
unavailableProduct :: LTAGen.LTAGen [Int]
unavailableProduct =
    LTAGen.node "computed" $ error "an empty product evaluated a generated value" <$ bitForest 64

-- | Retain homogeneous vectors of positive width with small local relations.
homogeneousBits :: Int -> LTAGen.LTAGen [Int]
homogeneousBits width = foldr (\_ rest -> prepend rest) ((: []) <$> bit) [2 .. width]
  where
    bit = LTAGen.namedPool [LTAGen.Refined (0 :: Int) "zero" nonNegative, LTAGen.Refined 1 "one" $ exact 1]
    prepend rest =
        LTAGen.refinedNodeByRoots "cons" (const . firstRefinement) equivalent $
            (:) <$> bit <*> rest
    firstRefinement (RefinedSymbol _ refinement : _) = refinement
    firstRefinement [] = error "a homogeneous vector node has no children"
    equivalent left right = allOf [left `isSubtypeOf` right, right `isSubtypeOf` left]

-- | Liquid Fixpoint declarations needed by the exact integer refinements.
declarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
declarations = [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)]
