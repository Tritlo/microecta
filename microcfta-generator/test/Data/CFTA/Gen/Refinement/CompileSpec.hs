module Data.CFTA.Gen.Refinement.CompileSpec (spec) where

import Control.Exception (evaluate)
import Control.Monad (forM_, void)
import Data.List (sort)
import Data.Ratio ((%))
import qualified Data.Tree as Tree
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Gen.Refinement.ExampleSupport (nonNegative)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Gen.Refinement.TestSupport (compileOrFail, massesByRank, rightOrFail, values)
import Data.CFTA.Index (Cardinality (..), Rank (..))
import Data.CFTA.Refinement (
    Entailment (Entailment),
    Guard (Bottom),
    Node (Mu, Node),
    Symbol (RefinedSymbol),
    Verdict (Yes),
    noConstraint,
    nodeCount,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (Refinement, refinementFormula, true, (./=), (.==), (.>), (.>=))
import Data.CFTA.Refinement.Guard (allOf, anyOf, isSameTermAs, isSubtypeOf, notGuard, requires)
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
spec =
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
            (LTAGen.cardinality <$> compiled, checked) `shouldBe` (Right (Left LTAGen.EmptyGenerator), Left LTAGen.EmptyGenerator)

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
