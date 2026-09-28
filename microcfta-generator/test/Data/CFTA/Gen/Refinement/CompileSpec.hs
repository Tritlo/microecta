module Data.CFTA.Gen.Refinement.CompileSpec (spec) where

import Control.Monad (forM_, void)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Ratio ((%))
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, it, shouldBe)

import Data.CFTA.Gen.Refinement.ExampleSupport (nonNegative)
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Gen.Refinement.TestSupport (compileOrFail, massesByRank, rightOrFail, values)
import Data.CFTA.Refinement (
    Entailment (Entailment),
    Guard (Bottom),
    Node (Mu, Node),
    Symbol (RefinedSymbol),
    Verdict (Yes),
    noConstraint,
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
    (.>=),
 )
import Data.CFTA.Refinement.Guard (allOf, descendant, isSameTermAs, isSubtypeOf, requires, unconstrained)
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
                LTAGen.cardinality compiled `shouldBe` Right total
                LTAGen.unrank compiled 0 `shouldBe` Right (replicate 64 0)
                LTAGen.unrank compiled (total - 1) `shouldBe` Right (replicate 64 1)

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

        it "give an empty language for an import that its condition empties" $ do
            -- The pruned automaton is empty, and reading it used to throw.
            let zero = Node [Transition "n" (refinementFormula (.== 0)) [] noConstraint]
                emptied = LTAGen.fromAutomatonUpToDepth 1 zero `LTAGen.satisfying` (.>= 1)
            compiled <- LTAGen.compileWith latticeEntailment emptied
            checked <- LTAGen.validOutcomes latticeEntailment emptied
            (LTAGen.cardinality <$> compiled, checked) `shouldBe` (Right (Left LTAGen.EmptyGenerator), Right [])

    describe "integer leaves" $ do
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

-- | The ranks whose term does not give the rank back.
unranked :: LTAGen.LTAGen a -> [Integer] -> [Integer]
unranked generator ranks =
    [ rank
    | rank <- ranks
    , let term = LTAGen.termAt generator rank
    , either (const True) (notElem rank) (LTAGen.ranksOf generator =<< term)
        || (LTAGen.termAt generator =<< LTAGen.rankOf generator =<< term) /= term
    ]

-- | Every rank of a finite language.
allRanks :: LTAGen.LTAGen a -> [Integer]
allRanks generator = either (const []) (\count -> [0 .. count - 1]) $ LTAGen.cardinality generator

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
