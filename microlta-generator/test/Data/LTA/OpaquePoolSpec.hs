module Data.LTA.OpaquePoolSpec (spec) where

import Control.Exception (evaluate)
import Control.Monad (forM_, void)
import qualified Data.Map.Strict as Map
import Data.Ratio ((%))
import Data.String (fromString)
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import Data.LTA (Entailment (Entailment), Guard (Bottom), LiquidConstraint, Refinement, Verdict (Unknown, Yes))
import Data.LTA.ExampleSupport (nonNegative)
import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.Guard (Position, allOf, isSameTermAs, isSubtypeOf, requires, unconstrained)
import Data.LTA.LiquidFixpoint (withZ3)
import Data.LTA.Refinement (value, (./=.), (.<.), (.==.), (.>=.))
import Data.LTA.TestSupport (compileOrFail, rightOrFail)
import qualified Data.Tree.Gen as Tree
import Data.Tree.Gen.Internal.Sampler (Exact (..))
import qualified Language.Fixpoint.Types as Fixpoint

-- | A deliberately partial operation over one fixed-size memory page.
newtype PageRead = PageRead {readOffset :: Int}
    deriving (Eq, Show)

-- | Valid byte offsets for the example page.
validOffset :: Refinement
validOffset = Fixpoint.pAnd [value .>=. (0 :: Int), value .<. pageSize]

-- | Exact refinement attached to one sampled integer.
exactOffset :: Int -> Refinement
exactOffset offset = value .==. offset

-- | Interpret the requirements understood by this native integer source.
offsetSatisfies :: Refinement -> Int -> Bool
offsetSatisfies requirement offset
    | requirement == validOffset = offset >= 0 && offset < pageSize
    | otherwise = False

-- | A broad native generator conditioned only when its LTA context asks.
offsetSource :: LTA.OpaqueSource Int
offsetSource =
    LTA.opaqueSource
        ( \requirements ->
            QC.chooseInt (-128, 127)
                `QC.suchThat` \offset -> all (`offsetSatisfies` offset) requirements
        )
        (fromString . ("offset-" <>) . show)
        exactOffset

-- | The guard is the single source of the range requirement.
sampledReads :: QC.Gen (LTA.LTAGen PageRead)
sampledReads =
    LTA.sampledNode "read-at" (\offset -> offset `requires` validOffset) $
        PageRead <$> LTA.opaquePool poolSize offsetSource

-- | The same language through an ordinary pool, as the rejection control.
unconstrainedReads :: LTA.LTAGen PageRead
unconstrainedReads =
    LTA.node "read-at" (\offset -> offset `requires` validOffset) $
        PageRead <$> LTA.freeze seed poolSize rawOffset
  where
    rawOffset = do
        offset <- QC.chooseInt (-128, 127)
        pure $ LTA.refined offset (fromString $ "offset-" <> show offset) $ exactOffset offset

-- | Read the selected byte. An invalid generated offset raises an exception.
runRead :: PageRead -> Int
runRead PageRead{readOffset} = page !! readOffset

-- | Concrete memory page used by the partial read.
page :: [Int]
page = [1000 .. 1000 + pageSize - 1]

-- | Fixed page extent used by both the concrete value and liquid requirement.
pageSize :: Int
pageSize = 32

-- | Number of values retained for the unary page-read pool.
poolSize :: Int
poolSize = 32

-- | Deterministic seed shared by the pushdown and freeze-first controls.
seed :: Int
seed = 20260902

-- | A partial operation with two independently sampled argument pools.
data Division = Division
    { dividend :: Int
    , divisor :: Int
    }
    deriving (Eq, Show)

-- | Refinement used as the second argument's division precondition.
nonZero :: Refinement
nonZero = value ./=. (0 :: Int)

-- | A source that makes wrong requirement routing visible in the final count.
zeroSource :: LTA.OpaqueSource Int
zeroSource =
    LTA.opaqueSource
        (const $ pure 0)
        (const "zero")
        exactOffset

-- | Produce zero without a constraint, and one when non-zero is required.
divisorSource :: LTA.OpaqueSource Int
divisorSource =
    LTA.opaqueSource
        (\requirements -> pure $ if nonZero `elem` requirements then 1 else 0)
        (fromString . ("divisor-" <>) . show)
        exactOffset

-- | Constrain only the second constructor argument.
divisionGuard :: Position -> Position -> LiquidConstraint
divisionGuard _ denominator = denominator `requires` nonZero

-- | Sample two independent pools under one positional guard.
sampledDivisions :: QC.Gen (LTA.LTAGen Division)
sampledDivisions =
    LTA.sampledNode "divide" divisionGuard $
        Division
            <$> LTA.opaquePool divisionPoolSize zeroSource
            <*> LTA.opaquePool divisionPoolSize divisorSource

-- | Number of ranks contributed by each division argument.
divisionPoolSize :: Int
divisionPoolSize = 8

-- | Execute the deliberately partial division operation.
runDivision :: Division -> Int
runDivision Division{dividend, divisor} = dividend `div` divisor

spec :: Spec
spec = do
    describe "refinement-aware opaque pools" $ do
        it "pushes a direct liquid requirement into an opaque suchThat source" $
            withZ3 declarations $ \solver -> do
                pushed <- compileOrFail solver $ unGen sampledReads (mkQCGen seed) 30
                baseline <- compileOrFail solver unconstrainedReads
                LTA.cardinality pushed `shouldBe` fromIntegral poolSize
                LTA.cardinality baseline `shouldSatisfy` (< fromIntegral poolSize)

        it "makes the partial page read total for every retained rank" $
            withZ3 declarations $ \solver -> do
                compiled <- compileOrFail solver $ unGen sampledReads (mkQCGen seed) 30
                let selectedReads =
                        [ generated
                        | rank <- [0 .. LTA.cardinality compiled - 1]
                        , Right generated <- [LTA.generatedValue <$> LTA.unrank compiled rank]
                        ]
                length selectedReads `shouldBe` poolSize
                map runRead selectedReads `shouldSatisfy` all (`elem` page)

        it "routes a requirement to the correct one of several opaque pools" $
            withZ3 declarations $ \solver -> do
                compiled <- compileOrFail solver $ unGen sampledDivisions (mkQCGen seed) 30
                let divisions =
                        [ generated
                        | rank <- [0 .. LTA.cardinality compiled - 1]
                        , Right generated <- [LTA.generatedValue <$> LTA.unrank compiled rank]
                        ]
                length divisions `shouldBe` divisionPoolSize * divisionPoolSize
                map runDivision divisions `shouldBe` replicate (length divisions) 0

    describe "automatic compilation" $ do
        it "preserves source order when observation keys have another order" $
            withZ3 declarations $ \solver -> do
                let atoms :: LTA.LTAGen Int
                    atoms =
                        LTA.pool
                            [ LTA.refined 2 "z" $ exactOffset 2
                            , LTA.refined 0 "a" $ exactOffset 0
                            , LTA.refined 1 "m" $ exactOffset 1
                            ]
                    generator =
                        LTA.node
                            "pair"
                            (\left right -> allOf [left `requires` nonNegative, right `requires` nonNegative])
                            $ (,) <$> LTA.children atoms <*> LTA.children atoms
                compiled <- compileOrFail solver generator
                expected <- LTA.validOutcomes solver generator
                selectedMembers compiled `shouldBe` expected
                fmap (map LTA.generatedValue) (selectedMembers compiled)
                    `shouldBe` Right [(left, right) | left <- [2, 0, 1], right <- [2, 0, 1]]

        it "retains repeated source ranks after mapping their values" $
            withZ3 declarations $ \solver -> do
                let generator =
                        void
                            ( LTA.pool
                                [ LTA.refined (1 :: Int) "z" $ exactOffset 1
                                , LTA.refined 1 "z" $ exactOffset 1
                                , LTA.refined 0 "a" $ exactOffset 0
                                ]
                            )
                compiled <- compileOrFail solver generator
                expected <- LTA.validOutcomes solver generator
                LTA.cardinality compiled `shouldBe` 3
                selectedMembers compiled `shouldBe` expected
                LTA.unrank compiled 0 `shouldBe` LTA.unrank compiled 1

        it "samples exact source weights across unequal and rejected branches" $
            withZ3 declarations $ \solver -> do
                atoms <-
                    rightOrFail $
                        LTA.frequency
                            [
                                ( 3
                                , LTA.pool
                                    [ LTA.refined (2 :: Int) "z" $ exactOffset 2
                                    , LTA.refined 0 "m" $ exactOffset 0
                                    ]
                                )
                            , (1, LTA.pool [LTA.refined 1 "a" $ exactOffset 1])
                            , (7, LTA.pool [LTA.refined 0 "trailing" $ exactOffset 0])
                            ]
                let generator =
                        LTA.node
                            "pair"
                            (\left right -> allOf [left `requires` nonZero, right `requires` nonZero])
                            $ (,) <$> LTA.children atoms <*> LTA.children atoms
                compiled <- compileOrFail solver generator
                expected <- LTA.validOutcomes solver generator
                selectedMembers compiled `shouldBe` expected
                fmap (map LTA.generatedValue) (selectedMembers compiled)
                    `shouldBe` Right [(2, 2), (2, 1), (1, 2), (1, 1)]
                fmap (map LTA.generatedWeight) (selectedMembers compiled)
                    `shouldBe` Right [9, 3, 3, 1]
                let samples = runExact $ Tree.lowerWithRank $ LTA.compiledRanked compiled
                    probabilities = Map.fromListWith (+) [(rank, mass) | (mass, (rank, _)) <- samples]
                Map.toAscList probabilities `shouldBe` zip [0 .. 3] [9 % 16, 3 % 16, 3 % 16, 1 % 16]
                forM_ samples $ \(_, (rank, generated)) ->
                    LTA.unrank compiled rank `shouldBe` Right generated
                runExact (Tree.lower $ LTA.compiledRanked compiled)
                    `shouldBe` [(mass, generated) | (mass, (_, generated)) <- samples]

        it "reconnects semantic shrinks through rejected source ranks" $
            withZ3 declarations $ \solver -> do
                let atoms :: LTA.LTAGen Int
                    atoms =
                        LTA.pool
                            [ LTA.refined 0 "non-negative" nonNegative
                            , LTA.refined 1 "one" $ exactOffset 1
                            ]
                    generator =
                        LTA.node "pair" isSubtypeOf $
                            (,) <$> LTA.children atoms <*> LTA.children atoms
                compiled <- compileOrFail solver generator
                fmap (map LTA.generatedValue) (selectedMembers compiled)
                    `shouldBe` Right [(0, 0), (1, 0), (1, 1)]
                LTA.shrinkRank compiled 2 `shouldBe` [1, 0]
                LTA.shrinkRank compiled 1 `shouldBe` [0]
                LTA.shrinkRank compiled 0 `shouldBe` []

        it "keeps accepted pools when optional shrink implications are unknown" $ do
            let solver = Entailment $ \_ _ -> pure Unknown
                generator = LTA.pool [LTA.refined (0 :: Int) "zero" $ exactOffset 0, LTA.refined 1 "one" $ exactOffset 1]
            compiled <- compileOrFail solver generator
            LTA.cardinality compiled `shouldBe` 2
            map (LTA.shrinkRank compiled) [0, 1] `shouldBe` [[], []]

        it "uses an unknown reverse implication only toward an earlier rank" $ do
            let precise = exactOffset 1
                solver = Entailment $ \source target ->
                    pure $ if source == precise && target == nonNegative then Yes else Unknown
                broadEntry = LTA.refined (0 :: Int) "non-negative" nonNegative
                preciseEntry = LTA.refined 1 "one" precise
            forM_ [([broadEntry, preciseEntry], [[], [0]]), ([preciseEntry, broadEntry], [[], []])] $ \(entries, expected) -> do
                compiled <- compileOrFail solver $ LTA.pool entries
                LTA.cardinality compiled `shouldBe` 2
                map (LTA.shrinkRank compiled) [0, 1] `shouldBe` expected

        it "finishes shrinking a compact two-member language with 64 binary sources" $
            withZ3 declarations $ \solver -> do
                compiled <-
                    LTA.compile solver (homogeneousBits 64)
                        >>= rightOrFail
                LTA.cardinality compiled `shouldBe` 2
                fmap (map LTA.generatedValue) (selectedMembers compiled)
                    `shouldBe` Right [replicate 64 0, replicate 64 1]
                completed <-
                    timeout 60000000
                        $ evaluate
                        $ LTA.shrinkRank compiled 1 == [0] && null (LTA.shrinkRank compiled 0)
                completed `shouldBe` Just True

        it "recognizes a constant-false factor without evaluating either huge product" $ do
            let solver = Entailment $ \_ _ -> error "a constant-empty product queried the solver"
                dead = LTA.node "dead" Bottom (pure () :: LTA.Children ())
                pair left right =
                    void (LTA.node "pair" unconstrained ((,) <$> LTA.children left <*> LTA.children right))
            forM_ [pair dead unavailableProduct, pair unavailableProduct dead] $ \generator -> do
                result <- LTA.compile solver generator
                fmap LTA.cardinality result `shouldBe` Left LTA.EmptyGenerator

        it "skips a huge computed right factor after semantic rejection on the left" $
            withZ3 declarations $ \solver -> do
                let dead =
                        LTA.node "dead" (\argument -> argument `requires` nonZero) $
                            LTA.leaf () "zero" (exactOffset 0)
                    generator = LTA.node "pair" unconstrained ((,) <$> LTA.children dead <*> LTA.children unavailableProduct)
                result <- LTA.compile solver generator
                fmap LTA.cardinality result `shouldBe` Left LTA.EmptyGenerator

        it "compiles leaf equality and rejects value-computed refinements" $
            withZ3 declarations $ \solver -> do
                let computed = LTA.refinedNodeBy "sum" (exactOffset . sum) unconstrained $ bitForest 2
                    equal = LTA.node "pair" isSameTermAs $ bitForest 2
                rejected <- LTA.compile solver computed
                fmap LTA.cardinality rejected `shouldBe` Left (LTA.RelationalComputedRefinement "sum")
                computedDiagnostic <- LTA.validOutcomes solver computed
                fmap length computedDiagnostic `shouldBe` Right 4
                compiledEqual <- compileOrFail solver equal
                expected <- LTA.validOutcomes solver equal
                selectedMembers compiledEqual `shouldBe` expected
                fmap (map LTA.generatedValue) (selectedMembers compiledEqual)
                    `shouldBe` Right [[0, 0], [1, 1]]

        it "rejects opaque refinement functions before evaluating their source" $
            withZ3 declarations $ \solver -> do
                let generator =
                        LTA.refinedNodeBy
                            "computed"
                            (\_ -> error "symbolic compilation must not decode candidates")
                            unconstrained
                            $ bitForest 64
                result <- LTA.compile solver generator
                case result of
                    Left err ->
                        err `shouldBe` LTA.RelationalComputedRefinement "computed"
                    Right _ -> expectationFailure "an oversized computed refinement was materialized"

        it "compiles a large supported product without materialization" $
            withZ3 declarations $ \solver -> do
                let generator = LTA.node "bits" unconstrained $ bitForest 64
                    total = 2 ^ (64 :: Int)
                compiled <- LTA.compile solver generator >>= rightOrFail
                LTA.cardinality compiled `shouldBe` total
                fmap LTA.generatedValue (LTA.unrank compiled 0) `shouldBe` Right (replicate 64 0)
                fmap LTA.generatedValue (LTA.unrank compiled (total - 1)) `shouldBe` Right (replicate 64 1)

-- | Build a product whose candidate count exceeds machine integers at width 64.
bitForest :: Int -> LTA.Children [Int]
bitForest width =
    foldr (\_ rest -> (:) <$> LTA.children bits <*> rest) (pure []) [1 .. width]
  where
    bits =
        LTA.pool
            [ LTA.refined 0 "zero" $ exactOffset 0
            , LTA.refined 1 "one" $ exactOffset 1
            ]

-- | A large fallback whose values and refinements must remain unobserved.
unavailableProduct :: LTA.LTAGen [Int]
unavailableProduct =
    LTA.refinedNodeBy
        "computed"
        (\_ -> error "an empty product evaluated a computed refinement")
        unconstrained
        $ const (error "an empty product evaluated a generated value") <$> bitForest 64

-- | Retain homogeneous vectors of positive width with small local relations.
homogeneousBits :: Int -> LTA.LTAGen [Int]
homogeneousBits width = foldr (\_ rest -> prepend rest) ((: []) <$> bit) [2 .. width]
  where
    bit = LTA.pool [LTA.refined (0 :: Int) "zero" nonNegative, LTA.refined 1 "one" $ exactOffset 1]
    prepend rest =
        LTA.refinedNodeByRoots "cons" firstRefinement equivalent $
            (:) <$> LTA.children bit <*> LTA.children rest
    firstRefinement (first : _) = LTA.observedRefinement first
    firstRefinement [] = error "a homogeneous vector node has no children"
    equivalent left right = allOf [left `isSubtypeOf` right, right `isSubtypeOf` left]

-- | Read every accepted rank without dropping decoder errors.
selectedMembers :: LTA.Compiled a -> Either LTA.GeneratorError [LTA.Generated a]
selectedMembers compiled = traverse (LTA.unrank compiled) [0 .. LTA.cardinality compiled - 1]

-- | Liquid Fixpoint declarations needed by the exact integer refinements.
declarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
declarations = [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)]
