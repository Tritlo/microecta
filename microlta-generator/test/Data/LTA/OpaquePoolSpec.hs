module Data.LTA.OpaquePoolSpec (spec) where

import Data.String (fromString)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import Data.LTA (Entailment, Guard, Refinement)
import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.Guard (Position, requires)
import Data.LTA.LiquidFixpoint (withZ3)
import Data.LTA.Refinement ((./=.), (.<.), (.==.), (.>=.))
import qualified Language.Fixpoint.Types as Fixpoint

-- | A deliberately partial operation over one fixed-size memory page.
newtype PageRead = PageRead {readOffset :: Int}
    deriving (Eq, Show)

-- | Liquid's distinguished value variable.
value :: Fixpoint.Expr
value = Fixpoint.EVar $ Fixpoint.symbol ("v" :: String)

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

-- | The old freeze-first route, retained as the rejection control.
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
divisionGuard :: Position -> Position -> Guard
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
spec =
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
                        , Right generated <- [LTA.generatedValue <$> LTA.select rank compiled]
                        ]
                length selectedReads `shouldBe` poolSize
                map runRead selectedReads `shouldSatisfy` all (`elem` page)

        it "routes a requirement to the correct one of several opaque pools" $
            withZ3 declarations $ \solver -> do
                compiled <- compileOrFail solver $ unGen sampledDivisions (mkQCGen seed) 30
                let divisions =
                        [ generated
                        | rank <- [0 .. LTA.cardinality compiled - 1]
                        , Right generated <- [LTA.generatedValue <$> LTA.select rank compiled]
                        ]
                length divisions `shouldBe` divisionPoolSize * divisionPoolSize
                map runDivision divisions `shouldBe` replicate (length divisions) 0

-- | Compile a fixture while preserving a useful Hspec failure.
compileOrFail :: Entailment -> LTA.LTAGen a -> IO (LTA.Compiled a)
compileOrFail solver generator = do
    result <- LTA.compile solver generator
    case result of
        Left err -> expectationFailure (show err) >> fail "unreachable"
        Right compiled -> pure compiled

-- | Liquid Fixpoint declarations needed by the exact integer refinements.
declarations :: [(Fixpoint.Symbol, Fixpoint.Sort)]
declarations = [(Fixpoint.symbol ("v" :: String), Fixpoint.FInt)]
