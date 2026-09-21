{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE QualifiedDo #-}

-- | Generate pairs whose left refinement implies the right one, proved by Z3.
module Main (main) where

import Control.Monad (unless)
import qualified Language.Fixpoint.Types as Fixpoint
import qualified Test.QuickCheck as QC

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Refinement.Expression ((.==.), (.>=.))
import Data.CFTA.Refinement.Guard (isSubtypeOf)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)

main :: IO ()
main =
    withZ3 [(value, Fixpoint.FInt)] $ \solver -> do
        let choices :: LTAGen.LTAGen Integer
            choices =
                LTAGen.pool
                    [ LTAGen.Refined 0 "non-negative" (value .>=. (0 :: Integer))
                    , LTAGen.Refined 1 "one" (value .==. (1 :: Integer))
                    ]
            pairs =
                LTAGen.node
                    "pair"
                    (\actual expected -> actual `isSubtypeOf` expected)
                    $ LTAGen.do
                        left <- choices
                        right <- choices
                        LTAGen.pure (left, right)
        compiledResult <- LTAGen.compile solver pairs
        case compiledResult of
            Left err -> fail (show err)
            Right compiled -> do
                let expected = [(0, 0), (1, 0), (1, 1)]
                    outcomes = LTAGen.cardinality compiled >>= \total -> traverse (LTAGen.unrank compiled) [0 .. total - 1]
                unless (outcomes == Right expected)
                    $ fail
                    $ "unexpected accepted pairs: " <> show outcomes
                unless (all (< 2) $ LTAGen.shrinkRank compiled 2)
                    $ fail
                    $ "unexpected shrinks: "
                        <> show (LTAGen.shrinkRank compiled 2)
                print outcomes
                result <-
                    QC.quickCheckResult $
                        LTAGen.forAll compiled (uncurry (>=))
                unless (QC.isSuccess result) $
                    fail "QuickCheck found an invalid liquid pair"
                shrinkResult <-
                    QC.quickCheckResult
                        $ QC.expectFailure
                        $ LTAGen.forAll compiled (== (0, 0))
                unless (QC.isSuccess shrinkResult) $
                    fail "QuickCheck did not find the refinement counterexample"
  where
    value :: Fixpoint.Symbol
    value = Fixpoint.symbol ("v" :: String)
