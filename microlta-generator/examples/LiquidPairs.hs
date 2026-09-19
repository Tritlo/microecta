{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE QualifiedDo #-}

-- | Generate pairs whose left refinement implies the right one, proved by Z3.
module Main (main) where

import Control.Monad (unless)
import qualified Language.Fixpoint.Types as Fixpoint
import qualified Test.QuickCheck as QC

import Data.CFTA.Refinement.Expression ((.==.), (.>=.))
import Data.CFTA.Refinement.Guard (isSubtypeOf)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)
import qualified Data.LTA.Gen.QuickCheck as LTA

main :: IO ()
main =
    withZ3 [(value, Fixpoint.FInt)] $ \solver -> do
        let choices :: LTA.LTAGen Integer
            choices =
                LTA.pool
                    [ LTA.refined 0 "non-negative" (value .>=. (0 :: Integer))
                    , LTA.refined 1 "one" (value .==. (1 :: Integer))
                    ]
            pairs =
                LTA.node
                    "pair"
                    (\actual expected -> actual `isSubtypeOf` expected)
                    $ LTA.do
                        left <- choices
                        right <- choices
                        LTA.pure (left, right)
        compiledResult <- LTA.compile solver pairs
        case compiledResult of
            Left err -> fail (show err)
            Right compiled -> do
                let expected = [(0, 0), (1, 0), (1, 1)]
                    outcomes =
                        [ LTA.generatedValue <$> LTA.unrank compiled rank
                        | rank <- [0 .. LTA.cardinality compiled - 1]
                        ]
                unless (outcomes == map Right expected)
                    $ fail
                    $ "unexpected accepted pairs: " <> show outcomes
                unless (LTA.shrinkRank compiled 2 == [1, 0])
                    $ fail
                    $ "unexpected refinement shrinks: "
                        <> show (LTA.shrinkRank compiled 2)
                mapM_ print outcomes
                result <-
                    QC.quickCheckResult $
                        LTA.forAll compiled (uncurry (>=))
                unless (QC.isSuccess result) $
                    fail "QuickCheck found an invalid liquid pair"
                shrinkResult <-
                    QC.quickCheckResult
                        $ QC.expectFailure
                        $ LTA.forAll compiled (== (0, 0))
                unless (QC.isSuccess shrinkResult) $
                    fail "QuickCheck did not find the refinement counterexample"
  where
    value :: Fixpoint.Symbol
    value = Fixpoint.symbol ("v" :: String)
