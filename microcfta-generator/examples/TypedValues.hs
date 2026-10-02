{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}

-- | Draw every value of several types without a pool, and relate them with a contract.
module Main (main) where

import Control.Monad (unless)
import Data.Word (Word8)
import qualified Test.QuickCheck as QC

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Refinement.Expression (Enumerated (..), Literal, literal, (./=), (.==), (.>), (.||))

-- | A color, written as its position.
data Color = Red | Green | Blue
    deriving (Bounded, Enum, Eq, Show)
    deriving (Literal) via (Enumerated Color)

{- | A pixel: a color that is not red, a brightness, and a flag. A brightness of
zero needs the flag.
-}
pixels :: LTAGen.LTAGen (Color, Word8, Bool)
pixels = LTAGen.guarded "pixel" (\_ brightness dimmed -> brightness .> 0 .|| dimmed .== literal True) $ LTAGen.do
    color <- LTAGen.every `LTAGen.satisfying` (./= literal Red)
    brightness <- LTAGen.every
    dimmed <- LTAGen.every
    LTAGen.pure (color, brightness, dimmed)

-- | Check the count, the rank order, and the sampled pixels.
main :: IO ()
main = do
    compiled <- LTAGen.compile pixels
    -- Two colors, and 255 brightnesses with either flag plus a zero brightness with the flag.
    unless (LTAGen.cardinality compiled == Right (2 * (255 * 2 + 1)))
        $ fail
        $ "unexpected count: " <> show (LTAGen.cardinality compiled)
    unless (LTAGen.unrank compiled 0 == Right (Green, 0, True))
        $ fail
        $ "unexpected first pixel: " <> show (LTAGen.unrank compiled 0)
    print (LTAGen.cardinality compiled)
    result <-
        QC.quickCheckResult $
            QC.conjoin
                [ LTAGen.forAll compiled $ \(color, brightness, dimmed) ->
                    color /= Red && (brightness > 0 || dimmed)
                , QC.forAll (LTAGen.toGenWithRank compiled) $ \(rank, pixel) ->
                    LTAGen.unrank compiled rank == Right pixel
                ]
    unless (QC.isSuccess result) $
        fail "pixels, their replay, or their shrinking failed"
