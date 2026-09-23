{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TypeApplications #-}

-- | Import a recursive LTA and compose its bounded terms with an ordinary pool.
module Main (main) where

import Control.Monad (unless)
import GHC.Generics (Generic)
import qualified Test.QuickCheck as QC

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Generic (HasFTA, TypedFTA, annotateConstructors, deriveFTA)
import Data.CFTA.Refinement (unconstrainedConstraint)
import Data.CFTA.Refinement.Expression (Refinement, (.==), (.>))

-- | A successor term denotes a positive integer.
positive :: Refinement
positive v = v .> 0

-- | Natural-number constructor structure.
data Natural = Zero | Successor Natural
    deriving (Eq, Show, Generic)

instance HasFTA Natural

-- | Derive the recursive grammar once, independently of its refinements.
naturals :: TypedFTA () Natural
naturals = either (error . show) id $ deriveFTA @Natural

-- | Interpret the generated datatype.
naturalValue :: Natural -> Integer
naturalValue Zero = 0
naturalValue (Successor child) = 1 + naturalValue child

-- | Import heights zero through two, and keep the positive ones as denominators.
divisions :: LTAGen.LTAGen (Integer, Integer, Integer)
divisions = LTAGen.node "divide" $ LTAGen.do
    numerator <- LTAGen.elements [12, 24]
    denominator <- naturalNumbers `LTAGen.satisfying` positive
    LTAGen.pure (numerator, denominator, numerator `div` denominator)
  where
    naturalNumbers = fmap naturalValue $ LTAGen.fromDatatypeUpToDepth 2 $ either (error . show) id annotated
    -- Zero denotes zero. Every other constructor, here Successor, is positive.
    annotated =
        annotateConstructors
            (positive, unconstrainedConstraint)
            [("Zero", (\v -> v .== 0, unconstrainedConstraint))]
            naturals

-- | Compile once, check every replay rank, and sample the accepted divisions.
main :: IO ()
main = do
    compiled <- LTAGen.compile divisions
    let expected = [(12, 1, 12), (12, 2, 6), (24, 1, 24), (24, 2, 12)]
        replayed = LTAGen.values compiled
    unless (replayed == Right expected)
        $ fail
        $ "unexpected replayed divisions: " <> show replayed
    print expected
    result <-
        QC.quickCheckResult $
            QC.conjoin
                [ LTAGen.forAll compiled $ \(numerator, denominator, quotient) ->
                    denominator > 0 && quotient == numerator `div` denominator
                , QC.forAll (LTAGen.toGenWithRank compiled) $ \(rank, division) ->
                    LTAGen.unrank compiled rank == Right division
                ]
    unless (QC.isSuccess result) $
        fail "imported automaton generation or replay failed"
