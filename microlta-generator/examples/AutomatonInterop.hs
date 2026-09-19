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

import Data.CFTA.Generic (HasFTA, TypedFTA, annotateDatatype, constructorName, deriveFTA)
import Data.LTA (Refinement, unconstrainedConstraint)
import qualified Data.LTA.Gen.QuickCheck as LTA
import Data.LTA.Guard (requires)
import Data.LTA.LiquidFixpoint (integerDeclarations, withZ3)
import Data.LTA.Refinement (integer, value, (.==.), (.>.))

-- | A successor term denotes a positive integer.
positive :: Refinement
positive = value .>. integer 0

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

-- | Import heights zero through two, then reject zero before dividing.
divisions :: LTA.LTAGen (Integer, Integer, Integer)
divisions =
    LTA.node "divide" (\_ denominator -> denominator `requires` positive) $ LTA.do
        numerator <- numerators
        denominator <- fmap naturalValue naturalNumbers
        LTA.pure (numerator, denominator, numerator `div` denominator)
  where
    naturalNumbers = LTA.fromDatatypeUpToDepth 2 $ annotateDatatype annotate naturals
    annotate constructor =
        (if constructorName constructor == "Zero" then value .==. integer 0 else positive, unconstrainedConstraint)
    numerators =
        LTA.pool
            [ LTA.refined 12 "twelve" (value .==. integer 12)
            , LTA.refined 24 "twenty-four" (value .==. integer 24)
            ]

-- | Compile once, check every replay rank, and sample the accepted divisions.
main :: IO ()
main = do
    withZ3 (integerDeclarations ["v"]) $ \solver -> do
        compiled <- LTA.compile solver divisions >>= either (fail . LTA.explain) pure
        let expected = [(12, 1, 12), (12, 2, 6), (24, 1, 24), (24, 2, 12)]
            replayed =
                traverse
                    (fmap LTA.generatedValue . (LTA.unrank compiled))
                    [0 .. LTA.cardinality compiled - 1]
        unless (replayed == Right expected)
            $ fail
            $ "unexpected replayed divisions: " <> show replayed
        print expected
        result <-
            QC.quickCheckResult $
                QC.conjoin
                    [ LTA.forAll compiled $ \(numerator, denominator, quotient) ->
                        denominator > 0 && quotient == numerator `div` denominator
                    , QC.forAll (LTA.toGenWithRank compiled) $ \(rank, division) ->
                        fmap LTA.generatedValue (LTA.unrank compiled rank) == Right division
                    ]
        unless (QC.isSuccess result) $
            fail "imported automaton generation or replay failed"
