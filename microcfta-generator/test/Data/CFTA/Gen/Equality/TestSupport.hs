{-# LANGUAGE TupleSections #-}

-- | Helpers shared by the generator specs.
module Data.CFTA.Gen.Equality.TestSupport (
    aggregateRights,
    decodesEveryRankExactly,
) where

import qualified Data.Map.Strict as Map
import Data.Ratio ((%))
import Test.Hspec (Expectation, expectationFailure, shouldBe)

import qualified Data.CFTA.Gen.Equality as Core
import Data.CFTA.Ranked.Internal.Sampler (Exact (..))

-- | Aggregate exact ticket multiplicities by their sampled result.
aggregateRights :: (Ord a) => [(Rational, Either e a)] -> [(Rational, a)]
aggregateRights outcomes =
    [ (mass, value)
    | (value, mass) <-
        Map.toAscList $
            Map.fromListWith
                (+)
                [ (value, mass)
                | (mass, Right value) <- outcomes
                ]
    ]

{- | Enumerate the compiled decoder through the exact backend and require,
for every rank in order: uniform mass and agreement with 'Core.unrank'.
-}
decodesEveryRankExactly :: (Eq a, Show a) => Core.ECTAGen a -> Expectation
decodesEveryRankExactly generator =
    case Core.cardinality generator of
        Left err -> expectationFailure $ show err
        Right total ->
            runExact (Core.lowerWithRankVia generator)
                `shouldBe` [ (1 % total, fmap (rank,) (Core.unrank generator rank))
                           | rank <- [0 .. total - 1]
                           ]
