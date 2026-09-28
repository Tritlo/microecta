-- | Helpers shared by the generator specs.
module Data.CFTA.Gen.Equality.TestSupport (
    aggregateRights,
    decodesEveryRankExactly,
    ranksBack,
    ranksEveryMemberBack,
    renameSymbols,
) where

import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import Data.Typeable (Typeable)
import Test.Hspec (Expectation, expectationFailure, shouldBe)

import qualified Data.CFTA as FTA
import Data.CFTA.Equality (Node)
import qualified Data.CFTA.Gen.Equality as ECTAGen
import Data.CFTA.Index (Rank, everyRank)
import qualified Data.CFTA.Interned as Interned
import Data.CFTA.Ranked.Internal.Sampler (Exact (..))

-- | Copy an automaton under other symbols, through its explicit view.
renameSymbols ::
    (Hashable symbol, Ord symbol, Show symbol, Typeable symbol, Hashable other, Ord other, Show other, Typeable other) =>
    (symbol -> other) -> Node symbol -> Node other
renameSymbols rename automaton =
    case Interned.toFTA automaton of
        Left err -> error $ show err
        Right explicit -> case FTA.mapSymbols rename explicit of
            Left err -> error $ show err
            Right renamed -> Interned.fromFTA renamed

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
for every rank in order: uniform mass and agreement with 'ECTAGen.unrank'.
-}
decodesEveryRankExactly :: (Eq a, Show a) => ECTAGen.ECTAGen a -> Expectation
decodesEveryRankExactly generator =
    case ECTAGen.cardinality generator of
        Left err -> expectationFailure $ show err
        Right total ->
            runExact (ECTAGen.lowerWithRankVia generator)
                `shouldBe` [ (1 / toRational total, fmap (ECTAGen.RankedValue rank) (ECTAGen.unrank generator rank))
                           | rank <- everyRank total
                           ]

-- | Require that the member at each rank ranks back to that rank.
ranksBack ::
    (ECTAGen.Gen symbol a -> a -> Either ECTAGen.GenError Rank) ->
    ECTAGen.Gen symbol a ->
    [Rank] ->
    Expectation
ranksBack rank generator ranks =
    (traverse (ECTAGen.unrank generator) ranks >>= traverse (rank generator)) `shouldBe` Right ranks

-- | Require that the member at every rank of a finite generator ranks back to that rank.
ranksEveryMemberBack ::
    (ECTAGen.Gen symbol a -> a -> Either ECTAGen.GenError Rank) ->
    ECTAGen.Gen symbol a ->
    Expectation
ranksEveryMemberBack rank generator =
    case ECTAGen.cardinality generator of
        Left err -> expectationFailure $ show err
        Right total -> ranksBack rank generator $ everyRank total
