-- | Helpers shared by the generator specs.
module Data.CFTA.Gen.Equality.TestSupport (
    aggregateRights,
    decodesEveryRankExactly,
    ranksBack,
    ranksEveryTermBack,
    renameSymbols,
) where

import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import Data.Typeable (Typeable)
import Test.Hspec (Expectation, expectationFailure, shouldBe)

import qualified Data.CFTA as FTA
import Data.CFTA.Equality (Node)
import qualified Data.CFTA.Gen.Equality as ECTAGen
import Data.CFTA.Gen.Internal.Automaton (finiteAutomatonRank)
import qualified Data.CFTA.Gen.Internal.Flat as Flat
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

-- | Require that the term at each rank of a finite import ranks back to that rank.
ranksBack ::
    (Ord symbol, Hashable symbol, Typeable symbol, Ord key) =>
    (symbol -> key) -> Node symbol -> [Rank] -> Expectation
ranksBack order root ranks =
    (traverse (ECTAGen.unrank $ Flat.fromAutomaton order root) ranks >>= traverse (finiteAutomatonRank order root))
        `shouldBe` Right ranks

-- | Require that the term at every rank of a finite import ranks back to that rank.
ranksEveryTermBack ::
    (Ord symbol, Hashable symbol, Typeable symbol, Ord key) =>
    (symbol -> key) -> Node symbol -> Expectation
ranksEveryTermBack order root =
    case ECTAGen.cardinality $ Flat.fromAutomaton order root of
        Left err -> expectationFailure $ show err
        Right total -> ranksBack order root $ everyRank total
