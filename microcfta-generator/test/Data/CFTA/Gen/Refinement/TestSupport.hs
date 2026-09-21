-- | Helpers shared by the refinement specs.
module Data.CFTA.Gen.Refinement.TestSupport (
    compileOrFail,
    rightOrFail,
    ranks,
    values,
    termsOf,
    termOf,
    massesByRank,
) where

import qualified Data.Tree as Tree
import Test.Hspec (expectationFailure)

import qualified Data.CFTA.Gen.Refinement as LTA
import Data.CFTA.Ranked.Internal.Sampler (Exact (..))
import Data.CFTA.Refinement (Entailment, LiquidSymbol)

-- | Compile a fixture, reporting a compilation error as an Hspec failure.
compileOrFail :: Entailment -> LTA.LTAGen a -> IO (LTA.LTAGen a)
compileOrFail solver generator = LTA.compile solver generator >>= rightOrFail

-- | Report a construction or compilation error as an Hspec failure.
rightOrFail :: (Show err) => Either err a -> IO a
rightOrFail result =
    case result of
        Left err -> expectationFailure (show err) >> fail "unreachable"
        Right compiled -> pure compiled

-- | Every rank of a finite generator; none when it failed.
ranks :: LTA.LTAGen a -> [Integer]
ranks generator = either (const []) (\total -> [0 .. total - 1]) $ LTA.cardinality generator

-- | Enumerate one small compiled language in stable rank order.
values :: LTA.LTAGen a -> [a]
values generator = [value | rank <- ranks generator, Right value <- [LTA.unrank generator rank]]

-- | The accepted liquid term of every rank, in rank order.
termsOf :: LTA.LTAGen a -> [Tree.Tree LiquidSymbol]
termsOf generator = [term | rank <- ranks generator, Right term <- [termOf generator rank]]

-- | The accepted liquid term of one rank: the user's part of the engine's term.
termOf :: LTA.LTAGen a -> Integer -> Either LTA.GenError (Tree.Tree LiquidSymbol)
termOf generator rank = do
    labelled <- LTA.termAt generator rank
    case LTA.surface labelled of
        [term] -> Right term
        _ -> Left LTA.CannotInspectOpaqueGenerator

-- | The exact sampling mass of every rank.
massesByRank :: LTA.LTAGen a -> [(Integer, Rational)]
massesByRank generator =
    [(rank, mass) | (mass, Right (rank, _)) <- runExact $ LTA.lowerWithRankVia generator]
