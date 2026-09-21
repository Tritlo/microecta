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

import qualified Data.CFTA.Gen.Refinement as LTAGen
import Data.CFTA.Ranked.Internal.Sampler (Exact (..))
import Data.CFTA.Refinement (Entailment, LiquidSymbol)

-- | Compile a fixture, reporting a compilation error as an Hspec failure.
compileOrFail :: Entailment -> LTAGen.LTAGen a -> IO (LTAGen.LTAGen a)
compileOrFail solver generator = LTAGen.compile solver generator >>= rightOrFail

-- | Report a construction or compilation error as an Hspec failure.
rightOrFail :: (Show err) => Either err a -> IO a
rightOrFail result =
    case result of
        Left err -> expectationFailure (show err) >> fail "unreachable"
        Right compiled -> pure compiled

-- | Every rank of a finite generator; none when it failed.
ranks :: LTAGen.LTAGen a -> [Integer]
ranks generator = either (const []) (\total -> [0 .. total - 1]) $ LTAGen.cardinality generator

-- | Enumerate one small compiled language in stable rank order.
values :: LTAGen.LTAGen a -> [a]
values generator = [value | rank <- ranks generator, Right value <- [LTAGen.unrank generator rank]]

-- | The accepted liquid term of every rank, in rank order.
termsOf :: LTAGen.LTAGen a -> [Tree.Tree LiquidSymbol]
termsOf generator = [term | rank <- ranks generator, Right term <- [termOf generator rank]]

-- | The accepted liquid term of one rank: the user's part of the engine's term.
termOf :: LTAGen.LTAGen a -> Integer -> Either LTAGen.GenError (Tree.Tree LiquidSymbol)
termOf generator rank = do
    labelled <- LTAGen.termAt generator rank
    case LTAGen.surface labelled of
        [term] -> Right term
        _ -> Left LTAGen.CannotInspectOpaqueGenerator

-- | The exact sampling mass of every rank.
massesByRank :: LTAGen.LTAGen a -> [(Integer, Rational)]
massesByRank generator =
    [(rank, mass) | (mass, Right (rank, _)) <- runExact $ LTAGen.lowerWithRankVia generator]
