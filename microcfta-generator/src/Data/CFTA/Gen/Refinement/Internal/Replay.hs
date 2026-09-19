{- | Replay and shrinking of a compiled generator.

Every solver call finishes during compilation, so this module stays pure. It
decodes an accepted rank, follows the valid shrinks of that rank, and turns
source shrink plans into accepted ranks through the shared shrink search.
-}
module Data.CFTA.Gen.Refinement.Internal.Replay (
    cardinality,
    unrank,
    shrinkRank,
    smallerMembers,
    mapCompiled,
    compiledSource,
    ImplicationTable,
    evaluateImplications,
    sourceShrinkRanks,
) where

import Data.Bifunctor (first)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set

import Data.CFTA.Gen.Error (GenError, fromRankedError)
import Data.CFTA.Gen.Refinement.Internal.ShrinkSearch (acceptedShrinks)
import Data.CFTA.Gen.Refinement.Internal.Types
import Data.CFTA.Gen.Refinement.Internal.Witness (termWitness)
import qualified Data.CFTA.Ranked as Tree
import Data.CFTA.Refinement

-- | Exact number of accepted, replayable outcomes.
cardinality :: Compiled a -> Integer
cardinality = Tree.cardinality . compiledRanked

-- | Decode one accepted zero-based rank into its value and witness.
unrank :: Compiled a -> Integer -> Either GenError (Generated a)
unrank compiled rank = first fromRankedError $ Tree.unrank (compiledRanked compiled) rank

-- | Direct valid shrinks of one accepted rank.
shrinkRank :: Compiled a -> Integer -> [Integer]
shrinkRank compiled rank
    | rank < 0 || rank >= cardinality compiled = []
    | otherwise =
        unique Set.empty $ compiledPlanShrinks compiled rank
  where
    unique _ [] = []
    unique seen (candidate : rest)
        | Set.member candidate seen = unique seen rest
        | otherwise = candidate : unique (Set.insert candidate seen) rest

-- | All transitively smaller accepted members reachable from one rank.
smallerMembers :: Compiled a -> Integer -> [(Integer, Generated a)]
smallerMembers compiled rank =
    [ (candidate, generated)
    | candidate <- allShrinks compiled rank
    , Right generated <- [unrank compiled candidate]
    ]

-- | All transitively smaller accepted ranks reachable from one rank.
allShrinks :: Compiled a -> Integer -> [Integer]
allShrinks compiled start = go Set.empty (shrinkRank compiled start)
  where
    go _ [] = []
    go visited (rank : rest)
        | Set.member rank visited = go visited rest
        | otherwise =
            rank
                : go
                    (Set.insert rank visited)
                    (shrinkRank compiled rank <> rest)

{- | Change only the Haskell view of a compiled LTA member.

The accepted liquid term, stable rank, support automaton, and shrink graph are
unchanged.
-}
mapCompiled :: (a -> b) -> Compiled a -> Compiled b
mapCompiled transform compiled =
    compiled
        { compiledRanked = mapGenerated <$> compiledRanked compiled
        }
  where
    mapGenerated generated =
        generated{generatedValue = transform $ generatedValue generated}

-- | Reuse a compiled term set as one finite source with its existing shrinks.
compiledSource :: Compiled a -> LTAGen a
compiledSource compiled =
    LTAGen
        (Just $ Prepared outcomes shrink)
        (Right $ CompiledRecipe compiled)
  where
    outcomes = case Tree.fromIndexedOnDemand $ Tree.Indexed (cardinality compiled) outcomeAt of
        Right ranked -> RankedFinite ranked
        Left err -> error $ "microcfta-generator bug in Data.CFTA.Gen.Refinement.Internal.Replay: invalid compiled source: " <> show err
    outcomeAt rank = case unrank compiled rank of
        Right generated ->
            Outcome (generatedWeight generated) (generatedValue generated) (termWitness $ generatedTerm generated)
        Left err -> error $ "microcfta-generator bug in Data.CFTA.Gen.Refinement.Internal.Replay: invalid source rank: " <> show err
    shrink rank = map (`ShrinkCandidate` AlwaysShrink) $ shrinkRank compiled rank

-- | The solver verdict for each refinement implication that shrinking needs.
type ImplicationTable = [((Refinement, Refinement), Verdict)]

-- | Ask the solver once for each requested refinement implication.
evaluateImplications ::
    Entailment ->
    [(Refinement, Refinement)] ->
    IO ImplicationTable
evaluateImplications entailment = go []
  where
    go table [] = pure $ reverse table
    go table ((antecedent, consequent) : rest) = do
        verdict <- entails entailment antecedent consequent
        go (((antecedent, consequent), verdict) : table) rest

-- | Decide whether the table permits one source shrink condition.
conditionHolds :: ImplicationTable -> ShrinkCondition -> Bool
conditionHolds _ AlwaysShrink = True
conditionHolds table (WeakenRefinement source candidate equivalentEarlier) =
    implication source candidate == Yes
        && (implication candidate source == No || equivalentEarlier)
  where
    implication antecedent consequent
        | antecedent == consequent = Yes
        | otherwise = fromMaybe Unknown $ lookup (antecedent, consequent) table

-- | Follow source shrinks to accepted ranks without materializing the language.
sourceShrinkRanks ::
    LTAGen a ->
    Integer ->
    (Integer -> Maybe Integer) ->
    ImplicationTable ->
    Integer ->
    [Integer]
sourceShrinkRanks generator acceptedCount acceptedRankFor implications =
    acceptedShrinks acceptedCount eligible acceptedRankFor
  where
    eligible source =
        [ shrinkCandidateIndex candidate
        | candidate <- generatorShrinks generator source
        , conditionHolds implications (shrinkCandidateCondition candidate)
        ]
