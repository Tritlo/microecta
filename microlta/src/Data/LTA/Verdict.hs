{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

{- | Three-valued decisions and the refinement entailment boundary.

Every semantic question about an LTA reaches a solver through 'Entailment'. A
solver can answer 'Unknown', and each combinator here keeps that answer
distinct from 'No'.
-}
module Data.LTA.Verdict (
    Verdict (..),
    Entailment (Entailment, entails),
    entailmentWithBindings,
    entailsWithBindings,
    RefinementRelation (..),
    refinementRelation,
    SemanticIntersection (..),
    semanticIntersection,
    negateVerdict,
    andVerdict,
    orVerdict,
    andM,
    orM,
) where

import qualified Language.Fixpoint.Types as Fixpoint

import Data.LTA.Types (Refinement)

-- | A three-valued decision. Solver uncertainty is never silently made false.
data Verdict = Yes | No | Unknown
    deriving (Eq, Show)

{- | The imperative entailment boundary used by the pure automaton structure.

Each binding pairs a fresh value name with a declared name of the same sort.
The binding does not assert equality between the two values.
-}
newtype Entailment = ScopedEntailment
    { entailsWithBindings :: [(Fixpoint.Symbol, Fixpoint.Symbol)] -> Refinement -> Refinement -> IO Verdict
    -- ^ Decide whether the first refinement implies the second under the bindings.
    }

{- | Construct a solver for queries that need no fresh value declarations.

The callback cannot declare fresh names. Such queries return 'Unknown'. Use
'entailmentWithBindings' to support distinct actuals with the same name.
-}
pattern Entailment :: (Refinement -> Refinement -> IO Verdict) -> Entailment
pattern Entailment{entails} <- (plainEntailment -> entails)
  where
    Entailment decide = ScopedEntailment $ \bindings antecedent consequent ->
        if null bindings then decide antecedent consequent else pure Unknown

{-# COMPLETE Entailment #-}

-- | Read the ordinary query interface of either entailment implementation.
plainEntailment :: Entailment -> Refinement -> Refinement -> IO Verdict
plainEntailment solver = entailsWithBindings solver []

-- | Construct a solver that can declare fresh values with existing sorts.
entailmentWithBindings ::
    ([(Fixpoint.Symbol, Fixpoint.Symbol)] -> Refinement -> Refinement -> IO Verdict) ->
    Entailment
entailmentWithBindings = ScopedEntailment

-- | The semantic subtype relationship between two refinements.
data RefinementRelation
    = -- | Each refinement implies the other.
      Equivalent
    | -- | The left refinement is strictly more specific.
      StrictSubtype
    | -- | The right refinement is strictly more specific.
      StrictSupertype
    | -- | Neither refinement implies the other.
      Incomparable
    | -- | The solver could not decide at least one required implication.
      RelationUnknown
    deriving (Eq, Show)

{- | Compare two refinements by asking for implication in both directions.

This four-way view is useful to clients that need to inspect an ordering.
Pruning and similarity themselves use directional entailment, matching the
paper's judgments. Solver uncertainty remains explicit.
-}
refinementRelation :: Entailment -> Refinement -> Refinement -> IO RefinementRelation
refinementRelation entailment left right = do
    leftToRight <- entails entailment left right
    rightToLeft <- entails entailment right left
    pure $ case (leftToRight, rightToLeft) of
        (Yes, Yes) -> Equivalent
        (Yes, No) -> StrictSubtype
        (No, Yes) -> StrictSupertype
        (No, No) -> Incomparable
        _ -> RelationUnknown

-- | Result of the paper's semantic intersection on refinement transitions.
data SemanticIntersection
    = -- | Entailment holds, so the antecedent transition is retained.
      RetainedAntecedent !Refinement
    | -- | The semantic entailment constraint cannot relate the transitions.
      BottomIntersection
    | -- | The solver could not decide the required relation.
      IntersectionUnknown
    deriving (Eq, Show)

{- | Apply the paper's directional semantic intersection to two refinements.

The first refinement is the antecedent transition at @p1@ and the second is the
consequent at @p2@. If @p1@ entails @p2@, the operation retains @p1@; it never
reverses the query to retain @p2@. This is Equation 4, not logical conjunction
or a symmetric meet.
-}
semanticIntersection :: Entailment -> Refinement -> Refinement -> IO SemanticIntersection
semanticIntersection entailment antecedent consequent = do
    verdict <- entails entailment antecedent consequent
    pure $ case verdict of
        Yes -> RetainedAntecedent antecedent
        No -> BottomIntersection
        Unknown -> IntersectionUnknown

-- | Exchange 'Yes' and 'No' while keeping solver uncertainty.
negateVerdict :: Verdict -> Verdict
negateVerdict Yes = No
negateVerdict No = Yes
negateVerdict Unknown = Unknown

-- | Conjoin two verdicts. One 'No' decides the result.
andVerdict :: Verdict -> Verdict -> Verdict
andVerdict No _ = No
andVerdict _ No = No
andVerdict Unknown _ = Unknown
andVerdict _ Unknown = Unknown
andVerdict Yes Yes = Yes

-- | Disjoin two verdicts. One 'Yes' decides the result.
orVerdict :: Verdict -> Verdict -> Verdict
orVerdict Yes _ = Yes
orVerdict _ Yes = Yes
orVerdict Unknown _ = Unknown
orVerdict _ Unknown = Unknown
orVerdict No No = No

-- | Conjoin verdicts in order and stop at the first 'No'.
andM :: [IO Verdict] -> IO Verdict
andM [] = pure Yes
andM (action : rest) = do
    verdict <- action
    case verdict of
        No -> pure No
        _ -> andVerdict verdict <$> andM rest

-- | Disjoin verdicts in order and stop at the first 'Yes'.
orM :: [IO Verdict] -> IO Verdict
orM [] = pure No
orM (action : rest) = do
    verdict <- action
    case verdict of
        Yes -> pure Yes
        _ -> orVerdict verdict <$> orM rest
