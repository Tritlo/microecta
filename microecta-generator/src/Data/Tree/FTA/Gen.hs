{-# LANGUAGE BangPatterns #-}

{- | Compile ordinary finite-language FTAs into ranked generators.

The FTA remains the inspectable support. This module adds exact cardinality,
stable replay ranks, backend-independent sampling, and structural shrinking.
Ranks identify accepting derivations; an ambiguous FTA may therefore produce
the same concrete term at more than one rank.
-}
module Data.Tree.FTA.Gen (
    CompileError (..),
    fromFTA,
) where

import Data.Maybe (mapMaybe)

import qualified Data.Tree.FTA as FTA
import Data.Tree.Gen (Ranked)
import qualified Data.Tree.Gen as Ranked
import Data.Tree.Term (Term (Term))

-- | Failure while compiling an FTA into a finite ranked language.
data CompileError state
    = -- | A cyclic FTA needs an explicit size bound before it is finite.
      RecursiveFTA !state
    | -- | The initial state accepts no terms.
      EmptyFTALanguage
    deriving (Eq, Show)

-- | Compile an acyclic ordinary FTA into its finite accepting derivations.
fromFTA ::
    (Ord state) =>
    FTA.PlainFTA state symbol ->
    Either (CompileError state) (Ranked (Term symbol))
fromFTA automaton = case FTA.cycleState automaton of
    Just state -> Left (RecursiveFTA state)
    Nothing -> maybe (Left EmptyFTALanguage) Right (compileState $ FTA.initialState automaton)
  where
    compileState state =
        combine $ mapMaybe compileTransition $ FTA.transitionsFrom automaton state

    compileTransition transition = do
        children <- traverse compileState (FTA.transitionChildren transition)
        pure $ buildTerm (FTA.transitionSymbol transition) children

    combine [] = Nothing
    combine alternatives =
        case Ranked.oneof alternatives of
            Left _ -> Nothing
            Right ranked -> Just ranked

buildTerm :: symbol -> [Ranked (Term symbol)] -> Ranked (Term symbol)
buildTerm symbol children =
    ($ [])
        <$> foldl'
            applyChild
            (pure $ Term symbol)
            children
  where
    applyChild partial child =
        (\finish value rest -> finish (value : rest)) <$> partial <*> child
