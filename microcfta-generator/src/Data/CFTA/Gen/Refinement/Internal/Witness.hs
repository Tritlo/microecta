{- | Complete generated witnesses and the check that accepts them.

A witness fixes one constructor, its guard, and its children. This module
reads a witness as a term and checks it with the solver. It also holds the
entailment cache that every check of one compilation shares.
-}
module Data.CFTA.Gen.Refinement.Internal.Witness (
    Witness (..),
    witnessTerm,
    termWitness,
    checkWitness,
    cacheEntailment,
) where

import Data.IORef (modifyIORef', newIORef, readIORef)
import qualified Data.Map.Strict as Map
import qualified Data.Tree as Tree

import Data.CFTA.Refinement

-- | One complete generated node with its label, guard, and children.
data Witness = Witness
    { witnessLabel :: !LiquidSymbol
    , witnessConstraint :: !LiquidConstraint
    , witnessChildren :: ![Witness]
    }

-- | Read one witness as its annotated liquid term.
witnessTerm :: Witness -> Tree.Tree LiquidSymbol
witnessTerm Witness{witnessLabel, witnessChildren} =
    Tree.Node witnessLabel (map witnessTerm witnessChildren)

-- | A compiled term needs no further constraints on its singleton witness.
termWitness :: Tree.Tree LiquidSymbol -> Witness
termWitness (Tree.Node label childTerms) =
    Witness label unconstrainedConstraint $ map termWitness childTerms

{- | Check one generated witness directly against its own liquid guards.

A generated witness already fixes every transition and child, so structural
recognition cannot reject it; only child validity and guards can.
-}
checkWitness :: Entailment -> Witness -> IO Verdict
checkWitness entailment witness = do
    childrenVerdict <- checkChildren (witnessChildren witness)
    case childrenVerdict of
        No -> pure No
        _ -> do
            constraintVerdict <- evaluateConstraint entailment (witnessConstraint witness) (witnessTerm witness)
            pure $ andVerdicts childrenVerdict constraintVerdict
  where
    checkChildren [] = pure Yes
    checkChildren (child : rest) = do
        childVerdict <- checkWitness entailment child
        case childVerdict of
            No -> pure No
            _ -> andVerdicts childVerdict <$> checkChildren rest

    andVerdicts No _ = No
    andVerdicts _ No = No
    andVerdicts Unknown _ = Unknown
    andVerdicts _ Unknown = Unknown
    andVerdicts Yes Yes = Yes

{- | Cache exact refinement queries for one compilation run.

Applicative generator products repeat the same local liquid obligations across
many complete witnesses. The entailment boundary is deterministic for a fixed
solver environment, so one verdict can safely serve every identical request
during this compile without making the cache part of the public API.
-}
cacheEntailment :: Entailment -> IO Entailment
cacheEntailment underlying = do
    verdicts <- newIORef Map.empty
    pure $ entailmentWithBindings $ \bindings antecedent consequent -> do
        cache <- readIORef verdicts
        let obligation = (bindings, antecedent, consequent)
        case Map.lookup obligation cache of
            Just verdict -> pure verdict
            Nothing -> do
                verdict <- entailsWithBindings underlying bindings antecedent consequent
                modifyIORef' verdicts $ Map.insert obligation verdict
                pure verdict
