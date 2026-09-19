{- | Complete generated witnesses and the checks that accept them.

A witness fixes one constructor, its refinement, its guard, and its children.
This module reads a witness as a term, checks it structurally and with the
solver, and builds the LTA support of a set of witnesses. It also holds the
entailment cache that every check shares.
-}
module Data.CFTA.Gen.Refinement.Internal.Witness (
    Witness (..),
    witnessTerm,
    termWitness,
    validateWitness,
    checkWitness,
    compileWitnesses,
    cacheEntailment,
) where

import Data.Bifunctor (first)
import Data.IORef (modifyIORef', newIORef, readIORef)
import qualified Data.Map.Strict as Map
import qualified Data.Tree as Tree

import Data.CFTA.Gen.Error (GenError (..))
import Data.CFTA.Refinement

-- | One complete generated node with its refinement, guard, and children.
data Witness = Witness
    { witnessSymbol :: !Symbol
    , witnessRefinement :: !Refinement
    , witnessConstraint :: !LiquidConstraint
    , witnessChildren :: ![Witness]
    }

-- | Read one witness as its annotated liquid term.
witnessTerm :: Witness -> Tree.Tree LiquidSymbol
witnessTerm Witness{witnessSymbol, witnessRefinement, witnessChildren} =
    Tree.Node
        (LiquidSymbol witnessSymbol witnessRefinement)
        (map witnessTerm witnessChildren)

-- | A compiled term needs no further constraints on its singleton witness.
termWitness :: Tree.Tree LiquidSymbol -> Witness
termWitness (Tree.Node (LiquidSymbol symbol refinement) childTerms) =
    Witness symbol refinement unconstrainedConstraint $ map termWitness childTerms

{- | Check the ranked-alphabet invariant of one witness.

All states allocated from a finite witness are present and acyclic, leaving
inconsistent reuse of one ranked symbol as the only possible structural error.
-}
validateWitness :: Witness -> Either GenError ()
validateWitness rootWitness = go Map.empty [rootWitness]
  where
    go _ [] = Right ()
    go arities (witness : rest) =
        let symbol = witnessSymbol witness
            actual = length $ witnessChildren witness
         in case Map.lookup symbol arities of
                Nothing ->
                    go
                        (Map.insert symbol actual arities)
                        (witnessChildren witness <> rest)
                Just expected
                    | expected == actual -> go arities (witnessChildren witness <> rest)
                    | otherwise ->
                        Left . InvalidSupport $
                            InconsistentArity symbol expected actual

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

-- | Build the LTA support that accepts exactly the given witnesses.
compileWitnesses :: [Witness] -> Either GenError Automaton
compileWitnesses [] = Left EmptyGenerator
compileWitnesses witnesses = do
    let root = Node $ map witnessTransition witnesses
    first InvalidSupport $ validate root
    pure root

-- | One transition whose children each accept exactly one child witness.
witnessTransition :: Witness -> Transition
witnessTransition Witness{witnessSymbol, witnessRefinement, witnessConstraint, witnessChildren} =
    Transition
        witnessSymbol
        witnessRefinement
        [Node [witnessTransition child] | child <- witnessChildren]
        witnessConstraint

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
