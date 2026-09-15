{- | Complete generated witnesses and the checks that accept them.

A witness fixes one constructor, its refinement, its guard, and its children.
This module reads a witness as a term, checks it structurally and with the
solver, and builds the LTA support of a set of witnesses. It also holds the
entailment cache that every check shares.
-}
module Data.LTA.Gen.Internal.Witness (
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

import Data.LTA
import Data.LTA.Gen.Internal.Error (GeneratorError (..))

-- | One complete generated node with its refinement, guard, and children.
data Witness = Witness
    { witnessSymbol :: !Symbol
    , witnessRefinement :: !Refinement
    , witnessConstraint :: !LiquidConstraint
    , witnessChildren :: ![Witness]
    }

-- | Read one witness as its annotated liquid term.
witnessTerm :: Witness -> LiquidTerm
witnessTerm Witness{witnessSymbol, witnessRefinement, witnessChildren} =
    LiquidTerm
        witnessSymbol
        witnessRefinement
        (map witnessTerm witnessChildren)

-- | A compiled term needs no further constraints on its singleton witness.
termWitness :: LiquidTerm -> Witness
termWitness (LiquidTerm symbol refinement childTerms) =
    Witness symbol refinement unconstrainedConstraint $ map termWitness childTerms

{- | Check the ranked-alphabet invariant of one witness.

All states allocated from a finite witness are present and acyclic, leaving
inconsistent reuse of one ranked symbol as the only possible structural error.
-}
validateWitness :: Witness -> Either GeneratorError ()
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
compileWitnesses :: [Witness] -> Either GeneratorError Automaton
compileWitnesses [] = Left EmptyGenerator
compileWitnesses witnesses =
    first InvalidSupport . mkAutomaton root . Map.toList . buildRows $
        foldl (flip $ addWitnessAt root) initialBuild witnesses
  where
    root = State 0
    initialBuild = Build 1 (Map.singleton root [])

-- | The states allocated so far while witnesses become an automaton.
data Build = Build
    { buildNextState :: !Int
    , buildRows :: !(Map.Map State [Transition])
    }

-- | Add one transition for a witness, and rows for its children.
addWitnessAt :: State -> Witness -> Build -> Build
addWitnessAt state witness build =
    let (childStates, withChildren) = addChildren (witnessChildren witness) build
        transition =
            Transition
                (witnessSymbol witness)
                (witnessRefinement witness)
                childStates
                (witnessConstraint witness)
     in withChildren
            { buildRows =
                Map.insertWith
                    (flip (<>))
                    state
                    [transition]
                    (buildRows withChildren)
            }

-- | Allocate one fresh state for each direct child witness.
addChildren :: [Witness] -> Build -> ([State], Build)
addChildren [] build = ([], build)
addChildren (witness : rest) build =
    let child = State (buildNextState build)
        allocated =
            build
                { buildNextState = buildNextState build + 1
                , buildRows = Map.insert child [] (buildRows build)
                }
        withChild = addWitnessAt child witness allocated
        (childStates, finished) = addChildren rest withChild
     in (child : childStates, finished)

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
