{- | Complete generated witnesses and the check that accepts them.

A witness fixes one constructor, its guard, and its children. This module
reads a witness as a term and checks it with the solver. It also holds the
entailment cache that every check of one compilation shares.
-}
module Data.CFTA.Gen.Refinement.Internal.Witness (
    Witness (..),
    termWitness,
    checkWitness,
    cacheEntailment,
) where

import Data.IORef (modifyIORef', newIORef, readIORef)
import qualified Data.Map.Strict as Map

import Data.CFTA.Refinement
import Data.CFTA.Refinement.Verdict (andVerdicts)
import Data.CFTA.Term (Term)
import qualified Data.CFTA.Term as Term

-- | One complete generated node with its label, guard, and children.
data Witness = Witness
    { witnessLabel :: !Symbol
    , witnessConstraint :: !Constraint
    , witnessChildren :: ![Witness]
    }

-- | Read one witness as its annotated liquid term.
witnessTerm :: Witness -> Term Symbol
witnessTerm Witness{witnessLabel, witnessChildren} =
    Term.Node witnessLabel (map witnessTerm witnessChildren)

{- | The witness of a term that the engine already accepted. No node of the
witness has a constraint.
-}
termWitness :: Term Symbol -> Witness
termWitness (Term.Node label childTerms) =
    Witness label noConstraint $ map termWitness childTerms

{- | Check a witness and its children against their guards.

A witness fixes every transition and every child, so only a guard can
reject it.
-}
checkWitness :: Entailment -> Witness -> IO Verdict
checkWitness entailment witness =
    andVerdicts $
        map (checkWitness entailment) (witnessChildren witness)
            <> [evaluateConstraint entailment (witnessConstraint witness) (witnessTerm witness)]

{- | Cache exact refinement queries for one compilation run.

The products of a generator send the solver the same query for many
witnesses. In the benchmark cells @lta-automaton@ and @lta-do@, 87% and 97%
of the queries of one compilation repeat an earlier query. A fixed solver
environment gives the same verdict for the same query, so the cache returns
the first verdict for each repeat. Each compilation has its own cache.

The cache also keeps 'Unknown' verdicts. 'Unknown' is the conservative
answer, and the cache gives the same answer for each repeat. A Z3 query that
reaches the time limit raises 'TimeLimitReached' and gives no verdict. Z3 gave
no 'Unknown' in the test suite or in the benchmark cells.
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
