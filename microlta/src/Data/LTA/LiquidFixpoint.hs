-- | A Z3-backed 'Entailment' implemented with Liquid Fixpoint's SMT API.
module Data.LTA.LiquidFixpoint (
    withZ3,
    withZ3Assuming,
) where

import Control.Concurrent.MVar (modifyMVar, newMVar, withMVar)
import Control.Exception (bracket)
import Control.Monad.State.Lazy (runStateT)
import qualified Data.Text as Text

import Data.LTA (Entailment (Entailment), Verdict (..))
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.Smt.Types as SMTTypes
import qualified Language.Fixpoint.Types as Fixpoint
import Language.Fixpoint.Types.Config (SMTSolver (Z3), defConfig, solver)

-- | Run actions using one reusable Z3 process and a fixed declaration set.
withZ3 :: [(Fixpoint.Symbol, Fixpoint.Sort)] -> (Entailment -> IO a) -> IO a
withZ3 declarations = withZ3Assuming declarations []

{- | Run entailment queries under a fixed collection of ambient assumptions.

This models the surrounding Liquid typing environment. For example, an input
named @bufferLength@ may be declared as an integer and assumed equal to three;
position substitution can then prove that an index lies below that particular
buffer length. The declarations must include every free name used by the
refinements, including term symbols that become actual values in a position
substitution.
-}
withZ3Assuming ::
    [(Fixpoint.Symbol, Fixpoint.Sort)] ->
    [Fixpoint.Pred] ->
    (Entailment -> IO a) ->
    IO a
withZ3Assuming declarations assumptions action =
    bracket acquire release $ \contextVar ->
        action (Entailment $ query contextVar)
  where
    config = defConfig{solver = Z3}

    acquire = newMVar =<< SMT.makeContextNoLog config
    release contextVar = withMVar contextVar SMT.cleanupContext

    query contextVar antecedent consequent =
        modifyMVar contextVar $ \context -> do
            (response, nextContext) <- runStateT check context
            verdict <- responseVerdict response
            pure (nextContext, verdict)
      where
        check = SMT.smtBracket "microlta entailment" $ do
            SMT.smtDecls declarations
            SMT.smtAssertDecl $
                Fixpoint.pAnd (assumptions <> [antecedent, Fixpoint.PNot consequent])
            SMT.command SMTTypes.CheckSat

    responseVerdict SMTTypes.Unsat = pure Yes
    responseVerdict SMTTypes.Sat = pure No
    responseVerdict SMTTypes.Unknown = pure Unknown
    responseVerdict (SMTTypes.Error message) =
        ioError . userError $ "Z3 rejected a microlta query: " <> Text.unpack message
    responseVerdict response =
        ioError . userError $ "Unexpected Z3 response: " <> show response
