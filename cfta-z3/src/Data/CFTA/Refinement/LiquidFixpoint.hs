{- | A Z3-backed 'Entailment' implemented with Liquid Fixpoint's SMT API.

The entailment translates each 'Formula' to a Liquid Fixpoint expression. Every
name is an integer.
-}
module Data.CFTA.Refinement.LiquidFixpoint (
    withZ3,
    withZ3Assuming,
    withZ3Timeout,
    defaultTimeLimit,
    TimeLimitReached (..),
) where

import Control.Concurrent.MVar (modifyMVar, newMVar, withMVar)
import Control.Exception (Exception (..), SomeException, bracket, throwIO, try, uninterruptibleMask_)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Lazy (runStateT)
import qualified Data.HashSet as HashSet
import qualified Data.Text as Text
import GHC.Clock (getMonotonicTime)

import Data.CFTA.Formula (Formula (..), Name (..), Relation (..), Term (..))
import Data.CFTA.Refinement.Verdict (Entailment, Verdict (..), entailmentWithBindings)
import Data.CFTA.Symbol (valueName)
import qualified Language.Fixpoint.Smt.Interface as SMT
import qualified Language.Fixpoint.Smt.Types as SMTTypes
import qualified Language.Fixpoint.Types as Fixpoint
import Language.Fixpoint.Types.Config (SMTSolver (Z3), defConfig, smtTimeout, solver)

{- | Run actions using one reusable Z3 process and a fixed set of names that
it declares as integers. Each query has the time limit 'defaultTimeLimit', as
in 'withZ3Assuming'.
-}
withZ3 :: [Name] -> (Entailment -> IO a) -> IO a
withZ3 names = withZ3Assuming names []

{- | Run entailment queries under a fixed collection of ambient assumptions.

This models the surrounding Liquid typing environment. For example, an input
named @bufferLength@ may be declared as an integer and assumed equal to three;
position substitution can then prove that an index lies below that particular
buffer length. Each query declares as an integer every name of its formulas,
including 'valueName' and term symbols that become actual values in a position
substitution. A fresh value name of a binding must not be one of the given
names; otherwise the query gives 'Unknown'.

Each query has the time limit 'defaultTimeLimit'. A query that reaches the
limit raises 'TimeLimitReached'. 'withZ3Timeout' sets another limit.
-}
withZ3Assuming ::
    [Name] ->
    [Formula] ->
    (Entailment -> IO a) ->
    IO a
withZ3Assuming = withZ3Timeout defaultTimeLimit

-- | The time limit of each query of 'withZ3' and 'withZ3Assuming': ten seconds.
defaultTimeLimit :: Int
defaultTimeLimit = 10000

{- | 'withZ3Assuming' with a time limit for each query, in milliseconds.

Z3 has no time limit of its own, so a query that it cannot decide, for
example about non-linear integer arithmetic, can run without end. At the
limit, Z3 stops the query and answers @unknown@, as it does when it gives up
before the limit. The entailment measures the time of the check. When the
answer is @unknown@ and the check took the whole limit, it raises
'TimeLimitReached' instead of giving 'Unknown'. The next query runs normally.
-}
withZ3Timeout ::
    Int ->
    [Name] ->
    [Formula] ->
    (Entailment -> IO a) ->
    IO a
withZ3Timeout milliseconds names assumptions action =
    bracket acquire release $ \contextVar ->
        action (entailmentWithBindings $ query contextVar)
  where
    valueSymbol = Fixpoint.symbol valueName
    given = [(nameSymbol name, Fixpoint.FInt) | name <- names]
    declarations
        | valueSymbol `elem` map fst given = given
        | otherwise = (valueSymbol, Fixpoint.FInt) : given
    known = HashSet.fromList $ map fst declarations
    solverAssumptions = map toFixpoint assumptions

    config = defConfig{solver = Z3, smtTimeout = Just milliseconds}

    acquire = newMVar =<< SMT.makeContextNoLog config
    release contextVar = withMVar contextVar SMT.cleanupContext

    query contextVar bindings antecedentFormula consequentFormula =
        case traverse freshDeclaration bindings of
            Nothing -> pure Unknown
            Just freshDeclarations -> do
                outcome <- modifyMVar contextVar $ \context -> do
                    let mentioned = foldMap Fixpoint.exprSymbolsSet (antecedent : consequent : solverAssumptions)
                        declared = HashSet.union known $ HashSet.fromList $ map fst freshDeclarations
                        undeclared =
                            [(name, Fixpoint.FInt) | name <- HashSet.toList $ HashSet.difference mentioned declared]
                    attempt <- try $ runStateT (check (freshDeclarations <> undeclared)) context
                    case attempt of
                        -- An exception during the query, such as a time limit
                        -- of the caller, can leave an open scope and an unread
                        -- answer in the process. The next query would read that
                        -- answer, so a new process replaces the old one.
                        Left err -> do
                            fresh <- replaceContext context
                            pure (fresh, Left (err :: SomeException))
                        Right (answer@(response, _), nextContext) -> case response of
                            -- Z3 answers the rejected command and then the check-sat.
                            -- Liquid Fixpoint reads only the first answer, so the next
                            -- query would read the second. A new process replaces the
                            -- old one. Each query sends its own declarations. The test
                            -- "answers correctly after the solver rejects a query"
                            -- gets shifted answers without the new process (checked
                            -- with Z3 4.15.3 and Liquid Fixpoint 0.9.6.3.7).
                            SMTTypes.Error _ -> do
                                fresh <- replaceContext nextContext
                                pure (fresh, Right answer)
                            _ -> pure (nextContext, Right answer)
                either throwIO responseVerdict outcome
      where
        antecedent = toFixpoint antecedentFormula
        consequent = toFixpoint consequentFormula

        check freshDeclarations = SMT.smtBracket "cfta entailment" $ do
            SMT.smtDecls $ declarations <> freshDeclarations
            SMT.smtAssertDecl $
                Fixpoint.pAnd (solverAssumptions <> [antecedent, Fixpoint.PNot consequent])
            start <- liftIO getMonotonicTime
            response <- SMT.command SMTTypes.CheckSat
            end <- liftIO getMonotonicTime
            pure (response, end - start)

        -- Another interruption must not leave the old process in the variable.
        replaceContext context = uninterruptibleMask_ $ do
            _ <- try (SMT.cleanupContext context) :: IO (Either SomeException ())
            SMT.makeContextNoLog config

        freshDeclaration (fresh, _)
            | HashSet.member (nameSymbol fresh) known = Nothing
            | otherwise = Just (nameSymbol fresh, Fixpoint.FInt)

        responseVerdict (SMTTypes.Unsat, _) = pure Yes
        responseVerdict (SMTTypes.Sat, _) = pure No
        responseVerdict (SMTTypes.Unknown, seconds)
            | seconds * 1000 >= fromIntegral milliseconds = throwIO $ TimeLimitReached milliseconds
            | otherwise = pure Unknown
        responseVerdict (SMTTypes.Error message, _) =
            ioError . userError $ "Z3 rejected a cfta query: " <> Text.unpack message
        responseVerdict (response, _) =
            ioError . userError $ "Unexpected Z3 response: " <> show response

-- | The Liquid Fixpoint expression of a formula.
toFixpoint :: Formula -> Fixpoint.Expr
toFixpoint formula = case formula of
    Top -> Fixpoint.PTrue
    And parts -> Fixpoint.PAnd $ map toFixpoint parts
    Bottom -> Fixpoint.PFalse
    Or parts -> Fixpoint.POr $ map toFixpoint parts
    Not inner -> Fixpoint.PNot $ toFixpoint inner
    Atom relation left right -> Fixpoint.PAtom (brel relation) (termToFixpoint left) (termToFixpoint right)
  where
    brel relation = case relation of
        Eq -> Fixpoint.Eq
        Ne -> Fixpoint.Ne
        Gt -> Fixpoint.Gt
        Ge -> Fixpoint.Ge
        Lt -> Fixpoint.Lt
        Le -> Fixpoint.Le

-- | The Liquid Fixpoint expression of a term.
termToFixpoint :: Term -> Fixpoint.Expr
termToFixpoint term = case term of
    Lit value -> Fixpoint.ECon $ Fixpoint.I value
    Var name -> Fixpoint.EVar $ nameSymbol name
    Neg inner -> Fixpoint.ENeg $ termToFixpoint inner
    Add left right -> Fixpoint.EBin Fixpoint.Plus (termToFixpoint left) (termToFixpoint right)
    Sub left right -> Fixpoint.EBin Fixpoint.Minus (termToFixpoint left) (termToFixpoint right)
    Mul left right -> Fixpoint.EBin Fixpoint.Times (termToFixpoint left) (termToFixpoint right)
    Ite condition yes no -> Fixpoint.EIte (toFixpoint condition) (termToFixpoint yes) (termToFixpoint no)

-- | The Liquid Fixpoint symbol of a name.
nameSymbol :: Name -> Fixpoint.Symbol
nameSymbol (Name text) = Fixpoint.symbol text

{- | Z3 stopped a query at the time limit, in milliseconds, before it decided
the query.
-}
newtype TimeLimitReached = TimeLimitReached Int
    deriving (Eq, Show)

instance Exception TimeLimitReached where
    displayException (TimeLimitReached milliseconds) =
        "Z3 stopped a query at the time limit of "
            <> show milliseconds
            <> " milliseconds. Run it again with a higher limit through withZ3Timeout,"
            <> " or simplify the refinements, for example remove non-linear arithmetic."
