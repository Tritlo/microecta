{- | Generator failures and the advice that explains them.

Every compilation path reports its failures through 'GeneratorError'. 'explain'
turns one failure into the next action a caller can take, in terms of the
public API.
-}
module Data.CFTA.Gen.Refinement.Internal.Error (
    GeneratorError (..),
    explain,
    fromRankedError,
) where

import Data.CFTA.Constraint.Equality (EqConstraints)
import qualified Data.CFTA.Gen.Equality.QuickCheck as ECTA
import qualified Data.CFTA.Ranked as Tree
import Data.CFTA.Refinement

-- | Failure while building, checking, or selecting from a generator.
data GeneratorError
    = -- | No candidate satisfies the language.
      EmptyGenerator
    | -- | A choice weight was not positive.
      NonPositiveWeight !Integer
    | -- | A replay rank was negative.
      NegativeRank !Integer
    | -- | A replay rank was outside a compiled language of the given size.
      SelectionOutOfRange !Integer !Integer
    | -- | The solver could not decide a guard.
      SolverUnknown
    | -- | The support is not a valid LTA.
      InvalidSupport !AutomatonError
    | -- | LTA pruning could not discharge a constraint.
      InvalidPruning !PruneError
    | -- | LTA similarity could not be computed.
      InvalidSimilarity !SimilarityError
    | -- | LTA minimization could not be applied.
      InvalidMinimization !MinimizeError
    | -- | The compiled ECTA support could not be constructed.
      InvalidECTAGenerator !ECTA.ECTAGenError
    | -- | The compiled rank plan is invalid.
      InvalidRankedGenerator !Tree.RankedError
    | -- | The source has no symbolic observation index.
      RelationalPlanUnavailable
    | -- | A constructor computes its refinement from a Haskell value.
      RelationalComputedRefinement !Symbol
    | -- | The source observations do not decide an equality constraint.
      RelationalEqualityUnsupported !EqConstraints
    | -- | The sparse relational shortcut cannot inspect complete subtrees.
      RelationalSyntacticEqualityUnsupported !Guard
    | -- | A state still carries equality constraints that the selected ranker cannot count.
      ResidualEquality !State !EqConstraints
    | -- | The automaton is recursive; bound it with 'fromLTA' first.
      RecursiveAutomaton
    | -- | Several runs accept the same term at the given state.
      AmbiguousAutomaton !State
    | -- | The generator contains a deferred 'fromLTA' source; call 'compile' first.
      SourceRequiresCompilation
    deriving (Eq, Show)

-- | Explain a failure and the next action in terms of the public API.
explain :: GeneratorError -> String
explain EmptyGenerator =
    "No candidates satisfy the language. Check the source pools, guards, and any fromLTA height bound."
explain (NonPositiveWeight weight) =
    "Choice weights must be positive; received " <> show weight <> "."
explain (NegativeRank rank) =
    "Replay ranks start at zero; received " <> show rank <> "."
explain (SelectionOutOfRange rank count) =
    "Replay rank " <> show rank <> " is outside this compiled language of " <> show count <> " members."
explain SolverUnknown =
    "The solver could not decide a guard. Check the variable declarations and ambient assumptions, or use a solver that can decide these refinements."
explain (InvalidSupport (GuardArityMismatch (Symbol symbol) childrenCount argumentCount)) =
    "Constructor "
        <> show symbol
        <> " has "
        <> show childrenCount
        <> " children, but its named guard takes "
        <> show argumentCount
        <> " arguments. Give the guard one argument per direct child, including unused children."
explain (InvalidSupport err) = "Invalid LTA structure: " <> show err
explain (InvalidPruning err) = "LTA pruning could not discharge a constraint: " <> show err
explain (InvalidSimilarity err) = "Could not compute LTA similarity: " <> show err
explain (InvalidMinimization err) = "Could not apply LTA minimization: " <> show err
explain (InvalidECTAGenerator err) = "Could not construct the compiled ECTA support: " <> show err
explain (InvalidRankedGenerator err) = "Invalid compiled rank plan: " <> show err
explain RelationalPlanUnavailable =
    "This compiled source has no symbolic observation index. Keep its source recipe available, or inspect small inputs explicitly with validOutcomes."
explain (RelationalComputedRefinement (Symbol symbol)) =
    "Constructor "
        <> show symbol
        <> " computes a refinement from a Haskell value. Use refinedNodeByRoots when child labels suffice. Use validOutcomes only for explicit diagnostics on small inputs."
explain (RelationalEqualityUnsupported _) =
    "The source observations do not decide this equality. Use fromLTA for symbolic equality over a bounded automaton, or validOutcomes for explicit diagnostics on small inputs."
explain (RelationalSyntacticEqualityUnsupported _) =
    "The source observations do not decide this syntactic equality. Use fromLTA for ordinary bounded subtree equality. Scoped equality on compound subtrees remains unsupported by the compiler."
explain (ResidualEquality state _) =
    "State "
        <> show state
        <> " still has equality constraints that the selected ranker cannot count. Use compile with fromLTA and an explicit height bound."
explain RecursiveAutomaton =
    "This automaton is recursive. Use fromLTA with an explicit height bound, then compile the generator."
explain (AmbiguousAutomaton state) =
    "Several runs can accept the same term at "
        <> show state
        <> ". Use compile with fromLTA and an explicit height bound to retain one rank per distinct term."
explain SourceRequiresCompilation =
    "This generator contains a deferred fromLTA source. Call compile first, then inspect compiledSupport."

-- | Report a failure of the shared ranked engine as a generator failure.
fromRankedError :: Tree.RankedError -> GeneratorError
fromRankedError Tree.EmptyRanked = EmptyGenerator
fromRankedError (Tree.NonPositiveRankedWeight weight) = NonPositiveWeight weight
fromRankedError (Tree.NegativeRankedRank rank) = NegativeRank rank
fromRankedError (Tree.RankedSelectionOutOfRange rank total) =
    SelectionOutOfRange rank total
fromRankedError err@(Tree.InsufficientRankedWeight _ _) = InvalidRankedGenerator err
