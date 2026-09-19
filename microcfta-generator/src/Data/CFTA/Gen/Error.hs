{- | The failures every generator layer reports.

Each constructor names one way a generator cannot be built, inspected,
compiled, or sampled. The derived 'Show' names the case; 'explain' says what
it means and which combinator resolves it. The three facades re-export this
type, so a caller sees one vocabulary.
-}
module Data.CFTA.Gen.Error (
    GenError (..),
    explain,
    fromRankedError,
) where

import Data.List (intercalate)

import Data.CFTA.Equality.Constraint (EqConstraints)
import qualified Data.CFTA.Ranked as Ranked
import Data.CFTA.Refinement (
    AutomatonError (GuardArityMismatch),
    Guard,
    MinimizeError,
    PruneError,
    SimilarityError,
    Symbol (Symbol),
 )

-- | Failure while constructing, inspecting, compiling, or sampling a generator.
data GenError
    = -- | The language has no members at all.
      EmptyGenerator
    | -- | A weighted alternative carried a weight below one.
      NonPositiveWeight !Integer
    | -- | Ranks start at zero, so a negative rank cannot select a member.
      NegativeRank !Integer
    | -- | A rank fell outside a language of the given cardinality.
      SelectionOutOfRange !Integer !Integer
    | -- | The generator crosses an opaque region, which has no structure.
      CannotInspectOpaqueGenerator
    | {- | Something needing a finite language met a recursive one, which has
      size classes rather than a cardinality.
      -}
      UnboundedGenerator
    | {- | Something needing one term per member met a recursive language,
      which retains its automaton rather than its members.
      -}
      CannotInspectRecursiveGenerator
    | {- | Alternatives that choose recursive structure carried unequal
      weights. Only finite choices closed by @atomic@ retain weights inside
      recursion.
      -}
      WeightedRecursiveAlternatives
    | -- | The operation family of an application is recursive.
      RecursiveOperationFamily
    | {- | An automaton's edges carry equality constraints, which correlate
      their children: the edge's count is an intersection, not a product.
      -}
      CannotCountConstrainedEdges
    | {- | An automaton has a node with two edges accepting a common term, so
      its runs outnumber its terms and counting runs would count that term
      twice.
      -}
      AmbiguousAutomaton
    | {- | A recursive definition reaches itself without passing through an
      application, so it has no smallest member and no size to count.
      -}
      UnguardedRecursion
    | {- | @upToSize@ or @atomic@ was applied to the recursive occurrence
      inside the body that is defining it, whose size classes are what the
      definition is still computing.
      -}
      BoundedRecursiveOccurrence
    | -- | The support is not a valid automaton.
      InvalidSupport !AutomatonError
    | -- | The compiled rank plan is invalid.
      InvalidRankedGenerator !Ranked.RankedError
    | -- | The solver could not decide a guard.
      SolverUnknown
    | -- | LTA pruning could not discharge a constraint.
      InvalidPruning !PruneError
    | -- | LTA similarity could not be computed.
      InvalidSimilarity !SimilarityError
    | -- | LTA minimization could not be applied.
      InvalidMinimization !MinimizeError
    | -- | The source has no symbolic observation index.
      RelationalPlanUnavailable
    | -- | A constructor computes its refinement from a Haskell value.
      RelationalComputedRefinement !Symbol
    | -- | The source observations do not decide an equality constraint.
      RelationalEqualityUnsupported !EqConstraints
    | -- | The sparse relational shortcut cannot inspect complete subtrees.
      RelationalSyntacticEqualityUnsupported !Guard
    | -- | A guard remained after pruning that the symbolic ranker cannot count.
      ResidualGuard !Guard
    | -- | The generator contains a deferred automaton source; call @compile@ first.
      SourceRequiresCompilation
    deriving (Eq, Show)

{- | What one failure means, and what to do about it.

Written for the person who hit it: the first line says what the generator
could not do in the vocabulary of the library, and the rest says which
combinator resolves it.
-}
explain :: GenError -> String
explain EmptyGenerator =
    guidance
        [ "The language has no members."
        , "Common causes: elements, fromIndexed, or pool over an empty list, a"
        , "match, relate, or apply whose keys never agree, a guard no candidate"
        , "satisfies, or a size or depth bound below one."
        ]
explain (NonPositiveWeight weight) =
    guidance
        [ "A weighted alternative carries the weight " <> show weight <> ". Weights are"
        , "relative counts, so every alternative needs a weight of one or more."
        , "Fix: give it a positive weight, or use oneof, which weights every"
        , "alternative equally."
        ]
explain (NegativeRank rank) =
    guidance
        [ "Rank " <> show rank <> " is negative, but ranks start at zero."
        , "Fix: use a rank returned by toGenWithRank or forAll, or pass a"
        , "non-negative rank to unrank."
        ]
explain (SelectionOutOfRange rank total)
    | total <= 0 =
        guidance
            [ "Rank " <> show rank <> " was asked of a language with no members."
            , "Fix: see EmptyGenerator for what leaves a language empty."
            ]
    | otherwise =
        guidance
            [ "Rank " <> show rank <> " is outside the language, which holds " <> show total
            , "members ranked 0 to " <> show (total - 1) <> "."
            , "Fix: a rank comes from unrank, toGenWithRank, or a forAll"
            , "counterexample, and replays only into the language it came from."
            , "For a recursive language that means the same size bound too:"
            , "countAtSize reports one size class, and upToSize fixes the"
            , "language a rank has to fall inside."
            ]
explain CannotInspectOpaqueGenerator =
    guidance
        [ "The generator crosses an opaque region built with fromGen. An"
        , "opaque region has no automaton structure, so it has no support, no"
        , "cardinality, and no ranks."
        , "Fix: build that region from elements, fromIndexed, or fromAutomaton,"
        , "or inspect the transparent parts around it instead."
        ]
explain UnboundedGenerator =
    guidance
        [ "This needs a language with finitely many members, but the generator"
        , "is recursive: it has a count per size class rather than a"
        , "cardinality."
        , "Fix: bound it first, with upToSize for a recursive generator or"
        , "fromAutomatonUpToDepth for a recursive automaton. Grouping and mass"
        , "inspection (groupBy, match, relate, pmf, countBy) additionally need"
        , "one term per member, which only a language read with fromAutomaton"
        , "retains. If every member has one known key, keyed enters the grouped"
        , "layer without inspecting members."
        ]
explain CannotInspectRecursiveGenerator =
    guidance
        [ "The members of this language carry no term. A recursive generator"
        , "retains its automaton instead of a term per member, and a term per"
        , "member is what groupBy, match, relate, pmf, and countBy read."
        , "Fix: keep the layer that needs terms finite, or read the language"
        , "from an automaton with fromAutomaton, whose members are terms."
        , "If every member has one known key, use keyed instead of groupBy."
        ]
explain WeightedRecursiveAlternatives =
    guidance
        [ "Alternatives that choose recursive structure carry different weights."
        , "Recursive structure is counted by size, so those weights cannot"
        , "also decide how deep the language recurses."
        , "Fix: use oneof, or oneofGrouped in a grouped family, and control"
        , "size with the bound. Put weighted finite choices behind atomic when"
        , "one complete choice should retain its distribution inside recursion."
        ]
explain RecursiveOperationFamily =
    guidance
        [ "The operation family passed to apply is recursive. Which components"
        , "an application has is decided by the operation signatures, so that"
        , "family has to be finite; only the argument families may recurse."
        , "Fix: build the operations with elements and groupBy, and let the"
        , "recursion go through the arguments."
        ]
explain CannotCountConstrainedEdges =
    guidance
        [ "An edge of this automaton carries equality constraints, which"
        , "correlate its children: the edge's count is the size of an"
        , "intersection rather than the product of its children's counts, and"
        , "fromAutomaton does not compute that."
        , "Fix: build a constrained language with the generator combinators,"
        , "where apply and match count their joins exactly, bound the automaton"
        , "with fromAutomatonUpToDepth, which counts symbolically, or read an"
        , "automaton whose edges are unconstrained."
        ]
explain AmbiguousAutomaton =
    guidance
        [ "The automaton has a node with two edges that accept a common term, so"
        , "it has more accepting runs than terms, and counting runs would count"
        , "that term once per run."
        , "Fix: make the alternatives disjoint, by splitting the shared part into"
        , "its own edge or intersecting it away. withoutRedundantEdges only drops"
        , "an alternative another one wholly subsumes, so it does not settle a"
        , "partial overlap."
        ]
explain UnguardedRecursion =
    guidance
        [ "The recursive language reaches itself without passing through an"
        , "application, so its members never get smaller and no size class can"
        , "be counted."
        , "Fix: put every occurrence of the argument under <*>, as in"
        , "Branch <$> self <*> self, or under apply in a grouped family. An"
        , "alternative that is the argument itself, such as oneof [leaf, self],"
        , "is the shape to look for."
        ]
explain BoundedRecursiveOccurrence =
    guidance
        [ "upToSize or atomic was applied to the recursive occurrence inside the"
        , "recur or recurGrouped body that defines it. The bound would need the"
        , "size classes the definition is still computing, and an atom over them"
        , "would have a cardinality depending on itself."
        , "Fix: bound or close the language outside the knot, as in"
        , "upToSize n (recur ...), and keep only finite atomic choices inside the"
        , "body."
        ]
explain (InvalidSupport (GuardArityMismatch (Symbol symbol) childrenCount argumentCount)) =
    guidance
        [ "Constructor " <> show symbol <> " has " <> show childrenCount <> " children, but its"
        , "named guard takes " <> show argumentCount <> " arguments."
        , "Fix: give the guard one argument per direct child, including unused"
        , "children."
        ]
explain (InvalidSupport err) =
    guidance
        [ "The support is not a valid automaton: " <> show err <> "."
        , "Fix: pass a closed node, keep one arity per constructor symbol, and"
        , "keep guard positions off recursive nodes."
        ]
explain (InvalidRankedGenerator err) = "Invalid compiled rank plan: " <> show err
explain SolverUnknown =
    guidance
        [ "The solver could not decide a guard."
        , "Fix: check the variable declarations and ambient assumptions, or use a"
        , "solver that can decide these refinements."
        ]
explain (InvalidPruning err) = "LTA pruning could not discharge a constraint: " <> show err
explain (InvalidSimilarity err) = "Could not compute LTA similarity: " <> show err
explain (InvalidMinimization err) = "Could not apply LTA minimization: " <> show err
explain RelationalPlanUnavailable =
    guidance
        [ "This compiled source has no symbolic observation index."
        , "Fix: keep its source recipe available, or inspect small inputs"
        , "explicitly with validOutcomes."
        ]
explain (RelationalComputedRefinement (Symbol symbol)) =
    guidance
        [ "Constructor " <> show symbol <> " computes a refinement from a Haskell value."
        , "Fix: use refinedNodeByRoots when child labels suffice, and"
        , "validOutcomes only for explicit diagnostics on small inputs."
        ]
explain (RelationalEqualityUnsupported _) =
    guidance
        [ "The source observations do not decide this equality."
        , "Fix: use fromAutomatonUpToDepth for symbolic equality over a bounded"
        , "automaton, or validOutcomes for explicit diagnostics on small inputs."
        ]
explain (RelationalSyntacticEqualityUnsupported _) =
    guidance
        [ "The source observations do not decide this syntactic equality."
        , "Fix: use fromAutomatonUpToDepth for ordinary bounded subtree equality."
        , "Scoped equality on compound subtrees stays unsupported by the compiler."
        ]
explain (ResidualGuard guard) =
    guidance
        [ "The guard " <> show guard <> " remained after pruning, and the symbolic"
        , "ranker cannot count it. Scoped equality on compound subtrees stays"
        , "unsupported by the compiler."
        , "Fix: use validOutcomes for explicit diagnostics on small inputs."
        ]
explain SourceRequiresCompilation =
    guidance
        [ "This generator contains a deferred automaton source."
        , "Fix: call compile first, then inspect compiledSupport."
        ]

-- | Report a failure of the shared ranked engine as a generator failure.
fromRankedError :: Ranked.RankedError -> GenError
fromRankedError Ranked.EmptyRanked = EmptyGenerator
fromRankedError (Ranked.NonPositiveRankedWeight weight) = NonPositiveWeight weight
fromRankedError (Ranked.NegativeRankedRank rank) = NegativeRank rank
fromRankedError (Ranked.RankedSelectionOutOfRange rank total) = SelectionOutOfRange rank total
fromRankedError err@(Ranked.InsufficientRankedWeight _ _) = InvalidRankedGenerator err

-- | One guidance message, one line per element.
guidance :: [String] -> String
guidance = intercalate "\n"
