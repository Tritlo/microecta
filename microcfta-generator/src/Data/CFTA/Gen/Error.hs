{- | The failures every generator layer reports.

Each constructor names one way a generator cannot be built, inspected,
compiled, or sampled. The derived 'Show' names the case; 'explain' says what
it means and which combinator resolves it. The three facades re-export this
type, so a caller sees one vocabulary.
-}
module Data.CFTA.Gen.Error (
    GenError (..),
    explain,
    orFail,
    fromRankedError,
) where

import Data.List (intercalate)

import Data.CFTA.Equality.Constraint (EqConstraints)
import Data.CFTA.Index (Cardinality, Rank, Weight)
import qualified Data.CFTA.Ranked as Ranked
import Data.CFTA.Refinement (
    AutomatonError (GuardArityMismatch),
    Guard,
    MinimizeError,
    PruneError,
    SimilarityError,
    Symbol (Symbol),
 )
import Data.CFTA.Refinement.Lattice (LatticeError (..))

-- | Failure while constructing, inspecting, compiling, or sampling a generator.
data GenError
    = -- | The language has no members at all.
      EmptyGenerator
    | -- | A weighted alternative carried a weight below one.
      NonPositiveWeight !Weight
    | -- | Ranks start at zero, so a negative rank cannot select a member.
      NegativeRank !Rank
    | -- | A rank fell outside a language of the given cardinality.
      SelectionOutOfRange !Rank !Cardinality
    | -- | The generator crosses an opaque region, which has no structure.
      CannotInspectOpaqueGenerator
    | {- | An operation that needs a finite language was applied to a recursive
      one, which has size classes rather than a cardinality.
      -}
      UnboundedGenerator
    | {- | An operation that needs one term per member was applied to a
      recursive language that keeps no term for its members.
      -}
      CannotInspectRecursiveGenerator
    | {- | Alternatives that choose recursive structure carried unequal
      weights. Only finite choices closed by @atomic@ retain weights inside
      recursion. A weighted choice between finite alternatives without @atomic@
      is not an error there, but its members are counted, and its weights are
      lost.
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
    | {- | A recursive definition reaches itself without passing through a
      pay or a product whose other side has no member of size zero, so
      counting a size reads that same size. Or it reaches itself without
      passing through a product or a constructor, so its members add no term
      node and one term could have infinitely many ranks.
      -}
      UnguardedRecursion
    | {- | @upToSize@ or @atomic@ was applied inside a recursive body to a
      language that reaches the occurrence of a recursion still being defined,
      such as the occurrence itself or a nested recursion that uses it. The
      size classes of that language are what the definition is still
      computing.
      -}
      BoundedRecursiveOccurrence
    | -- | The support is not a valid automaton.
      InvalidSupport !AutomatonError
    | {- | The codec of a datatype rejects a term of its own grammar that
      contains the named constructor or atomic literal.
      -}
      UndecodableConstructor !String
    | -- | The compiled rank plan is invalid.
      InvalidRankedGenerator !Ranked.RankedError
    | -- | The solver could not decide a guard.
      SolverUnknown
    | -- | A solver query reached the time limit, in milliseconds.
      SolverTimeLimit !Int
    | -- | LTA pruning could not discharge a constraint.
      InvalidPruning !PruneError
    | -- | LTA similarity could not be computed.
      InvalidSimilarity !SimilarityError
    | -- | LTA minimization could not be applied.
      InvalidMinimization !MinimizeError
    | -- | A constructor computes its label from its children's roots, and a child has none.
      MissingRootObservation
    | -- | The source observations do not decide an equality constraint.
      RelationalEqualityUnsupported !EqConstraints
    | -- | The sparse relational shortcut cannot inspect complete subtrees.
      RelationalSyntacticEqualityUnsupported !Guard
    | -- | A guard remained after pruning that the symbolic ranker cannot count.
      ResidualGuard !Guard
    | -- | The generator contains a deferred automaton source; call @compile@ first.
      SourceRequiresCompilation
    | {- | A condition from @satisfying@ was applied to a generator that does not
      end in a constructor, such as a product, @pure@, or a recursive language.
      -}
      ConditionNeedsConstructor
    | -- | The conditions of an integer leaf do not give a countable set of integers.
      UncountableIntegers !LatticeError
    | {- | A guard reads an integer leaf, or a measure of integer leaves, in a
      form that compile cannot count.
      -}
      IntegerLeafRead !(Maybe Guard)
    | -- | The measure of the constructor names a child that has no measure: a refinement that does not fix one integer.
      InexactMeasure !Symbol
    | {- | A guard reads the children of a constructor, and one child gives a
      number of terms other than one, as a choice of products or a source
      without symbols does. Or an equality reads a node whose members are
      leaves and non-leaves.
      -}
      ChildNotOneTerm
    | -- | A term to rank is not a member of the generator's language.
      TermNotInLanguage
    deriving (Eq, Show)

{- | Return the value, or fail with the 'explain' text of the error.

Use it where a generator is known to be valid, such as in @main@ or a test:

>>> orFail (Left EmptyGenerator) :: Maybe ()
Nothing
-}
orFail :: (MonadFail m) => Either GenError a -> m a
orFail = either (fail . explain) pure

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
        , "satisfies, a size bound below one, or a depth bound below zero."
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
        , "fromAutomatonUpToDepth for a recursive automaton. The bounded"
        , "language keeps one term per member, so grouping and mass inspection"
        , "(groupOn, match, relate, pmf, countOn) work on it. termAt and rankOf"
        , "work without a bound. If every member has one known key, keyed enters"
        , "the grouped layer without inspecting members."
        ]
explain CannotInspectRecursiveGenerator =
    guidance
        [ "The members of this recursive language carry no term, and a term per"
        , "member is what termAt, rankOf, groupOn, match, relate, pmf, and"
        , "countOn read. The combinators of this package keep a term for every"
        , "member of a recursive language, so the language was built another way."
        , "Fix: build the recursive language with recur, recurGrouped, or"
        , "fromAutomaton."
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
        , "Fix: build the operations with elements and groupOn, and let the"
        , "recursion go through the arguments."
        ]
-- A cyclic automaton is counted by size through a fixed point of size
-- indexes. An equality between the children of an edge makes the count of the
-- edge the size of an intersection at every size, and the fixed point has no
-- such operation: it would need the intersection of recursive languages,
-- counted by size, inside the fixed point. The bounded form counts equalities
-- symbolically instead.
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
        [ "The recursive language reaches itself without passing through a"
        , "constructor or a product that makes its members larger, so its size"
        , "classes cannot be counted, or its terms do not grow."
        , "Fix: put every occurrence of the argument under node, as in"
        , "node \"branch\" (Branch <$> self <*> self), or under a product whose"
        , "other side has no member of size zero, such as Cons <$> elements xs"
        , "<*> self, or under pay around a product. An alternative that is the"
        , "argument itself, such as oneof [leaf, self] or oneof [leaf, pay self],"
        , "is the shape to look for."
        ]
explain BoundedRecursiveOccurrence =
    guidance
        [ "upToSize or atomic was applied inside a recur or recurGrouped body to a"
        , "language that reaches the occurrence of that definition, such as the"
        , "occurrence itself or a nested recur that uses it. The bound would need"
        , "the size classes the definition is still computing, and an atom over"
        , "them would have a cardinality depending on itself."
        , "Fix: bound or close the language outside the knot, as in"
        , "upToSize n (recur ...), and keep only finite atomic choices inside the"
        , "body."
        ]
explain (InvalidSupport (GuardArityMismatch (Symbol symbol) childrenCount argumentCount)) =
    guidance
        [ "Constructor " <> show symbol <> " has " <> show childrenCount <> " children, but its"
        , "named guard, contract, or measure takes " <> show argumentCount <> " arguments."
        , "Fix: give the guard, the contract, or the measure one argument per direct"
        , "child, including unused children."
        ]
explain (InvalidSupport err) =
    guidance
        [ "The support is not a valid automaton: " <> show err <> "."
        , "Fix: pass a closed node, keep one arity per constructor symbol, and"
        , "keep guard positions off recursive nodes."
        ]
explain (UndecodableConstructor name) =
    guidance
        [ "fromDatatype cannot decode the terms of this datatype: the codec rejects"
        , "a term of its own grammar that contains the constructor or literal"
        , show name <> ". An atomic literal is the text that show gives, and the"
        , "codec reads that text back with read."
        , "Fix: give the atomic type a Show instance whose text Read accepts, or"
        , "give the type a HasFTA instance whose decodeTerm accepts every term"
        , "that encodeTerm gives."
        ]
explain (InvalidRankedGenerator err) = "Invalid compiled rank plan: " <> show err
explain SolverUnknown =
    guidance
        [ "The solver could not decide a guard."
        , "Fix: check the variable declarations and ambient assumptions, or use a"
        , "solver that can decide these refinements."
        ]
explain (SolverTimeLimit milliseconds) =
    guidance
        [ "A solver query reached the time limit of " <> show milliseconds <> " milliseconds before"
        , "the solver decided it. The query may be decidable with more time."
        , "Fix: compile again with compileWith and a solver from withZ3Timeout with a"
        , "higher limit, or simplify the refinements, for example remove non-linear"
        , "arithmetic."
        ]
explain (InvalidPruning err) = "LTA pruning could not discharge a constraint: " <> show err
explain (InvalidSimilarity err) = "Could not compute LTA similarity: " <> show err
explain (InvalidMinimization err) = "Could not apply LTA minimization: " <> show err
explain MissingRootObservation =
    guidance
        [ "A constructor computes its refinement from the roots of its children,"
        , "but a child has no observable root: it is a source without symbols."
        , "Fix: give the child a symbol with pool, leaf, or a constructor."
        ]
explain (RelationalEqualityUnsupported _) =
    guidance
        [ "The source observations do not decide this equality."
        , "Fix: use fromAutomatonUpToDepth for symbolic equality over a bounded"
        , "automaton, or validOutcomes for explicit diagnostics on small inputs."
        ]
-- The compiler groups the children by what the parent observes: root labels
-- and the requested paths. Two compound subtrees with equal observations can
-- differ below them. An equality between them needs the whole subtrees in the
-- observation, which enumerates the child languages, or a symbolic count of
-- equal pairs, as the equality layer makes with the intersection of languages.
-- The compiler has neither.
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
        , "unsupported by the compiler. validOutcomes reads an import through the"
        , "same pruning, so it reports the same error."
        , "Fix: write the guard of the imported automaton without scoped equality"
        , "on compound subtrees."
        ]
explain ConditionNeedsConstructor =
    guidance
        [ "A condition applies to the root constructor of each term, and this"
        , "generator does not end in one: it is a product, pure, a recursive"
        , "language, an opaque source, or a source without symbols, such as"
        , "fromIndexed, freeze, a join, upToSize, or a compiled generator."
        , "Fix: put the condition on a pool, a leaf, or a node, or state it as the"
        , "contract of the enclosing guarded node."
        ]
explain ChildNotOneTerm =
    guidance
        [ "A guard reads the children of a constructor by position, and one child"
        , "does not give one term for each member: a choice of products gives"
        , "several terms, and a choice of pure values or a source without symbols,"
        , "such as fromIndexed, freeze, or samplePool, gives none. The terms take"
        , "that many positions, so the guard would read the wrong children. Or"
        , "isSameTermAs reads a node whose members are leaves and non-leaves, such"
        , "as a node over a choice of pure values and constructors."
        , "Fix: put the choice around the whole constructor, or give each"
        , "alternative or source a node of its own."
        ]
explain SourceRequiresCompilation =
    guidance
        [ "This generator has a guard, an integer leaf from every, or an imported"
        , "automaton that needs compile, or such a part sits inside a join, a"
        , "recursion, or a grouping that compile cannot fold."
        , "Fix: call compile on the guarded part first, then inspect or combine it."
        ]
explain (UncountableIntegers err) =
    guidance $
        "The conditions of an integer leaf, or a contract over integer leaves, do"
            : "not give a set of integers that compile can count."
            : case err of
                UnboundedVariable name ->
                    [ "No condition bounds " <> show name <> " in one direction. Inside a"
                    , "choice, the conditions of each integer leaf must bound it, because the"
                    , "choice weighs its alternatives by their values."
                    , "Fix: bound it, as in every @Integer `satisfying` (\\v -> 0 .<= v .&& v .< 100)."
                    , "The type application needs the TypeApplications extension."
                    ]
                NonLinearTerm term ->
                    [ "The term " <> show term <> " is not linear: it multiplies two"
                    , "values, divides, applies a function, or chooses a term by a"
                    , "condition, as abs and signum do."
                    , "Fix: state the condition with sums, differences, and constant factors,"
                    , "as in -3 .<= v .&& v .<= 3 for abs v .<= 3."
                    ]
                UnsupportedFormula formula ->
                    [ "The formula " <> show formula <> " uses a form other than the"
                    , "comparisons and the connectives."
                    , "Fix: state the condition with .==, ./=, .<, .<=, .>, .>=, .&&, .||, and lnot."
                    ]
                UnknownName name ->
                    [ "The formula names " <> show name <> ", which is not a value that"
                    , "compile counts. A name from compileAssuming is a fact for the solver,"
                    , "and compile does not count it."
                    , "Fix: state conditions on integer leaves, and contracts over them, with"
                    , "the values and constants only."
                    ]
                NonUnitCoefficient name ->
                    [ "A bound has a coefficient other than one or minus one on " <> show name <> "."
                    , "The counter sums the values out from the last to the first. When it sums"
                    , "out a value, every bound on that value must have the coefficient one or"
                    , "minus one on it. This includes the bounds that summing out a later value"
                    , "creates, so a factor against a later value can also fail."
                    , "Fix: draw the value with the factor first, state the bound without the"
                    , "factor, or use elements."
                    ]
explain (IntegerLeafRead reader) =
    guidance $
        [ "A constructor reads one of its integer children in a form that compile"
        , "cannot count."
        ]
            <> maybe [] (\guard -> ["The guard is " <> show guard <> "."]) reader
            <> [ "Compile counts an integer child through its own conditions, the"
               , "contract of guarded or measured, and the measure of measured. Each"
               , "other child that they name must have one exact integer refinement, as"
               , "elements gives, or be an integer leaf or a constructor with a measure."
               , "An equality, a guard that reads below the root of such a child, and"
               , "the function of refinedNodeByRoots, which reads exact labels, cannot"
               , "read its integers."
               , "Fix: state the relation as the contract of the constructor whose"
               , "children it relates, or build the child with measured to give it a"
               , "measure."
               ]
explain (InexactMeasure (Symbol symbol)) =
    guidance
        [ "The measure of the constructor " <> show symbol <> " names a child that has"
        , "no measure: its refinement does not fix one integer, so the measure has"
        , "no one value."
        , "Fix: draw that child from elements, every, or a constructor built with"
        , "measured, or leave it out of the measure."
        ]
explain TermNotInLanguage =
    guidance
        [ "The term is not a member of the generator's language, so it has no rank."
        , "rankOf reads the terms that termAt returns, with the private labels of"
        , "the engine. rankOfTerm reads the terms that an imported automaton"
        , "accepts, and rankOfValue encodes a datatype value with its codec."
        , "Fix: rank a term that the generator produced."
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
