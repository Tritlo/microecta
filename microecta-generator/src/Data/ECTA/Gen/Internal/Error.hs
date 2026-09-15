{- | The failures the generator engine reports.

Every constructor names one way a generator cannot be built, inspected, or
sampled. "Data.ECTA.Gen" re-exports this type and 'explain', because both are
what a caller sees.
-}
module Data.ECTA.Gen.Internal.Error (
    ECTAGenError (..),
    explain,
) where

import Data.List (intercalate)

{- | Failure while constructing, inspecting, or sampling a generator.

The derived 'Show' names the case; 'explain' says what it means and what to
do about it.
-}
data ECTAGenError
    = -- | The language has no members at all.
      EmptyGenerator
    | -- | A weighted alternative carried a weight below one.
      NonPositiveWeight !Integer
    | -- | The generator crosses an opaque region, which has no structure.
      CannotInspectOpaqueGenerator
    | -- | A rank fell outside a language of the given cardinality.
      SelectionOutOfRange !Integer !Integer
    | -- | Ranks start at zero, so a negative rank cannot select a member.
      NegativeRank !Integer
    | {- | Something needing a finite language met a recursive one, which has
      size classes rather than a cardinality.
      -}
      UnboundedGenerator
    | {- | Something needing one ECTA term per member met a recursive
      language, which retains its automaton rather than its members.
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
    | -- | An automaton has free recursive variables, so it is not a language.
      OpenAutomaton
    | {- | An automaton has a node with two edges accepting a common term, so
      its runs outnumber its terms and counting runs would count that term
      twice.
      -}
      AmbiguousAutomaton
    | InvalidImportedAutomaton !String
    | {- | A recursive definition reaches itself without passing through an
      application, so it has no smallest member and no size to count.
      -}
      UnguardedRecursion
    | {- | @upToSize@ or @atomic@ was applied to the recursive occurrence
      inside the body that is defining it, whose size classes are what the
      definition is still computing.
      -}
      BoundedRecursiveOccurrence
    deriving (Eq, Show)

{- | What one failure means, and what to do about it.

Written for the person who hit it: the first line says what the generator
could not do in the vocabulary of the library, and the rest says which
combinator resolves it.
-}
explain :: ECTAGenError -> String
explain (InvalidImportedAutomaton reason) = "The imported automaton is invalid: " <> reason
explain EmptyGenerator =
    guidance
        [ "The language has no members."
        , "Common causes: elements or fromIndexed over an empty list, a"
        , "match, relate, or apply whose keys never agree, or a size bound"
        , "below one."
        ]
explain (NonPositiveWeight weight) =
    guidance
        [ "A weighted alternative carries the weight " <> show weight <> ". Weights are"
        , "relative counts, so every alternative needs a weight of one or more."
        , "Fix: give it a positive weight, or use oneof, which weights every"
        , "alternative equally."
        ]
explain CannotInspectOpaqueGenerator =
    guidance
        [ "The generator crosses an opaque region built with fromGen. An"
        , "opaque region has no ECTA structure, so it has no support, no"
        , "cardinality, and no ranks."
        , "Fix: build that region from elements, fromIndexed, or fromECTA, or"
        , "inspect the transparent parts around it instead."
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
explain (NegativeRank rank) =
    guidance
        [ "Rank " <> show rank <> " is negative, but ranks start at zero."
        , "Fix: use a rank returned by toGenWithRank or forAll, or pass a"
        , "non-negative rank to unrank."
        ]
explain UnboundedGenerator =
    guidance
        [ "This needs a language with finitely many members, but the generator"
        , "is recursive: it has a count per size class rather than a"
        , "cardinality."
        , "Fix: bound it with upToSize first. Grouping and mass inspection"
        , "(groupBy, match, relate, pmf, countBy) additionally need one ECTA"
        , "term per member, which only a language read with fromECTA retains."
        , "If every member has one known key, keyed enters the grouped layer"
        , "without inspecting members."
        ]
explain CannotInspectRecursiveGenerator =
    guidance
        [ "The members of this language carry no ECTA term. A recursive"
        , "generator retains its automaton instead of a term per member, and a"
        , "term per member is what groupBy, match, relate, pmf, and countBy"
        , "read."
        , "Fix: keep the layer that needs terms finite, or read the language"
        , "from an automaton with fromECTA, whose members are terms."
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
        , "fromECTA does not compute that."
        , "Fix: build a constrained language with the generator combinators,"
        , "where apply and match count their joins exactly, or read an"
        , "automaton whose edges are unconstrained."
        ]
explain OpenAutomaton =
    guidance
        [ "The automaton has free recursive variables, so it stands for the"
        , "body of a Mu rather than a language of its own."
        , "Fix: pass the whole recursive node, the one createMu returns, not a"
        , "node taken from inside it."
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

-- | One guidance message, one line per element.
guidance :: [String] -> String
guidance = intercalate "\n"
