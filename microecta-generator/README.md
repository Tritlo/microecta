# microecta-generator

[![Hackage](https://img.shields.io/hackage/v/microecta-generator.svg)](https://hackage.haskell.org/package/microecta-generator)

`microecta-generator` builds indexed generators on
[`microecta`](https://hackage.haskell.org/package/microecta). Transparent
generator regions retain an exact ECTA support, cardinality, and replay rank;
the same package includes QuickCheck integration for sampling, opaque fallbacks,
and structural shrinking.

Add the package to `build-depends` and import the QuickCheck-facing API:

```cabal
build-depends: microecta-generator
```

```haskell
import Data.ECTA.Gen.QuickCheck (ECTAGen)
import Data.ECTA.Gen.QuickCheck qualified as ECTAGen
```

## Generator API

`Data.ECTA.Gen` turns a finite indexed source into an ECTA whose leaves contain
stable indices, not generated values. `Functor` and `Applicative` composition
preserve that symbolic structure, so ordinary `ApplicativeDo` builds ECTA
products. Alongside the ECTA, the generator tracks an exact cardinality and a
rank-to-outcome selector; applicative products multiply their counts rather
than materializing their Cartesian products.

`match` generates two values under a reified key equality: in
`match (authenticatedUser :==: fileOwner) authentication filesystem`, the
`:==:` keeps both projections as data, so the match can group each input by
its own key, encode the shared keys as an actual ECTA equality constraint,
count the matching group products, and unrank directly into the selected
group. `:&&:` conjoins several equalities. `match` accepts arbitrary value
projections, so discovering its groups requires enumerating the input ranks;
conditioning three or more generators is the grouped layer's job (`groupBy`
and `apply`).

`Grouped key a` is the explicit grouping-preserving path for nested or very
large languages. The `key` is the type returned by the classifier and used to
decide which groups may be joined; it is not part of the generated `a`. Matching
key values receive equal internal labels on constrained ECTA paths. `groupBy`
classifies any transparent generator's outcomes (enumerating them once), and
grouped generators support ordinary `fmap` (and `mapWithKey` when the value
should absorb its key). `regroupBy` changes the
classification without enumerating values, `sizes` returns the stored
cardinality of every group, and `atKey` selects one group as an ordinary
conditional generator. An operation of any arity is classified by a `Sig`,
written like a many-sorted operation signature — `:*` between argument keys,
`:->` before the result key: `leftKey :* rightKey :-> resultKey`.
`apply` matches each signature
key with the corresponding argument family, equates their paths in one ECTA
edge holding one equality constraint per argument, and retains the result key
for later equality constraints. The operation family holds functions (`fmap`
a compiling function onto it); the argument families arrive as an `Args`
chain. `frequencies` chooses among grouped generators with relative weights,
group by group, so alternated layers (for example expressions of depth at
most n) stay grouped. `ungroup` returns an ordinary `ECTAGen` with
the same exact distribution. Stable source order and ascending key order give
deterministic replay ranks.

```haskell
functionsBySignature :: Grouped (Sig '[Type, Type] Type) BinaryFunctionInstance
functionsBySignature = ECTAGen.groupBy signature (ECTAGen.elements functionInstances)

signature function =
  argument1Type function :* argument2Type function :-> resultType function

atomsByType :: Grouped Type TypedExpression
atomsByType = ECTAGen.groupBy expressionType (ECTAGen.elements atoms)

applicationGen children =
  ECTAGen.apply (compile <$> functionsBySignature) (children :& children :& ANil)

depthFour = applicationGen depthThree

upToDepth 0 = atomsByType
upToDepth n = ECTAGen.frequencies
  [(1, atomsByType), (3, applicationGen (upToDepth (n - 1)))]
```

Both layers also support qualified do-notation through `Data.ECTA.Gen.Do`,
which `Data.ECTA.Gen.QuickCheck` re-exports. Enable `QualifiedDo` together
with `ApplicativeDo`; statements must stay independent, and the final
statement must use the qualified `ECTAGen.pure`. A grouped block chooses the
operation family first and then one argument per signature component in
order; whatever the arity, it builds exactly one `apply` join:

```haskell
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE QualifiedDo #-}

authentication :: ECTAGen Authentication
authentication = ECTAGen.do
  user <- generatedUser
  method <- ECTAGen.elements [Password, Token]
  ECTAGen.pure (Authentication user method)

applicationGen children = ECTAGen.do
  op <- functionsBySignature
  x <- children
  y <- children
  ECTAGen.pure (compile op x y)
```

Impossible shapes fail at compile time with an explanation: a statement using
an earlier bound value, an unqualified `pure` ending, a missing operation
argument, or a fallible pattern.

Every transparent generator samples compositionally by rank, including exact
non-uniform `frequency` and conditioned joins; sampling never materializes the
final Cartesian product. `cardinality` and `unrank` expose deterministic replay,
while `countBy` reports exact coverage of ranked outcomes. Both `countBy` and
`pmf` enumerate every rank because their projections or complete result values
are not retained groups. The `Grouped` path avoids that work when a caller
supplies the reusable classification structure up front.
`Data.ECTA.Gen.QuickCheck` exposes `toGen`, plus
`toGenWithRank` when the sampled replay rank is needed. `forAll` checks a
property and shrinks to the smallest failing member: candidates first search
every structurally smaller member in size order (`smallerMembers`, capped),
so the reported counterexample is globally size-minimal whenever the search
reaches one - a guarantee ordinary shrinking cannot make. Structural
component shrinking through `shrinkRank` follows as a fallback. Every
candidate is a member of the generated language, and the failing rank is
printed for deterministic replay with `unrank`. `sized` builds one generator per QuickCheck size (shared
across samples), so layered generators can scale with the size parameter.

```haskell
import Data.ECTA.Gen.QuickCheck (ECTAGen)
import Data.ECTA.Gen.QuickCheck qualified as ECTAGen

joined :: ECTAGen (Authentication, Filesystem)
joined =
  ECTAGen.match
    (authenticatedUser :==: fileOwner)
    authentication
    filesystem
```

```haskell
replay :: Either ECTAGenError Authentication
replay = ECTAGen.unrank authentication 42

coverage :: Either ECTAGenError (Map UserId Integer)
coverage = ECTAGen.countBy authenticatedUser authentication
```

## Recursive languages

`mu` builds a generator from its own language, so a language can be
unbounded rather than unrolled layer by layer:

```haskell
tree :: ECTAGen Tree
tree = ECTAGen.mu $ \self ->
    ECTAGen.frequency
        [ (1, Leaf <$> ECTAGen.elements [0 .. 2])
        , (1, Branch <$> self <*> self)
        ]
```

The result stands for the whole language. It has no cardinality; it has
size classes, counted by FEAT-style convolution, where size is the number of
source choices in a member — `countAtSize tree 4` is `Right 405` for the
tree above. Ranks are size-major, so `unrank tree 0` is the smallest member
and every rank replays as usual, and the ECTA support is a `Mu` node: one
finite automaton for infinitely many terms.

`upToSize n` bounds the language back to an ordinary finite generator over
the members of size at most `n`, and `toGen` and `forAll` apply it from
QuickCheck's size parameter, so a recursive generator samples uniformly from
the members of at most the current size. Bounding preserves ranks — the
members of size at most `n` hold the same ranks under every bound — so a
counterexample found at one size replays at any other, and `forAll` shrinks
by walking whole size classes below the failing member.

Two rules apply inside the knot. The recursion must be guarded: every
occurrence of the argument sits under at least one `<*>`, or the language
has no smallest member and counting it diverges. And a recursive language is
uniform over each size class, so `frequency` alternatives around a recursive
occurrence must carry equal weights — the size bound, not the weights,
controls how large members get. Unequal weights are rejected rather than
ignored. Inspection that needs one ECTA term per member (`groupBy`, `match`,
`pmf`, `countBy`) is not available on a recursive language; bound it first,
or keep that layer finite.

`muGrouped` does the same for the grouped layer, which is where recursion
and equality constraints meet in one cycle:

```haskell
expressions :: Grouped Type TypedExpression
expressions = ECTAGen.muGrouped $ \self ->
    ECTAGen.frequencies
        [ (1, atomsByType)
        , (1, applicationGen self)
        ]

anyExpression = ECTAGen.ungroup expressions
intExpression = ECTAGen.atKey TInt expressions
```

Which keys the family has is part of the fixpoint, so it is solved first —
from the empty family upward, adding the result keys of operations whose
argument keys are already present — and the languages are tied over that
settled set. All the keys share one `Mu` node whose edges carry their key as
a first child; an occurrence at one key is that node under an edge holding
the key's label, with an equality constraint tying the two. A recursive
family is therefore one recursive automaton whose cycle carries the keyed
joins' equality constraints, which is the shape only an ECTA can hold.

For the language above that automaton has 139 nodes and 40 equality
constraints, and unfolding it twice accepts exactly the 106 expressions the
counting layer reports for size at most three — the same 106 a hand-unrolled
depth-one generator produces. `ungroup` and `atKey` are the exits back to an
ordinary recursive generator, so bounding, sampling, replay, and shrinking
all work as above. `sizes` has no cardinality to report for a recursive
family; use `countAtSize` on `atKey`.

`fromECTA` goes the other way: it reads an existing automaton as a generator
of the terms it accepts, counting them by size — the number of term nodes —
with the automaton itself as the support.

```haskell
types :: Node
types = createMu $ \recursive -> Node
    [ Edge "baseType" []
    , Edge "->" [recursive, recursive]
    , Edge "Maybe" [recursive]
    ]

typeGen :: ECTAGen Term
typeGen = ECTAGen.fromECTA types
```

`countAtSize typeGen` reports 1, 1, 2, 4, 9 for sizes one to five, `unrank`
walks the terms in size order, and sampling draws uniformly from the terms
of at most the current size. Because the generated values *are* the accepted
terms, bounding one of these keeps full inspection: `pmf`, `countBy`, and
`groupBy` all work on `upToSize n (fromECTA node)`.

Equality constraints are not counted. They correlate an edge's children, so
the edge's count is the size of an intersection rather than a product of the
children's counts; an automaton carrying them is rejected with
`CannotCountConstrainedEdges` rather than miscounted.

`fromIndexed` is the transparent boundary for a FEAT-style finite enumeration:
it needs only a cardinality and a stable function from an integer index to a
value. `elements` is the corresponding list convenience function.

`fromGen` embeds an ordinary `QuickCheck.Gen` as an explicitly opaque region.
Opaque regions still compose and sample, but cannot be inspected with `pmf`;
joining through one falls back to QuickCheck rejection. Opaque regions also
have no replay rank. There is deliberately no `Monad` or `Selective` instance.
This keeps inspectable applicative regions inside ECTA and makes the loss of
structure explicit.

## Module map

- `Data.ECTA.Gen` is the backend-polymorphic indexed generator core.
- `Data.ECTA.Gen.Sig` defines the signature (`Sig`) and condition (`On`)
  syntax; `Data.ECTA.Gen` re-exports both.
- `Data.ECTA.Gen.Do` provides the qualified do-notation operators.
- `Data.ECTA.Gen.QuickCheck` provides the ordinary QuickCheck-facing API,
  including `fromGen`, `toGen`, `forAll`, and `sized`.
- `Data.ECTA.Gen.Internal`, `Data.ECTA.Gen.Internal.Automaton`,
  `Data.ECTA.Gen.Internal.Decoder`, `Data.ECTA.Gen.Internal.Shrink`, and
  `Data.ECTA.Gen.Internal.Size` implement static languages, joins, reading
  an automaton, compiled rank decoding, structural shrinking, and
  size-stratified counting. They are not exposed.

## Dependency surface

The package depends directly on `microecta`, `QuickCheck`, `containers`,
and `text`. The dependency direction is one-way: `microecta` does not depend
on this package or on QuickCheck.

## Build

From the repository root:

```sh
cabal build microecta-generator -j1
cabal test microecta-generator:unit-tests -j1
```
