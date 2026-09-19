# microcfta-generator

Ranked generation, random sampling, replay, and shrinking for the automata of
[`microcfta`](../microcfta/README.md), with QuickCheck integration. There is
one ranked layer and three generators, one per constraint theory:

| Module | Purpose |
| --- | --- |
| `Data.CFTA.Ranked` | Finite ranks, weighted sampling, replay, and structural shrinking, independent of automata. |
| `Data.CFTA.Ranked.QuickCheck` | QuickCheck sampling and properties over a ranked language. |
| `Data.CFTA.Gen` | Ordinary automaton compilation and constructor-based source recipes. |
| `Data.CFTA.Gen.QuickCheck` | Ordinary sampling, properties, and qualified do-notation. |
| `Data.CFTA.Gen.Error` | The one failure vocabulary of every layer, and `explain`. |
| `Data.CFTA.Gen.Equality` | Equality-constrained sources, equality and relational joins, retained key groups, and recursive generation. |
| `Data.CFTA.Gen.Equality.QuickCheck` | Re-exports `Data.CFTA.Gen.Equality` and its do-notation, and adds `pool`, `freeze`, `toGen`, `forAll`, and `sized`. |
| `Data.CFTA.Gen.Refinement` | Refinement-constrained sources compiled once with a solver into pure sampling, replay, and shrinking. |
| `Data.CFTA.Gen.Refinement.QuickCheck` | The QuickCheck-facing refinement API. |
| `Data.CFTA.Ranked.Internal.*`, `Data.CFTA.Gen.Internal.*`, `Data.CFTA.Gen.Equality.Internal.Symbolic` | The shared decoder, sampler, size, shrink, and symbolic-count implementation; exposed for integration, not covered by the PVP contract. |

The generator APIs close qualified-do child blocks consistently with
`FTA.node`, `ECTA.node`, and `LTA.node`; see
[`docs/automata-syntax.md`](../docs/automata-syntax.md) for the side-by-side
forms. The core package does not depend on this package or on QuickCheck.

## Ordinary generators

Run the complete example from the workspace root:

```sh
nix-shell --run 'cabal run cfta-pairs'
```

[`examples/FinitePairs.hs`](examples/FinitePairs.hs) derives the pair datatype with the finite `Int`
domain `[0, 1]`.
It checks all replay ranks and samples the accepted pairs with QuickCheck.
It also constructs the same language with `Common.Node String ()`, converts
the shared graph with `Common.toFTA`, and checks the imported generator.

`FTA.node "pair"` closes an applicative child block. Each binding supplies one
direct child. Enable `ApplicativeDo` and `QualifiedDo`, and finish the block
with `FTA.pure`. Child generators must be independent.

`fromAutomaton` compiles an acyclic interned automaton. Its ranks identify
accepting derivations. An ambiguous automaton can assign several ranks to the
same term. Alternatives have equal branch weights; this does not guarantee
equal probability for every complete term. Use `Data.CFTA.Interned.fromFTA`
first when the source is an explicit-state automaton; the import is total and
retains shared states.

`fromAutomatonUpToDepth` also accepts recursive automata. A leaf has depth zero.
The compiler bounds the shared graph and preserves transition and child order.
`fromAutomatonUpToSize` bounds the total number of tree nodes. Its ranks are ordered
by size, and it samples uniformly over those ranks. Both imports count accepting
runs. An empty bounded language returns `EmptyGenerator`.

Recursive size indexing and finite automaton rank shrinking belong to
`Data.CFTA.Gen.Internal.*`. ECTA retains its constraint and ambiguity
checks before using the shared index. LTA uses the ordinary shrinker only
after it has removed transition constraints.

`Data.CFTA.Ranked` is independent of automaton representation. `Indexed` describes
a finite rank domain. `WeightedIndexed` separates replay ranks from sampling
tickets. Its callbacks must obey the documented rank and weight invariants.
Counting and replay do not require enumerating the entire source.

The `Data.CFTA.Ranked.Internal.*` and `Data.CFTA.Gen.Internal.*` modules are
the integration interface between the three generators. Their exports are not
covered by the PVP contract. Ordinary applications should use the public
construction modules.

`fromDatatypeUpToDepth` and `fromDatatypeUpToSize` combine a derived grammar
with its retained decoder. They return ordinary `FTAGen` values. Replay keeps
the constructor term and the typed value at the same rank. Decoding a selected
value does not enumerate any other member. Depth counts constructors, including
primitive fields: a `Leaf Bool` term has depth one and two tree nodes.

### Generate a language up to a depth bound

This complete example derives a grammar with `microcfta`, then generates every
expression with literals `0` and `1` up to constructor-tree depth 3:

```haskell
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import GHC.Generics (Generic)

import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Generic (HasFTA, deriveFTAWith, domain)

-- | Arithmetic expressions with integer literals.
data Expr = Lit Int | Add Expr Expr
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | Print every expression in a depth-bounded language.
main :: IO ()
main = do
    datatype <- either (fail . show) pure $ deriveFTAWith @Expr (domain @Int [0, 1])
    let language = Gen.fromDatatypeUpToDepth 3 datatype
    total <- either (fail . Gen.explain) pure $ Gen.cardinality language
    mapM_ (either (fail . Gen.explain) print . Gen.unrank language) [0 .. total - 1]
```

Add both `microcfta` and `microcfta-generator` to your component's
`build-depends`. In this checkout, save the program as `Main.hs` at the
workspace root and run:

```sh
cabal build microcfta-generator
cabal exec -- runghc -package=microcfta -package=microcfta-generator Main.hs
```

The output is:

```text
Lit 0
Lit 1
Add (Lit 0) (Lit 0)
Add (Lit 0) (Lit 1)
Add (Lit 0) (Add (Lit 0) (Lit 0))
Add (Lit 0) (Add (Lit 0) (Lit 1))
Add (Lit 0) (Add (Lit 1) (Lit 0))
Add (Lit 0) (Add (Lit 1) (Lit 1))
Add (Lit 1) (Lit 0)
Add (Lit 1) (Lit 1)
Add (Lit 1) (Add (Lit 0) (Lit 0))
Add (Lit 1) (Add (Lit 0) (Lit 1))
Add (Lit 1) (Add (Lit 1) (Lit 0))
Add (Lit 1) (Add (Lit 1) (Lit 1))
Add (Add (Lit 0) (Lit 0)) (Lit 0)
Add (Add (Lit 0) (Lit 0)) (Lit 1)
Add (Add (Lit 0) (Lit 0)) (Add (Lit 0) (Lit 0))
Add (Add (Lit 0) (Lit 0)) (Add (Lit 0) (Lit 1))
Add (Add (Lit 0) (Lit 0)) (Add (Lit 1) (Lit 0))
Add (Add (Lit 0) (Lit 0)) (Add (Lit 1) (Lit 1))
Add (Add (Lit 0) (Lit 1)) (Lit 0)
Add (Add (Lit 0) (Lit 1)) (Lit 1)
Add (Add (Lit 0) (Lit 1)) (Add (Lit 0) (Lit 0))
Add (Add (Lit 0) (Lit 1)) (Add (Lit 0) (Lit 1))
Add (Add (Lit 0) (Lit 1)) (Add (Lit 1) (Lit 0))
Add (Add (Lit 0) (Lit 1)) (Add (Lit 1) (Lit 1))
Add (Add (Lit 1) (Lit 0)) (Lit 0)
Add (Add (Lit 1) (Lit 0)) (Lit 1)
Add (Add (Lit 1) (Lit 0)) (Add (Lit 0) (Lit 0))
Add (Add (Lit 1) (Lit 0)) (Add (Lit 0) (Lit 1))
Add (Add (Lit 1) (Lit 0)) (Add (Lit 1) (Lit 0))
Add (Add (Lit 1) (Lit 0)) (Add (Lit 1) (Lit 1))
Add (Add (Lit 1) (Lit 1)) (Lit 0)
Add (Add (Lit 1) (Lit 1)) (Lit 1)
Add (Add (Lit 1) (Lit 1)) (Add (Lit 0) (Lit 0))
Add (Add (Lit 1) (Lit 1)) (Add (Lit 0) (Lit 1))
Add (Add (Lit 1) (Lit 1)) (Add (Lit 1) (Lit 0))
Add (Add (Lit 1) (Lit 1)) (Add (Lit 1) (Lit 1))
```

`fromDatatypeUpToDepth` compiles the bounded grammar and retains the decoder
for `Expr`. `cardinality` gives the number of replay ranks. `unrank` constructs
the member at a zero-based rank. The example prints all 38 expressions in
rank order. It handles replay errors before printing each `Expr` value.

As in the `microcfta` README, the bound includes the `Int` child of `Lit`.
`Lit 0` has depth one. An `Add` of two literals has depth two. At depth three,
either child of the outer `Add` can itself be an `Add`.

Change `fromDatatypeUpToDepth 3` to `fromDatatypeUpToDepth 4` to generate a
larger language:

| Maximum depth | Number of expressions |
| --- | ---: |
| 2 | 6 |
| 3 | 38 |
| 4 | 1,446 |

Each next depth permits the two literals and every ordered pair of expressions
from the previous depth: `2 + n * n` choices. The rank decoder constructs the
selected values from the compiled grammar.

The QuickCheck adapter adds random sampling and shrinking. Counts and replay
ranks identify accepting derivations; an ambiguous handwritten grammar can
give one term several ranks. This derived expression grammar is unambiguous.

For another complete example, see
[`FinitePairs.hs`](examples/FinitePairs.hs), or run
`cabal run cfta-pairs` from the workspace root.

## Equality-constrained generators

Transparent generator regions retain an exact equality-constrained support,
cardinality, and replay rank; the same layer includes QuickCheck integration
for sampling, opaque fallbacks, and structural shrinking. Run the complete
introductory example from the workspace root with
`nix-shell --run 'cabal run cfta-finite-languages'`.

Import the QuickCheck-facing API:

```haskell
import Data.CFTA.Gen.Equality.QuickCheck (ECTAGen)
import qualified Data.CFTA.Gen.Equality.QuickCheck as ECTAGen
```

### Generator API

`fromAutomatonUpToDepth` compiles an equality-constrained automaton, a
`Node Symbol EqConstraints`, up to a depth. Build it with `mkEdge`, or
annotate an explicit-state automaton with `Data.CFTA.annotate` and intern it
with `Data.CFTA.Interned.fromFTA`.
`fromDatatypeUpToDepth` accepts a derived `TypedFTA EqConstraints a` and returns
typed values. Both functions are available from the QuickCheck API.

For example, derive `(Bool, Bool)` with `deriveFTA`, then use
`annotateDatatype` to attach `mkEqConstraints [[path [0], path [1]]]` to its
tuple constructor. The generator has two ranks: `(False, False)` and
`(True, True)`. The introductory example uses one derived pair grammar for
ordinary and equality generation.

A leaf has depth zero. The bounded import retains one rank per distinct term
and samples uniformly over those ranks. Direct child equalities select once
from the intersection of the child languages. The shared rank plan reuses that
term at each equal position. Size inspection counts source choices, so repeated
equal children contribute one selected child. Shrinks remain accepted.
Nested equality paths and overlapping alternatives use symbolic counts over
shared automaton states. Equality unifies selected subtrees, and overlapping
alternatives count each accepted term once. Unranking constructs only the
selected term. Existing `fromAutomaton` behavior is unchanged.

`Data.CFTA.Gen.Equality` turns a finite indexed source into an ECTA whose leaves contain
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
group. `:&&:` conjoins several equalities. This is the exact-uniform
conditioning of [Claessen, Duregård and Pałka, *Generating Constrained Random
Data with Uniform Distribution*, JFP 25,
2015](https://doi.org/10.1017/S0956796815000143), with the condition reified as
data rather than tested on samples. `match` accepts arbitrary value
projections, so discovering its groups requires enumerating the input ranks;
conditioning three or more generators is the grouped layer's job (`groupBy`
and `apply`).

`relate leftKey rightKey relation left right` admits every pair for which the
projected keys satisfy `relation`. The relation is an ordinary Haskell
function such as `canRead Admin Public = True`; it may be asymmetric and the
two key types may differ. A transparent join evaluates it once per live key
pair, then counts, ranks, and samples the accepted group products directly.
An opaque input uses rejection filtering. `match` remains the shorter and
faster operation for equality because it intersects the two key maps without
testing their Cartesian product.

`relateM` is the compile-time, effectful form for finite transparent inputs.
It groups each input once, invokes the callback once per live key pair, and
then uses the same equality join. `relateGroupsM` starts from already grouped
languages and therefore never enumerates their members; this is the boundary
used by the LTA compiler to turn solver-approved refinement tuples into a pure
ECTA rank plan. `relateN` generalizes that operation to homogeneous n-ary key
tuples, and `filterGroupsM` performs an effectful selection over an existing
key space without visiting the members below each key.

`Grouped key a` is the explicit grouping-preserving path for nested or very
large languages. The `key` is the type returned by the classifier and used to
decide which groups may be joined; it is not part of the generated `a`. Matching
key values receive equal internal labels on constrained ECTA paths. `groupBy`
classifies any transparent generator's outcomes (enumerating them once), and
`keyed key generator` declares that every member already has one known key.
`keyed` does not enumerate members, so it also accepts a recursive transparent
generator. The caller is responsible for declaring the right key. Grouped
generators support ordinary `fmap` (and `mapWithKey` when the value should
absorb its key). `regroupBy` changes the
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
most n) stay grouped. `uniformlyGrouped` combines grouped generators in
proportion to their exact cardinalities, so every member of the union is
equally likely, which is what a layered language wants; `uniformly` does the
same for flat generators. `ungroup` returns an ordinary `ECTAGen` with
the same exact distribution. Stable source order and ascending key order give
deterministic replay ranks.

```haskell
commandsByKind = ECTAGen.oneofGrouped
  [ ECTAGen.keyed Read readCommands
  , ECTAGen.keyed Write writeCommands
  ]
```

Here each command language keeps its existing compact support. Only the two
declared keys are stored.

```haskell
binaryFunctionsBySignature :: Grouped BinarySignature BinaryFunctionInstance
binaryFunctionsBySignature =
  ECTAGen.groupBy binarySignature (ECTAGen.elements binaryFunctionInstances)

binarySignature instance_ =
  firstArgumentType instance_
    :* secondArgumentType instance_
    :-> binaryResultType instance_

literalsByType :: Grouped Type TypedExpression
literalsByType = ECTAGen.groupBy expressionType (ECTAGen.elements literals)

unaryFunctionsBySignature :: Grouped UnarySignature (TypedExpression -> TypedExpression)
unaryFunctionsBySignature =
  compileNot <$ ECTAGen.keyed unarySignature (ECTAGen.elements [()])

conditionalFunctionsBySignature =
  compileConditional
    <$> ECTAGen.groupBy conditionalSignature (ECTAGen.elements allTypes)

binaryLayer children =
  ECTAGen.apply
    (compileBinary <$> binaryFunctionsBySignature)
    (children :& children :& ANil)

conditionalLayer children =
  ECTAGen.apply
    conditionalFunctionsBySignature
    (children :& children :& children :& ANil)
```

The
[`Data.CFTA.Gen.TypedExpressionLanguage`](https://github.com/Tritlo/microecta/blob/main/microcfta-generator/common/Data/CFTA/Gen/TypedExpressionLanguage.hs)
flagship, a test and benchmark support module, combines unary `Not`, binary functions, and
ternary `IfExpression`. Its finite layers combine those three alternatives with
`uniformlyGrouped`, so every expression remains equally likely. Its
recursive layer uses equal structural alternatives, as recursive declarations
require.

Both layers also support qualified do-notation through `Data.CFTA.Gen.Equality.Do`,
which `Data.CFTA.Gen.Equality.QuickCheck` re-exports. Enable `QualifiedDo` together
with `ApplicativeDo`; statements must stay independent, and the final
statement must use the qualified `ECTAGen.pure`. A grouped block chooses the
operation family first and then one argument per signature component in
order; whatever the arity, it builds exactly one `apply` join:

```haskell
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE QualifiedDo #-}

authentication :: ECTAGen Authentication
authentication = ECTAGen.node "authentication" $ ECTAGen.do
  user <- generatedUser
  method <- ECTAGen.elements [Password, Token]
  ECTAGen.pure (Authentication user method)

conditionalLayer children = ECTAGen.node "if" $ ECTAGen.do
  build <- conditionalFunctionsBySignature
  condition <- children
  ifTrue <- children
  ifFalse <- children
  ECTAGen.pure (build condition ifTrue ifFalse)
```

Impossible shapes fail at compile time with an explanation: a statement using
an earlier bound value, an unqualified `pure` ending, or a fallible pattern.
A block that binds fewer arguments than its operation's signature arity is a
type mismatch against `Applying`, whose haddock says what the remaining keys
are. A statement whose result is a tuple, as `match` and `relate` give, must
bind it lazily: `ApplicativeDo` rejects `(a, b) <- match ...` and accepts
`~(a, b) <- match ...`.

Every transparent generator samples compositionally by rank, including exact
non-uniform `frequency` and conditioned joins; sampling never materializes the
final Cartesian product. `cardinality` and `unrank` expose deterministic
replay, while `countBy` reports exact coverage of ranked outcomes. A retained
`Grouped` key is also a symbolic observation. `countsAtSize` reports how many
members reach each key. `massesAtSize` reports the exact key distribution used
by sampling that size. Declared atomic weights can therefore produce equal
counts and unequal masses. Recursive groups memoize both size series, so these
queries do not enumerate traces. ECTA support is demand-driven: counts, masses,
replay, sampling, and constrained joins retain it as a lazy thunk. `support`
forces the complete symbolic representation.

`smallest (atKey key family)` returns a globally smallest witness for one
observation. An unreachable key returns `Right Nothing`. A temporal observation
such as "failure state reached" belongs in the recursive key as a sticky state
bit; it is not recovered later by filtering complete traces.

`pmfAtSize` asks the more general value-level distribution question. It
interprets the same size-indexed sampler used by lowering, including weighted
atomic choices, but may enumerate products before equal results are aggregated.
The generic `countBy`, `pmf`, and `pmfAtSize` observers are therefore best for
finite or small result languages. Retain a reusable classification with
`Grouped` when the observation is part of a recursive language.

```haskell
failure = ECTAGen.atKey FailureReached tracesByOutcome

shortestFailure = ECTAGen.smallest failure
outcomeCounts = ECTAGen.countsAtSize tracesByOutcome 41
outcomeProbabilities = ECTAGen.massesAtSize tracesByOutcome 41
samples = ECTAGen.toGen (ECTAGen.ungroup tracesByOutcome)
```

`AtSize` means structural source choices, not list length. In this example the
empty trace contributes one choice, so size 41 represents forty commands.

`Data.CFTA.Gen.Equality.QuickCheck` exposes `toGen`, plus
`toGenWithRank` when the sampled replay rank is needed. `forAll` checks a
property and shrinks to the smallest failing member. It first tests every
member of strictly smaller size, in size order (`smallerMembers`, capped by
`smallerMemberLimit`), so the reported counterexample is globally size-minimal
whenever that search reaches one. Behind that it offers size-major structural
shrinking through `shrinkRank`, which for a recursive generator reads its
candidates from the form bounded at the current size, since bounding is what
gives a recursive member components to shrink. Every candidate is a member of
the generated language, and the failing rank is printed for deterministic
replay with `unrank`. A generator with an opaque region has no ranks at all, so
`forAll` tests it by sampling with no shrinking. `sized` builds and compiles
one generator per QuickCheck size (shared across samples), so layered
generators can scale with the size parameter.

Greedy shrinkers - QuickCheck, Hedgehog, Hypothesis, falsify - stop at a local
minimum. Bounded-exhaustive tools find a smallest counterexample by testing the
whole space up to a bound ([Runciman, Naylor and Lindblad, *SmallCheck and Lazy
SmallCheck*, Haskell 2008](https://doi.org/10.1145/1411286.1411292), and FEAT's
exhaustive modes). `forAll` gets a size-minimal counterexample starting from a
random one, by enumerating every member of strictly smaller size first.

```haskell
import Data.CFTA.Gen.Equality.QuickCheck (ECTAGen)
import qualified Data.CFTA.Gen.Equality.QuickCheck as ECTAGen

joined :: ECTAGen (Authentication, Filesystem)
joined =
  ECTAGen.match
    (authenticatedUser :==: fileOwner)
    authentication
    filesystem
```

```haskell
canRead :: Role -> Classification -> Bool
canRead Admin _ = True
canRead Member Public = True
canRead _ _ = False

authorized :: ECTAGen (User, File)
authorized =
  ECTAGen.relate roleOf classification canRead users files
```

```haskell
replay :: Either GenError Authentication
replay = ECTAGen.unrank authentication 42

coverage :: Either GenError (Map UserId Integer)
coverage = ECTAGen.countBy authenticatedUser authentication
```

### Inspect a generator

Use `namedElements` to retain source names, including names for function values.
Use `nameGroups` to retain display names for classified keys without decoding
their members. Both functions preserve semantic support, ranks, and weights.

```haskell
{-# LANGUAGE OverloadedStrings #-}

import qualified Data.CFTA.Gen.Equality.QuickCheck as Gen

-- | Two named integer source choices.
integers :: Gen.ECTAGen Int
integers = Gen.namedElements [("zero", 0), ("one", 1)]

-- | Apply a named function to the integer source.
incremented :: Gen.ECTAGen Int
incremented = Gen.namedElements [("increment", (+ 1))] <*> integers
```

`Gen.inspect incremented` returns an `Inspection`. Its `inspectionGraph` is a
`Node InspectionSymbol EqConstraints`. Pass it to `ECTA.toTree`, then render the typed
labels with `fmap` and `Data.Tree.drawTree`. Each `InspectionSymbol` retains
`originalSymbol` and an optional `displayLabel`. `inspectionName` holds a group
name when one is available. `ViewPath` locations belong to the graph passed to
`toTree`.

Source names describe source choices. `fmap` preserves those names; it does not
infer names for mapped results. `regroupBy` clears old group names because the
keys change. Apply `nameGroups` after regrouping to name the new keys. Source
names remain available through grouping, application, and recursion.

The diagnostic graph preserves construction structure and equality obligations.
Names distinguish occurrences that share one semantic node, such as integer
and Boolean sources with the same rank indices. The graph does not run equality
reduction. Use `Gen.support` for membership and other semantic operations.

Counts and rank decoding do not evaluate display names or construct the
diagnostic graph. Retaining the extra fields and closures still uses memory.
Inspecting the graph also allocates its nodes and formatted names.

Run `cabal run cfta-draw-typed-expressions` to draw the actual finite and recursive
expression generators. The [complete renderer](examples/DrawTypedExpressions.hs)
shows source choices such as `Add :: Int -> Int -> Int` and `IntLiteral 0 :: Int`,
with `Int` and `Bool` labels on the equality witnesses.

#### Read the ASCII tree

The drawing alternates between state lines (`q0`, `q1`, ...) and transition
lines (`choice 0`, `if`, `Add :: Int -> Int -> Int`, ...). At a state, choose
one transition alternative. A chosen transition uses all of its child states
in order. For example, the two alternatives below `q5` select `Add` or
`Multiply`; the children below `binary-application` supply its operation and
both arguments.

Each state occurrence has a local name and a root-relative location:

```text
q14 @1:0/0:1
```

`q14` identifies the state in this drawing. The text after `@` identifies this
occurrence of that state. Read each `alternative:child` pair as two zero-based
indexes: select a transition alternative, then select one of its children.
Index `0` means the first item. A slash starts the next step from the reached
state. `@root` means the initial state, with no steps.

In the depth-one `Int` drawing, `@1:0/0:1` means:

| Step | Current state | Select alternative | Select child | Reach |
|---|---|---|---|---|
| `1:0` | `q0` | `1`: `choice 1` | `0`: its only child | `q9`, the conditional state |
| `0:1` | `q9` | `0`: `if` | `1`: the condition argument | `q14` |

The location is stored as `[(1, 0), (0, 1)]` in `viewPath`. The child indexes
include the operation: below `if`, child `0` holds the operation, child `1`
holds its condition argument, and children `2` and `3` hold its two branches.
The condition argument has its own type witness and value child. One further
step, `0:1`, reaches its Boolean literal choices at `@1:0/0:1/0:1`.

References stop repeated expansion:

| State line | Meaning |
|---|---|
| `q7 @0:0/0:1/0:1` | Expand state `q7` at this occurrence. |
| `ref q7 @0:0/0:2/0:1` | Reuse the same state from another occurrence. |
| `mu q0 @...` | Refer to an ancestor state and stop the recursive expansion. |

A reference's `@` path locates the reference, not the earlier definition.
State names and occurrence paths belong to one drawing. They can change when
the graph or its alternative order changes.

Equality annotations use a different path notation. In
`binary-application [0.1 = 2.0, 0.0 = 1.0]`, each dot-separated path starts at
that transition and follows child indexes only. Thus `0.1` reaches the
operation's second type witness, and `2.0` reaches the second argument's type
witness. The equality requires those subterms to agree. These paths do not
contain alternative indexes and do not start at the drawing's root.

### Recursive languages

`recur` builds a generator from its own language, so a language can be
unbounded rather than unrolled layer by layer:

```haskell
tree :: ECTAGen Tree
tree = ECTAGen.recur $ \self ->
    ECTAGen.oneof
        [ Leaf <$> ECTAGen.elements [0 .. 2]
        , Branch <$> self <*> self
        ]
```

The result stands for the whole language. It has no cardinality; it has
size classes, counted by FEAT-style convolution, where size is the number of
source choices in a member — `countAtSize tree 4` is `Right 405` for the
tree above. Ranks are size-major, so `unrank tree 0` is the smallest member
and every rank replays as usual, and the ECTA support is a `Mu` node: one
finite automaton for infinitely many terms.

The convolution is FEAT's ([Duregård, Jansson and Wang, *Feat: Functional
Enumeration of Algebraic Types*, Haskell
2012](https://doi.org/10.1145/2364506.2364515)), but the size measure is not:
FEAT charges size wherever the definition says `pay`, while here every source
choice costs one and nothing else does. "Size-major rank" is this package's own
term for the resulting order. Counting a family by a size recurrence and
drawing from those counts is the recursive method of Nijenhuis and Wilf,
*Combinatorial Algorithms*, 2nd ed., 1978, and of [Flajolet, Zimmermann and Van
Cutsem, *A Calculus for the Random Generation of Labelled Combinatorial
Structures*, TCS 132, 1994](https://doi.org/10.1016/0304-3975(94)90226-7);
turning a rank back into a member is unranking, as in [Martínez and Molinero,
*A generic approach for the unranking of labeled combinatorial classes*, RSA
19, 2001](https://doi.org/10.1002/rsa.10025).

`pure` is one source choice like any other, so `pure f <*> x` has one more
choice than `f <$> x`: the two have different sizes and therefore different
ranks. It also counts as guarding recursion, so `pure f <*> self` is accepted
where `f <$> self` is `UnguardedRecursion`.

`upToSize n` bounds the language back to an ordinary finite generator over
the members of size at most `n`, and `toGen` and `forAll` apply it from
QuickCheck's size parameter. Size classes and structural alternatives are
selected from their member counts; weighted finite choices closed with
`atomic` retain their declared PMF inside the selected size. Bounding preserves
ranks: the members of size at most `n` hold the same ranks under every bound
large enough to contain them. A counterexample therefore replays under any
larger bound, and `forAll` shrinks by walking whole size classes below the
failing member and then, past its cap, by shrinking the components of the form
bounded at the failing member's size.

`atomic` treats every member of a finite generator as one source choice. This
sets a domain-sized boundary inside a recursive language. For example, an
acyclic command FTA can retain its compact support and rank decoder while each
complete command, rather than each node in its term, contributes one unit to a
trace's size:

```haskell
command = decodeCommand <$> ECTAGen.atomic (ECTAGen.fromAutomaton commandFTA)

nonEmptyTrace = ECTAGen.recur $ \rest ->
  ECTAGen.oneof
    [ (: []) <$> command
    , (:) <$> command <*> rest
    ]
```

This does not enumerate the FTA or add one support edge per command. It keeps
the accepted language, compact support, ranks, and decoder. The whole acyclic
FTA becomes the finite command source, so QuickCheck's size acts on the outer
trace instead of taking a second prefix inside each command. For an already
finite generator, its cardinality and distribution also stay unchanged. Only
the size and structural-shrinking boundary changes. A recursive input has
infinitely many members, so bound it with `upToSize` before making it atomic --
and do that *outside* the recursive definition. Neither `upToSize` nor `atomic`
can be applied to the `recur` argument, or to anything built from it: the bound
would need the size classes that definition is still computing, and an atom
over them would have a cardinality depending on itself. Both shapes are
rejected with `BoundedRecursiveOccurrence`. Opaque generators have no size
structure and cannot be made atomic.

The self-reference has to go through `recur`. A generator that names itself
directly, as in `tree = Branch <$> tree <*> tree`, is an infinite Haskell
value: building it never finishes, and the failure is a hang rather than
anything the library can report. In the other direction, a body that never
uses the argument is not recursive, and is handed back as it is: a finite
body stays a finite generator, cardinality and inspection included. A body
that could not be built at all reports its own error, rather than becoming a
recursive language every finite inspector calls unbounded.

Two rules apply inside the knot. The recursion must be guarded: every
occurrence of the argument sits under at least one `<*>`, or the language
has no smallest member — an unguarded definition is rejected with
`UnguardedRecursion` rather than left to hang. The check is per definition, so
inside a nested `recur` an occurrence of the *outer* language must also sit
under an application within the inner body. Structural alternatives around a
recursive occurrence must carry equal weights; `oneof` is the combinator that
already reads that way, and the size bound controls how large members get.
`frequency` with unequal recursive-branch weights is rejected rather than
ignored. A weighted finite choice may still enter through `atomic`, retaining
its own distribution inside every recursive size.

Inspection that needs one ECTA term per member (`groupBy`, `match`, `relate`,
`pmf`, `countBy`) is not available on a language built with `recur`, bounded or
not: a recursive generator retains its automaton rather than a term per member,
and `upToSize` bounds the rank space without recovering those terms. Use the
exact-size observers (`countAtSize`, `pmfAtSize`, `countsAtSize`,
`massesAtSize`), keep that layer finite, or read the language from an automaton
with `fromAutomaton`, whose members *are* terms and which therefore does keep full
inspection once bounded.

`recurGrouped` does the same for the grouped layer, which is where recursion
and equality constraints meet in one cycle:

```haskell
expressions :: Grouped Type TypedExpression
expressions = ECTAGen.recurGrouped $ \self ->
    ECTAGen.oneofGrouped [literalsByType, applicationLayer self]

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

For the language above, unfolding that automaton twice accepts exactly the 46
expressions produced by the hand-unrolled depth-one generator. This includes
unary `Not`, the binary functions, and ternary `IfExpression`. `ungroup` and
`atKey` are the exits back to an ordinary recursive generator, so bounding,
sampling, replay, and shrinking all work as above. `sizes` has no cardinality
to report for a recursive family; use `countAtSize` on `atKey`.

`fromAutomaton` goes the other way: it reads an existing automaton as a generator
of the terms it accepts, counting them by size — the number of term nodes —
with the automaton itself as the support.

```haskell
import qualified Data.Tree as Tree

types :: Node Symbol EqConstraints
types = createMu $ \recursive -> Node
    [ Edge "baseType" []
    , Edge "->" [recursive, recursive]
    , Edge "Maybe" [recursive]
    ]

typeGen :: ECTAGen (Tree.Tree Symbol)
typeGen = ECTAGen.fromAutomaton types
```

`countAtSize typeGen` reports 1, 1, 2, 4, 9 for sizes one to five, `unrank`
walks the terms in size order, and sampling draws uniformly from the terms
of at most the current size. Because the generated values *are* the accepted
terms, bounding one of these keeps full inspection: `pmf`, `countBy`, and
`groupBy` all work on `upToSize n (fromAutomaton node)`.

Equality constraints are not counted. They correlate an edge's children, so
the edge's count is the size of an intersection rather than a product of the
children's counts; an automaton carrying them is rejected with
`CannotCountConstrainedEdges` rather than miscounted.

Ambiguity is not counted either. A node's count is the sum over its edges,
which counts accepting *runs*, so a node with two edges that accept a common
term would count that term twice and `unrank` would return it at two ranks.
Every reachable node is checked, and an ambiguous automaton is rejected with
`AmbiguousAutomaton`. Two edges overlap when they share a symbol and arity and
every child position has a non-empty intersection, which without constraints
is exactly when they share a term.

`fromIndexed` is the transparent boundary for a FEAT-style finite enumeration:
it needs only a cardinality and a stable function from an integer index to a
value. `elements` is the corresponding list convenience function.

`Data.CFTA.Ranked.fromIndexedOnDemand` is the automaton-adapter variant. It keeps
the same cardinality, ranks, and sampler but never tabulates a small indexed
source while compiling its replay decoder. LTA counting uses it so the
automaton remains a graph until one rank is selected.

`pool n native` bridges a large or infinite QuickCheck source into this finite
world. Its outer `Gen` samples `n` values once and returns an `ECTAGen` whose
ranks are those draws. The result supports exact inspection and constrained
joins. Repeated draws remain repeated ranks and therefore retain their
empirical weight. Reuse the returned generator when two choices must range over
the same frozen universe.

`freeze seed n native` is `pool` with the draws fixed by a seed, so it is an
ordinary transparent generator rather than a `Gen` of one: it can be weighted
by `uniformly`, keyed, joined, replayed, and shrunk, and its ranks are the same
in every run under the same seed. The native generator runs at QuickCheck size
30, the default of `generate`; use `resize` on it for another size.

Every failure is a `GenError`. The derived `Show` names the case, and
`explain` says what it means and which combinator resolves it; sampling a
generator that could not be built raises both together.

```
>>> putStrLn (ECTAGen.explain ECTAGen.UnguardedRecursion)
The recursive language reaches itself without passing through an
application, so its members never get smaller and no size class can
be counted.
Fix: put every occurrence of the argument under <*>, as in
Branch <$> self <*> self, or under apply in a grouped family. An
alternative that is the argument itself, such as oneof [leaf, self],
is the shape to look for.
```

`fromGen` embeds an ordinary `QuickCheck.Gen` as an explicitly opaque region.
Opaque regions still compose and sample, but cannot be inspected with `pmf`;
joining through one falls back to QuickCheck rejection. Opaque regions also
have no replay rank, and `forAll` therefore tests a generator holding one by
sampling alone, without shrinking. There is deliberately no `Monad` or
`Selective` instance.
This keeps inspectable applicative regions inside ECTA and makes the loss of
structure explicit.


## Refinement-constrained generators

Describe candidate values and their refinements. Add a guard with named child
arguments. Call `compile` once, then use pure sampling, replay, and shrinking.
The compiler retains symbolic counts and constructs selected values on demand.
Unsupported guards return an error.

### A complete first program

This program generates safe divisions. It rejects the zero denominator before
it evaluates the division.

```haskell
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTA
import Data.CFTA.Refinement.Guard (requires)
import Data.CFTA.Refinement.LiquidFixpoint (integerDeclarations, withZ3)
import Data.CFTA.Refinement.Expression (integer, value, (./=.), (.==.))
import qualified Test.QuickCheck as QC

main :: IO ()
main = withZ3 (integerDeclarations ["v"]) $ \solver -> do
  let nonZero = value ./=. integer 0
      denominators = LTA.pool
        [ LTA.refined (0 :: Integer) "zero" (value .==. integer 0)
        , LTA.refined 1 "one" (value .==. integer 1)
        , LTA.refined 2 "two" (value .==. integer 2)
        ]
      divisions =
        LTA.node "divide" (\denominator -> denominator `requires` nonZero) $ LTA.do
          denominator <- denominators
          LTA.pure (denominator, 12 `div` denominator)
  compiled <- LTA.compile solver divisions >>= either (fail . LTA.explain) pure
  QC.quickCheck $ LTA.forAll compiled $ \(denominator, quotient) ->
    denominator /= 0 && quotient == 12 `div` denominator
  print $ fmap LTA.generatedValue $ LTA.unrank compiled 0
```

Use the packages `base`, `microcfta`, `microcfta-generator`, and `QuickCheck`.
Install Z3 and put it on `PATH`. The public refinement helpers do not require a
Liquid Fixpoint import. `value` is the conventional refinement variable `v`;
`variable "input"` names another expression. Declare each variable's sort before
compilation. `integerDeclarations` declares integer variables, and
`withZ3Assuming` adds ambient facts when a contract depends on external inputs.
The lower-level solver API accepts other sorts and custom entailment callbacks.

The caller must ensure that each refinement describes its Haskell value.
The compiler proves implications between these annotations. It does not inspect
an arbitrary Haskell value to prove its annotation. Mapping a generator changes
its Haskell value and retains the term and refinement that justify its guards.

Run the checked introductory example from the workspace:

```sh
nix-shell --run 'cabal run cfta-safe-division'
```

[`SafeDivision.hs`](https://github.com/Tritlo/microecta/blob/main/microcfta-generator/examples/SafeDivision.hs) also checks ambient assumptions,
exact replay, and semantic pool shrinking. CI runs it and the automaton example.

### Construction and compilation

`fromDatatypeUpToDepth` accepts a derived
`TypedFTA (Refinement, LiquidConstraint) a`. Use `annotateDatatype` to supply
the refinement and constraint for each constructor. The datatype supplies its
fields and recursive structure. The existing LTA compiler supplies accepted
terms, exact replay, and valid shrinking; the retained codec supplies `a`.
The caller must still justify the refinements assigned to each constructor.

The natural-number example in `examples/AutomatonInterop.hs` derives its
recursive grammar, annotates zero and successor, and uses the generated
datatype in safe divisions. A handwritten graph is an LTA already: build it
with `Node`, `Transition`, and `Mu`, and pass it to `fromAutomatonUpToDepth`.

Finite counting, structural ambiguity checks, direct value decoding, depth
bounds, and ordinary automaton shrinking use the shared FTA implementation.
Liquid guard evaluation, refinement grouping, and Boolean equality
interpretation remain in this layer.

Each qualified do-block describes independent direct children. Its adjacent
`node` supplies the constructor and guard. Guard arguments have the same order
as the child generators. A named guard must take exactly one argument per
child; write `_` for an unused child. An argument-count mismatch is a construction
error, including when the source is empty. Raw `LiquidConstraint` values remain
available and retain the paper's Boolean meaning for missing paths.

`node` uses the universal result refinement. `refinedNode` supplies a fixed
result refinement. `refinedNodeByRoots` computes one from child labels and
refinements with a single function. `refinedNodeBy` computes one from the
Haskell result. Only the explicit `validOutcomes` diagnostic accepts that
value callback; compilation rejects it.
Dependent child choices do not belong in the applicative block. Express their
relationship in the guard, for example `actual `isSubtypeOf` expected`,
`argument `requires` nonZero`, or
`withActualFor actual formal dependentResultCheck`.
`descendant argument [1]` selects the argument's second child.

`isSameTermAs` normally requires exact subtree equality. Inside `withActualFor`,
it compares views with the formal symbol replaced by the actual symbol,
including free variables in refinement annotations. The generated terms and
values stay unchanged. Several replacements in `withActualsFor` apply
simultaneously. Compilation can decide this scoped equality on observed leaves.
Scoped equality on compound subtrees remains unsupported by the compiler.

`compile` retains original source order and source weights. It groups candidates
by the observations a guard needs, then indexes the accepted source ranks.
This can represent a language larger than a machine integer without traversing
its members. Bounded automata use symbolic counts for nested equality,
negation, disjunction, and overlapping alternatives. Each distinct accepted
term has one rank, and unranking constructs only the selected term.

Compilation has no cardinality limit and no enumerating fallback. Its cost can
still grow with the number of distinct observation groups or equality contexts.
Value-computed refinements and unresolved guards return errors. For example,
substitution guards that need the identity of compound actual terms remain
unsupported. `explain` describes each error. An undecidable acceptance guard is
an error. An undecidable optional shrink implication omits the unproved edge.

Repeated pool entries retain separate ranks and sampling weight. `frequency`
multiplies each branch's occurrence weights; it does not assign equal probability
to branches of different sizes. Mapping two members to the same value does not
merge their ranks. Replay is deterministic for a fixed language and source
order. A changed pool, bound, or specification can change the ranks.

Pool shrinks weaken a refinement. Equivalent refinements move toward earlier
pool entries. Composite sources keep these semantic shrinks and search through
rejected intermediate candidates to return accepted targets. Imported automata
use structural shrinks that strictly reduce tree node count. All returned
shrinks stay in the compiled language. Sampling, replay, and shrinking make no
solver calls.

### Import an LTA

`fromAutomatonUpToDepth` is the escape hatch for an existing automaton. It takes an explicit
maximum tree height; leaves have height zero. It preserves the shared graph
until compilation and composes with ordinary sources:

```haskell
boundedTerms = LTA.fromAutomatonUpToDepth 6 automaton

wrapped = LTA.node "wrap" (\child -> child `requires` desiredRefinement) $ LTA.do
  term <- boundedTerms
  LTA.pure (decode term)

compiled <- LTA.compile solver wrapped >>= either (fail . LTA.explain) pure
```

Each distinct accepted annotated term has one rank, even when several runs
accept it. Equal Haskell values obtained from different terms remain distinct.
An empty or negative-bound import is an empty source and can occur beside a
nonempty alternative. Recursive automata are bounded before counting. Ambiguous
runs count each accepted term once. Boolean subtree equality uses symbolic
intersections and complements after semantic pruning. Residual semantic or
scoped compound-equality guards return an error.

[`AutomatonInterop.hs`](https://github.com/Tritlo/microecta/blob/main/microcfta-generator/examples/AutomatonInterop.hs) derives a recursive
natural-number grammar, annotates it, imports it with `fromDatatypeUpToDepth`,
and composes it with a refined pool:

```sh
nix-shell --run 'cabal run cfta-automaton-interop'
```

`support` explicitly enumerates an ordinary source. An unresolved `fromAutomatonUpToDepth`
source instead returns `SourceRequiresCompilation`; inspect `compiledSupport`
after compilation. `validOutcomes` explicitly enumerates checked candidates and
has no materialization limit. These observers are for small diagnostic inputs.

### Advanced compilation APIs

`compileRelational` exposes native grouped ECTA order and structural shrinking.
It accepts unit-weight alternatives and reports guards that its observations
cannot decide. Its ranks and shrink policy differ from the default compiler's
source order and semantic shrinking.

`compileAutomaton` handles finite automata. `compileAutomatonUpToDepth` first
bounds recursive automata. Both retain symbolic counts for Boolean subtree
equality after semantic pruning. Their `With` variants fold each selected
transition directly into a domain value and leave the term witness lazy.
Use `compile` with `fromAutomatonUpToDepth` for a bounded source that composes with other sources.

The authoritative representation remains an LTA. Pruning returns an LTA. A
pruned automaton without constraints is counted as an ordinary FTA; residual
positive, negated, or disjunctive equality uses the symbolic counter. A
residual guard outside that fragment is reported as `ResidualGuard`. Core
`denotationAtMost` remains an explicit bounded reference evaluator.

### Frozen native pools

The pool need not be part of a long-lived specification. It can be sampled and
frozen only for one generation run:

```haskell
compiled <- LTA.compileSampled solver $ do
  lefts  <- LTA.samplePool 32 nativeRefinedInt
  rights <- LTA.samplePool 8  nativeRefinedInt
  pure $
    LTA.node "pair" subtypePair $ LTA.do
      left  <- lefts
      right <- rights
      LTA.pure (left, right)
```

Here the two pools are sampled independently. Sample once and use the same
`LTAGen` at both child positions when they should share a universe. The pools
remain fixed inside `compiled`; changing them for each individual test would
make ranks, replay, and shrinking unstable and would also invoke Z3 per test.
Independent pool sizes multiply: the example describes 32 x 8 candidate pairs.
The default compiler groups the observations needed by the guard. Use smaller
pools when every candidate has a distinct observation.

For replay across process runs, fix each pool with a seed, just as in the
equality generator:

```haskell
lefts  = LTA.freeze 20260902 32 nativeRefinedInt
rights = LTA.freeze 20260903 8  nativeRefinedInt
```

The same seed, size, and native generator produce the same pool ranks. Reuse a
single frozen value at several child positions when they should range over one
shared universe; use distinct seeds for independent pools.

#### Push direct refinements into opaque sampling

Freezing first can waste most of a small native pool on values the LTA will
immediately reject. An `OpaqueSource` receives the unconditional refinements
required at its direct child position, so an adapter for the native value can
move those requirements into `suchThat` before the pool is frozen:

```haskell
offsetSource =
  LTA.opaqueSource
    (\requirements ->
      chooseInt (-128, 127) `suchThat` \offset ->
        all (`offsetSatisfies` offset) requirements)
    (fromString . ("offset-" <>) . show)
    exactOffset

sampledReads =
  LTA.sampledNode "read-at" (\offset -> offset `requires` validOffset) $
    PageRead <$> LTA.opaquePool 32 offsetSource
```

This leaves the range predicate in the LTA specification; it is not duplicated
as a second handwritten generator contract. `offsetSatisfies` is the small
boundary that interprets the refinements this opaque Haskell type understands.
The library cannot generically evaluate a Liquid Fixpoint expression over an
arbitrary Haskell value.

Several `opaquePool` calls may be combined applicatively. `sampledNode` routes
the first guard argument's requirements to the first pool, the second to the
second, and so on. It deliberately pushes only positive, direct-child
`requires` clauses (and conjunctions of them). Subtyping between children,
substitution, disjunction, negation, and nested paths still need the assembled
term and remain solver work.

The optimization is not trusted: `compile` checks the exact refinement attached
to every sampled value against the original guard with Z3. A partial adapter
therefore leaves extra candidates for compilation to reject; an incorrect
adapter can discard useful candidates but cannot admit an invalid one. As with
any `suchThat`, use this only for reasonably dense predicates. Constructive
native generation is preferable when rejection sampling would be sparse or
unsatisfiable.

The executable
[`OpaquePoolSpec`](https://github.com/Tritlo/microecta/blob/main/microcfta-generator/test/Data/CFTA/Gen/Refinement/OpaquePoolSpec.hs) compares this with the
freeze-first route on a partial page read, checks every retained offset, and
uses a two-pool division example to verify positional routing.

### What the LTA adds

An FTA says which constructor shapes exist. An ECTA additionally says that two
paths must contain the same term. An LTA can say that one path's refinement
implies another predicate, including after substituting actual argument names
for formal parameters. That permits constraints such as:

```haskell
safeDivision =
  LTA.node "divide" validDenominator $ LTA.do
    numerator   <- integers
    denominator <- integers
    LTA.pure (Divide numerator denominator)

validDenominator _ denominator = denominator `requires` nonZero
```

For dependent application, put the result type, function, and argument in the
term exactly as the paper does, and give names to the nested type positions:

```haskell
applicationGuard result function argument =
  allOf
    [ argument `isSubtypeOf` descendant function [1] -- input type
    , withActualFor argument (descendant function [0]) $
        descendant function [2] `isSubtypeOf` result -- output type
    ]
```

The default compiler checks these contracts through grouped observations where
possible. It uses complete candidates when the contract needs them. Both paths
return a pure language with the same source ranks and semantic shrink policy.

### Flagship: typed state-machine traces

[`Data.CFTA.Gen.Refinement.StateMachineTraceLanguage`](https://github.com/Tritlo/microecta/blob/main/microcfta-generator/common/Data/CFTA/Gen/Refinement/StateMachineTraceLanguage.hs)
is the LTA step in the repository's worked progression. The FTA example has
only integer expression shapes; the ECTA example adds Boolean result types;
this example carries those types through time as a stack-machine state.

The abstract contract is the familiar typed reverse-Polish calculator:

```text
Push TInt  : Stack s                   -> Stack (TInt  ': s)
Add        : Stack (TInt ': TInt ': s) -> Stack (TInt  ': s)
Equal      : Stack (a    ': a    ': s) -> Stack (TBool ': s)
Pop        : Stack (a    ': s)         -> (a, Stack s)
```

Those are explanatory signatures, not GADT constructors. The public Haskell
values stay ordinary. The surface specification recursively builds a prefix
and one command, grouped by their root refinements. The liquid guard decides
which group tuples survive, and `refinedNodeByRoots` propagates the resulting
output state without decoding the traces hidden inside those groups:

```haskell
extendTrace prefixes =
  LTA.refinedNodeByRoots
    "step"
    stepRefinementFromRoots
    validStep $ LTA.do
      prefix  <- prefixes
      command <- commandContracts
      LTA.pure (predictPrefixStep prefix command)

validStep previous command =
  allOf
    [ previous `isSubtypeOf` command
    , withActualFor previous (descendant command [0]) $
        descendant command [1] `isSubtypeOf` root
    ]

Right compiled <- LTA.compile solver (tracesOfLength length)
```

The first guard says that the preceding trace's output state inhabits the next
command's input space. The second substitutes that actual state for the
command's formal `model` and proves its output formula implies the new trace
root. With the top stack type in the low bits, for example, pushing an integer
has output `v = 2 * model + 1`, while `Add` accepts two leading integer tags and
has output relation `model = 2 * v + 1`.

The stack depth is bounded only to keep the refinement-key space finite. There
is one liquid schema per operation; each compilation layer relates the live
prefix-state and command-contract groups instead of expanding complete command
sequences. This is where the LTA is materially clearer than an ECTA: a bounded
ECTA could tabulate every valid state pair, but it cannot state and reuse the
dependent arithmetic transition itself.

Following the
[quickcheck-state-machine workflow](https://well-typed.com/blog/2019/01/qsm-in-depth/),
the whole trace is generated before execution. Every retained event predicts
its before-state, response space, and after-state. The specs ask Z3 to prune the
LTA, check its independently computed cardinalities, enumerate all 132 accepted
traces of length three, and replay each through an independent abstract model
and a separate concrete integer/Boolean interpreter. A smaller surface-DSL
variant also verifies guarded shrinking. The final QuickCheck property needs no
implication or `suchThat` filter.

### LTA-biased case study: sized-vector pipelines

The stack machine is a good stateful progression, but its bounded stack shapes
can still be tabulated by a sufficiently patient FTA author. The more
LTA-native example is
[`Data.CFTA.Gen.Refinement.SizedVectorLanguage`](https://github.com/Tritlo/microecta/blob/main/microcfta-generator/common/Data/CFTA/Gen/Refinement/SizedVectorLanguage.hs): a
dependent vector-expression language in which result sizes are arithmetic
refinements rather than finite type tags.

```text
append xs ys    : Vector n -> Vector m -> Vector (n + m)
take k xs       : 0 <= k <= n => Vector n -> Vector k
zipWith (+) x y : Vector n -> Vector n -> Vector n
index i xs      : 0 <= i < n => Vector n -> Int
```

One operation layer is ordinary applicative LTA syntax:

```haskell
takenVectors maximumLength children =
  LTA.refinedNodeByRoots "take" resultRefinement validTake $ LTA.do
    result    <- possibleLengths maximumLength
    _function <- takeFunction
    count     <- possibleLengths maximumLength
    input     <- children
    LTA.pure $ SizedVector
      (Take (numberValue count) $ vectorExpression input)
      (numberRefinement result)

resultRefinement ((_, refinement) : _) = refinement
resultRefinement [] = true

validTake result function count input =
  withActualFor count (takeCountFormalAt function) $
    allOf
      [ vectorLengthAt input `isSubtypeOf` function
      , takeResultAt function `isSubtypeOf` result
      ]
```

The `takeFunction` contract says that its input length is at least the formal
`k` and its result is exactly `k`. The guard substitutes the selected count for
that formal. `append` substitutes both input lengths into `out = n + m`;
`zipWith` substitutes the left length and requires the right length to inhabit
the same input space. A stable result-length child lets these proofs compose at
the next expression layer without exposing a refinement wrapper in `Program`.

The one-layer language contains 20 pipelines and exactly 44 safe indexing
programs. The tests enumerate them, check every result refinement against an
independent list interpreter, and execute the deliberately partial indexer over
every accepted program.

This is the specification-leverage example. A handwritten exact-uniform
generator must group every recursive sublanguage by result length, derive the
append, take, and zip cardinality recurrences for those groups, weight each
constructor by its number of valid completions, and repeat the bookkeeping for
the final index. The LTA source states the four dependent contracts once. This
small surface compiler is intentionally an executable clarity example; large
recursive languages should be compiled as automata so terms stay symbolic.

### A second dependent example: safe buffer programs

[`Data.CFTA.Gen.Refinement.SafeBufferLanguage`](https://github.com/Tritlo/microecta/blob/main/microcfta-generator/common/Data/CFTA/Gen/Refinement/SafeBufferLanguage.hs) gives
buffers and indexes symbolic integer names, records the surrounding Liquid
environment as solver assumptions, and generates two deliberately partial
operations:

```haskell
safeReads = LTA.node "read-at" validRead $ LTA.do
  buffer <- sourceBuffers
  function <- readFunction
  ~(_, index) <- indexes
  LTA.pure (ReadAt (bufferExpression buffer) index)

validRead buffer function index =
  withActualFor buffer (descendant function [0]) $
    index `isSubtypeOf` descendant function [1]
```

The function's input refinement is `0 <= v && v < n`. Substitution replaces
the formal `n` with the selected buffer-length symbol; Z3 then uses facts such
as `tripleLength = 3` to retain indexes 0, 1, and 2 while rejecting -1 and 3.

The same module demonstrates a two-argument dependent result. Append declares
`resultLength = n + m`, substitutes both selected buffer lengths, and uses
`refinedNodeByRoots` to retain the proven result refinement. A later `head` node can
therefore prove the appended buffer non-empty. The property itself needs no
precondition:

```haskell
withZ3Assuming solverDeclarations solverAssumptions $ \solver -> do
  Right compiled <- LTA.compile solver safePrograms
  quickCheck $ LTA.forAll compiled $ \program ->
    programIsSafe program && safeResult program == Just (runProgram program)
```

The specs enumerate all 14 accepted programs, verify exact append lengths, and
run the partial interpreter through QuickCheck. This is the distinction from
an ECTA key: the accepted combinations depend on arithmetic implication under
an environment, not equality of a finite classification tag.

### Refinement shrinking, similarity, and pools

A refined pool contributes potential local replacements. Compilation asks Z3
whether the current refinement implies each candidate refinement. Strict
implication is a shrink; logically equivalent entries shrink toward the earlier
pool rank to keep the graph acyclic.

The refinement is a trusted annotation on the Haskell value. The generic
library cannot prove that an arbitrary `a` satisfies a Liquid Fixpoint
predicate without an explicit encoding for `a`; callers that require that proof
must validate the encoding before constructing the pool.

Those local replacements are lifted through `node` products. The complete LTA
guard is then decisive: a replacement that makes the whole tree invalid is
never handed to QuickCheck. The compiler follows its shrink edges through that
invalid intermediate and reconnects any valid descendants.

For a two-entry pool ordered as `[nonNegative, exactOne]` and a pair guard
``left `isSubtypeOf` right``, the raw product is:

```text
(0,0)  accepted
(0,1)  rejected: non-negative does not entail exactly-one
(1,0)  accepted
(1,1)  accepted
```

`(1,1)` therefore shrinks first to `(1,0)` and can reach `(0,0)` without ever
emitting `(0,1)`. `samplePool n native` does the same thing for a finite pool
drawn once from a native QuickCheck generator. Repeated draws remain repeated
ranks, retaining empirical weight, while implication supplies semantic shrink
edges.

`compiledSupport` records which lower layer backs the ranked plan.
`AutomatonSupport` contains the LTA returned by semantic pruning;
`RelationalSupport` contains the native hash-consed ECTA built by the grouped
surface compiler. `Data.CFTA.Ranked` and `Data.CFTA.Ranked.QuickCheck` provide
the shared sampling and shrinking machinery. Weights influence sampling but do
not duplicate replay ranks. Transition refinements are part of the support
alphabet, so replay cannot invent a new annotation for an existing constructor.

Similarity minimisation remains separate and opt-in because dropping a
syntactically different value is often the wrong trade-off for testing. Declare
the non-liquid type class when semantic representatives are what you want:

```haskell
Right representatives <-
  LTA.minimizePoolBy solver operationKind candidates
```

`minimizePoolBy` represents the entries as a one-state LTA, invokes the core
`similarity` and `minimize` procedures, then turns the retained transitions back
into a pool. Within each class, a subtype replaces its supertype, equivalent
entries keep the earlier rank, and incomparable entries remain. The generator
therefore does not carry a second imitation of LTA minimization; it is an
adapter over the automaton operation. Ordinary pools are never reduced
implicitly.

### Recursive LTAs

The core accepts recursive LTAs as long as guards do not point into cyclic
states. QuickCheck needs a finite language, so compile with an explicit
tree-height bound:

```haskell
Right compiled <- LTA.compileAutomatonUpToDepth solver 6 recursiveLTA
```

Depth zero keeps nullary transitions. Every parent-to-child edge consumes one
unit, including edges outside a cycle. A negative bound or empty language
returns `EmptyGenerator`. Ranks remain deterministic inside the bounded
language.

The compiler discovers every implication relation inside a pool, which is
quadratic in the number of distinct pool refinements. That is useful for small
semantic universes. A production version should let a native value shrinker
propose a sparse candidate graph for large sampled pools, with Z3 validating
only those edges.

Enter the repository's `nix-shell` to place Z3 on `PATH`, then run the complete
example:

```sh
cabal run cfta-liquid-pairs
```

## Sampling performance

The flagship FTA and ECTA languages each have three exact-uniform generators:

- **naive** generates an unconstrained representation and recognizes or
  rejects it afterwards;
- **bespoke** is a handwritten generator specialized to the language; and
- **FTA/ECTA** compiles the declarative automaton to a rank decoder.

All rows at a given depth therefore sample the same finite language with the
same uniform distribution. This is important: a smaller or biased baseline
would make its speed meaningless. The FTA's naive generator builds a generic
ranked term, recognizes it with a one-state FTA, then decodes it. There is no
semantic condition to reject, so that row is the zero-rejection control. The
ECTA's naive generator creates a raw application at each layer and rejects it
after independent type inference; its root alternatives are weighted by raw
candidate counts, so conditioning preserves uniformity. The bespoke ECTA
generator carries the requested result type through ordinary Haskell.

Every cell runs in a fresh process because the interning tables never evict. The first-sample column includes construction; the throughput and
allocation columns reuse the resulting generator. A complete cell has a
30-second wall-clock limit and successful cells are the median of three runs.

### Ordinary generators: untyped integer expressions

Each successful FTA cell draws 100,000 samples.

| depth | members | engine | first sample | samples/s | alloc/sample | setup mem | retained after 100k |
| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 8 | naive | 0.02 ms | 654,446 | 11.1 KB | 33.6 KB | 35.8 KB |
| 1 | 8 | bespoke | 0.02 ms | 808,100 | 9.9 KB | 1.6 KB | 34.8 KB |
| 1 | 8 | FTA | 0.03 ms | 746,280 | 10.7 KB | 35.3 KB | 36.8 KB |
| 2 | 128 | naive | 0.03 ms | 281,419 | 25.4 KB | 33.9 KB | 36.0 KB |
| 2 | 128 | bespoke | 0.02 ms | 334,263 | 23.6 KB | 33.0 KB | 35.0 KB |
| 2 | 128 | FTA | 0.03 ms | 309,879 | 25.3 KB | 39.1 KB | 45.0 KB |
| 3 | 32,768 | naive | 0.03 ms | 131,340 | 54.0 KB | 34.4 KB | 36.5 KB |
| 3 | 32,768 | bespoke | 0.03 ms | 155,084 | 50.9 KB | 33.5 KB | 35.5 KB |
| 3 | 32,768 | FTA | 0.04 ms | 142,587 | 54.6 KB | 44.9 KB | 77.8 KB |
| 4 | 2,147,483,648 | naive | 0.05 ms | 63,311 | 111.2 KB | 35.4 KB | 37.5 KB |
| 4 | 2,147,483,648 | bespoke | 0.04 ms | 74,049 | 105.7 KB | 34.5 KB | 36.5 KB |
| 4 | 2,147,483,648 | FTA | 0.06 ms | 68,013 | 113.1 KB | 54.8 KB | 208.8 KB |

The control behaves as it should: all three approaches stay close because an
ordinary FTA adds no semantic pruning to this language. The FTA decoder is
within roughly 9% of the direct bespoke generator throughout.

### Equality generators: typed integer and Boolean expressions

Each successful ECTA cell draws 20,000 samples. The smaller fixed workload
keeps depth three measurable while preserving the depth-four rejection
failure; it is still large enough for stable normalized rates.

| depth | members | engine | first sample | samples/s | alloc/sample | setup mem | retained after 20k |
| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 42 | naive | 0.02 ms | 155,435 | 49.1 KB | 33.5 KB | 35.6 KB |
| 1 | 42 | bespoke | 0.02 ms | 533,874 | 14.1 KB | 3.1 KB | 41.5 KB |
| 1 | 42 | ECTA | 0.04 ms | 2,147,075 | 3.6 KB | 37.0 KB | 37.8 KB |
| 2 | 27,054 | naive | 0.08 ms | 17,013 | 449.0 KB | 34.3 KB | 36.5 KB |
| 2 | 27,054 | bespoke | 0.04 ms | 194,865 | 38.3 KB | 37.4 KB | 105.9 KB |
| 2 | 27,054 | ECTA | 0.06 ms | 1,765,381 | 3.8 KB | 47.4 KB | 58.5 KB |
| 3 | 8,887,065,932,466 | naive | 0.30 ms | 2,528 | 2.93 MB | 35.1 KB | 37.3 KB |
| 3 | 8,887,065,932,466 | bespoke | 0.10 ms | 67,956 | 112.4 KB | 50.1 KB | 304.5 KB |
| 3 | 8,887,065,932,466 | ECTA | 0.08 ms | 947,239 | 5.8 KB | 62.0 KB | 137.4 KB |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | naive | **timeout (30s)** | — | — | — | — |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | bespoke | 0.60 ms | 21,942 | 335.9 KB | 83.9 KB | 850.4 KB |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | ECTA | 0.14 ms | 367,532 | 12.8 KB | 98.7 KB | 334.4 KB |

At depth three the ECTA decoder is about 375x faster than rejection and 14x
faster than the bespoke generator, allocating about 517x and 19x less per
sample respectively. At depth four, rejection cannot complete the fixed cell;
the ECTA remains about 17x faster than the bespoke implementation. The setup
cost stays below 0.15 ms because the finite dependency structure is
compiled once and every later sample is one rank decode.

Measured with GHC 9.12.2 and `-O2` on the maintainer's Apple Silicon machine on
2026-09-02. An empty generator ran at about 16.4M draws/s and one `chooseInt`
at 2.7M draws/s during the ECTA run. Rates move a few percent between runs and
with the QuickCheck and `random` versions in use. Reproduce one table, or all
four repository tables, with:

```sh
cabal bench microcfta-generator:untyped-expression-speed --enable-optimization=2
cabal bench microcfta-generator:typed-expression-speed --enable-optimization=2
./scripts/benchmark-generators.sh
```

### Refinement generators: typed state-machine traces

The recorded measurements in this section and the equality-theory comparison
below predate the standard-tree migration. They used the earlier `LiquidTerm`
representation. Run the benchmark commands below to measure the current code.

The typed stack-machine benchmark separates seven useful paths:

- **naive** draws uniformly from all nine raw commands at every position and
  rejects the complete sequence if abstract replay fails;
- **QSM online** follows the normal state-machine-testing shape: choose a
  command admitted by the current model, advance the model, and continue;
- **bespoke** is ordinary compositional QuickCheck code which weights every
  valid next command by its number of complete suffixes;
- **ranked** is the strongest handwritten control: it duplicates the count and
  global-unrank algorithm in application code and constructs `Trace` directly;
- **LTA do** preserves the qualified-do recipe, groups its live refinement
  observations, and lowers solver-approved tuples through ECTA joins;
- **LTA materialized** prunes the explicit automaton, constructs a selected
  `Tree LiquidSymbol`, then decodes it to `Trace`;
- **LTA fused** uses the same explicit automaton but folds a selected run
  directly into `Trace`.

Naive rejection, bespoke, ranked, and all three LTA rows are uniform over the
same exact trace language. QSM online has the same support but intentionally has
a different distribution: choosing uniformly at each prefix gives extra
probability to traces passing through states with fewer valid continuations.
That is usually the right engineering trade in state-machine testing. As in
[quickcheck-state-machine](https://well-typed.com/blog/2019/01/qsm-in-depth/),
the complete trace is generated before execution; after a failure,
`qsmTraceShrinks` removes commands and replays the remainder so dependencies
whose producers disappeared are rejected.

Each successful cell draws 20,000 traces. It runs in a fresh process with a
30-second wall-clock limit and is the median of three runs. The first-sample
column includes all setup—in an LTA row, that includes starting Z3, compiling
the semantic constraints, building the rank index, and drawing once.
Steady-state sampling is pure. After an engine times out at one length, the
harness skips its larger cells and reports `after timeout`.

The crossover and deep-scaling rows are:

| length | members | engine | first sample | samples/s | alloc/sample | setup mem | retained after 20k |
| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 8 | 342,136 | naive | 0.07 ms | 6,280 | 1.23 MB | 33.3 KB | 35.3 KB |
| 8 | 342,136 | QSM online | 0.02 ms | 179,795 | 42.6 KB | 32.7 KB | 34.7 KB |
| 8 | 342,136 | bespoke | 0.07 ms | 127,266 | 37.5 KB | 47.6 KB | 32.91 MB |
| 8 | 342,136 | ranked | 0.06 ms | 394,719 | 11.7 KB | 41.4 KB | 43.4 KB |
| 8 | 342,136 | LTA do | 71.08 ms | 277,200 | 19.4 KB | 1.18 MB | 1.20 MB |
| 8 | 342,136 | LTA materialized | 356.54 ms | 112,936 | 58.0 KB | 199.4 KB | 175.8 KB |
| 8 | 342,136 | LTA fused | 355.83 ms | 111,456 | 56.3 KB | 199.6 KB | 176.0 KB |
| 10 | 8,567,224 | naive | 0.20 ms | 1,913 | 3.97 MB | 33.4 KB | 35.5 KB |
| 10 | 8,567,224 | QSM online | 0.03 ms | 139,808 | 53.6 KB | 32.7 KB | 34.7 KB |
| 10 | 8,567,224 | bespoke | 0.10 ms | 69,854 | 57.5 KB | 54.3 KB | 74.04 MB |
| 10 | 8,567,224 | ranked | 0.07 ms | 302,517 | 14.3 KB | 43.2 KB | 45.3 KB |
| 10 | 8,567,224 | LTA do | 88.30 ms | 233,495 | 23.6 KB | 1.47 MB | 1.52 MB |
| 10 | 8,567,224 | LTA materialized | 430.83 ms | 89,208 | 72.1 KB | 227.4 KB | 203.8 KB |
| 10 | 8,567,224 | LTA fused | 422.05 ms | 91,050 | 69.3 KB | 227.6 KB | 203.9 KB |
| 12 | 215,809,688 | naive | **timeout (30s)** | — | — | — | — |
| 12 | 215,809,688 | QSM online | 0.03 ms | 118,229 | 64.5 KB | 32.7 KB | 34.7 KB |
| 12 | 215,809,688 | bespoke | 0.10 ms | 52,289 | 77.4 KB | 56.6 KB | 118.24 MB |
| 12 | 215,809,688 | ranked | 0.08 ms | 253,498 | 16.0 KB | 45.1 KB | 47.1 KB |
| 12 | 215,809,688 | LTA do | 101.66 ms | 191,694 | 26.9 KB | 1.78 MB | 1.84 MB |
| 12 | 215,809,688 | LTA materialized | 486.62 ms | 74,372 | 85.4 KB | 255.1 KB | 231.5 KB |
| 12 | 215,809,688 | LTA fused | 490.85 ms | 76,824 | 81.5 KB | 255.2 KB | 231.6 KB |
| 20 | 90,356,263,022,904 | QSM online | 0.04 ms | 68,492 | 108.4 KB | 32.7 KB | 34.7 KB |
| 20 | 90,356,263,022,904 | bespoke | 0.15 ms | 23,546 | 157.6 KB | 73.9 KB | 303.87 MB |
| 20 | 90,356,263,022,904 | ranked | 0.12 ms | 140,412 | 25.1 KB | 52.5 KB | 54.6 KB |
| 20 | 90,356,263,022,904 | LTA do | 167.76 ms | 121,021 | 42.6 KB | 3.02 MB | 3.13 MB |
| 20 | 90,356,263,022,904 | LTA materialized | 748.54 ms | 45,329 | 143.6 KB | 372.8 KB | 349.2 KB |
| 20 | 90,356,263,022,904 | LTA fused | 758.00 ms | 46,578 | 132.7 KB | 373.0 KB | 349.4 KB |
| 40 | 11,207,052,560,775,737,667,197,734,440 | QSM online | 0.05 ms | 34,359 | 218.0 KB | 32.7 KB | 34.7 KB |
| 40 | 11,207,052,560,775,737,667,197,734,440 | bespoke | 0.32 ms | 8,494 | 365.0 KB | 122.1 KB | 778.94 MB |
| 40 | 11,207,052,560,775,737,667,197,734,440 | ranked | 0.23 ms | 57,282 | 50.7 KB | 76.4 KB | 78.4 KB |
| 40 | 11,207,052,560,775,737,667,197,734,440 | LTA do | 333.75 ms | 59,187 | 84.0 KB | 6.15 MB | 6.41 MB |
| 40 | 11,207,052,560,775,737,667,197,734,440 | LTA materialized | 1,411.81 ms | 21,378 | 307.7 KB | 653.1 KB | 629.5 KB |
| 40 | 11,207,052,560,775,737,667,197,734,440 | LTA fused | 1,416.92 ms | 22,158 | 263.8 KB | 653.2 KB | 629.6 KB |

The ordinary bespoke generator wins at very short lengths, but LTA do overtakes
it after length four. At length 40 the generic relational compiler produces
59,187 traces/s versus 8,494/s: a 7.0x throughput win, while retaining 6.41 MB
rather than 778.94 MB after the fixed workload. It pays 334 ms once, then reuses
the compiled ECTA rank plan instead of rebuilding weighted QuickCheck choices
through every generated suffix.

The hand-ranked row remains the specialization ceiling. At length 40 it is
within 4% of LTA do in throughput and allocates only 50.7 KB per trace versus
84.0 KB. Treat that throughput difference as a tie, not a claim that a generic
compiler has defeated its own hand-coded algorithm. QSM online is the pragmatic
state-machine baseline: LTA do is 1.7x faster in this run and remains uniform
over complete traces, at the cost of a solver-backed setup phase and a larger
retained rank index.

Naive rejection cracks at length 12 for the 20,000-sample workload. At length
10 it is already 122x slower than LTA do and allocates 3.97 MB per accepted
trace.

The first benchmark run made repeated solver work visible: length four took
6.50 seconds to compile and length five timed out, despite only 115 distinct
entailment requests among 34,073 requests at length four. Caching exact
obligations for one compile and checking a generated witness directly, rather
than first turning it into a singleton automaton, cut length-four setup to 188
ms and made length five complete in 1.94 seconds.

Replacing the outcome lists with `PlanAp` removed product allocation but did
not remove the work: the old surface compiler still visited `11^6 = 1,771,561`
ranks to discover 13,760 valid traces. Retaining the applicative recipe changes
that algorithm. Children are grouped by only the refinements their parent
observes; the solver selects live key tuples, and the equality counter counts
their products
without visiting members. The same qualified-do source now reaches length 40.

The direct automaton rows isolate decoding cost. At length 40, fusing the
bottom-up `Trace` decoder saves 43.9 KB per sample—14.3%—and gives a small
throughput improvement over materializing and immediately traversing the
earlier `LiquidTerm`. The remaining gap is in generic automaton unranking. Conversely,
LTA do's retained relational index uses 6.15 MB of setup memory versus about
653 KB for the direct automaton; reducing that compact-index constant and using
a persistent worklist in automaton pruning are the next focused opportunities.

### Equality theory cost: ECTA versus LTA

The typed-expression flagship also has a deliberately equivalent liquid
encoding in
[`Data.CFTA.Gen.Refinement.EqualityTypedExpressionLanguage`](https://github.com/Tritlo/microecta/blob/main/microcfta-generator/common/Data/CFTA/Gen/Refinement/EqualityTypedExpressionLanguage.hs).
`TInt` is the refinement `v = 0` and `TBool` is `v = 1`. Each application LTA
contains candidate ground child states, and Z3 retains precisely those whose
refinements imply the operation's expected input equalities. This expresses the
same language as the ECTA's path-equality join without adding LTA-only power.

This control uses the same rank order and fixed QuickCheck seed for both
engines, draws 20,000 values per cell, and forces the complete expression tree.
The checksum matched at every depth, in addition to the LTA cardinality being
checked against the independent ECTA count.

| depth | members | engine | first sample | samples/s | alloc/sample | setup mem | retained after 20k |
| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 42 | ECTA | 0.05 ms | 2,158,429 | 3.6 KB | 36.9 KB | 37.7 KB |
| 1 | 42 | LTA equality | 4.16 ms | 1,082,720 | 6.9 KB | 61.7 KB | 38.1 KB |
| 2 | 27,054 | ECTA | 0.06 ms | 1,719,247 | 3.8 KB | 47.3 KB | 58.4 KB |
| 2 | 27,054 | LTA equality | 5.08 ms | 427,881 | 15.7 KB | 63.4 KB | 39.8 KB |
| 3 | 8,887,065,932,466 | ECTA | 0.08 ms | 878,966 | 5.8 KB | 61.9 KB | 137.3 KB |
| 3 | 8,887,065,932,466 | LTA equality | 5.25 ms | 143,836 | 44.8 KB | 65.2 KB | 41.6 KB |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | ECTA | 0.16 ms | 323,076 | 12.8 KB | 98.6 KB | 334.3 KB |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | LTA equality | 5.28 ms | 53,521 | 134.1 KB | 66.9 KB | 43.3 KB |

For equality alone, the ECTA is the right tool. Its setup stays below 0.2 ms;
the LTA pays about 4–5.3 ms to start Z3 and prune the guarded graph. The LTA
sampler is 2.0x slower at depth one and 6.0x slower at depth four, with 10.5x
the per-sample allocation at depth four. That allocation is the cost of
constructing an annotated `LiquidTerm` and decoding it to the same Haskell AST.
The language itself remains symbolic: even the roughly 4.95e38-member
depth-four language occupies only about 67 KB of LTA setup memory.

Measured with GHC 9.12.2 and `-O2` on the maintainer's Apple Silicon machine on
2026-09-03. Reproduce either LTA table, or all four repository tables, from the
repository root with:

```sh
cabal bench microcfta-generator:state-machine-trace-speed --enable-optimization=2
cabal bench microcfta-generator:typed-expression-constraint-cost --enable-optimization=2
./scripts/benchmark-generators.sh
```

## Concurrency

Safe. Generators build automata, and `microcfta` interns nodes through
process-global tables, which are synchronized.

This matters here more than it sounds, because this is a testing library and
test runners parallelize: `tasty` runs independent tests concurrently by
default when the test binary is linked with `-threaded` and run with `+RTS -N`,
and `hspec` does under `parallel`. A property drawing from an
`ECTAGen` can be run that way without anything in your code looking
concurrent. Against `microecta` 0.1.0.0 that was silent corruption rather than
a crash; see the concurrency note in the `microcfta` README.

## Dependencies

The library depends on `microcfta`, `QuickCheck`, `array`, `containers`,
`hashable`, `mtl`, and `text`; the benchmarks additionally use `random` and
`process`. The refinement generator and its tests need `z3` on `PATH`.

## Build

From the repository root:

```sh
cabal build microcfta-generator
cabal test microcfta-generator
```

The package has three test suites, `plain-tests`, `equality-tests`, and
`refinement-tests`; the last one needs `z3`. `-j1` keeps an optimized build of
the core inside a small machine's memory.
