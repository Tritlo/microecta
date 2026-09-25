# microcfta-generator

Ranked generation, random sampling, replay, and shrinking for the automata of
[`microcfta`](../microcfta/README.md), with QuickCheck integration. There is
one generator type, `Gen symbol constraint a`, and one facade per constraint
theory:

| Module | Purpose |
| --- | --- |
| `Data.CFTA.Gen` | The generator: sources, constructors, choices, joins, recursion, imported automata and datatypes, exact inspection, replay, and shrinking, for every theory. |
| `Data.CFTA.Gen.QuickCheck` | Sampling and properties over a generator, and frozen pools. |
| `Data.CFTA.Gen.Do` | Qualified applicative do-notation, re-exported by the three `QuickCheck` facades; `FTAGen.do`, `ECTAGen.do`, and `LTAGen.do` are this module under the facade's alias. |
| `Data.CFTA.Gen.Error` | The one failure vocabulary, and `explain`. |
| `Data.CFTA.Gen.Equality` | `ECTAGen`: the `EqConstraints` theory, and imports ranked by symbol text. |
| `Data.CFTA.Gen.Equality.QuickCheck` | Re-exports `Data.CFTA.Gen.Equality` with the QuickCheck functions. |
| `Data.CFTA.Gen.Refinement` | `LTAGen`: inferred and refined pools, values without a pool with `every`, conditions with `satisfying`, contracts with `guarded`, liquid imports, `compile`, and `validOutcomes`. |
| `Data.CFTA.Gen.Refinement.QuickCheck` | Re-exports `Data.CFTA.Gen.Refinement` with the QuickCheck functions. |
| `Data.CFTA.Ranked`, `Data.CFTA.Ranked.QuickCheck` | Finite ranks, weighted sampling, replay, and structural shrinking, independent of automata. |
| `Data.CFTA.Gen.Internal.*`, `Data.CFTA.Ranked.Internal.*` | The engine: static and recursive languages, joins, symbolic counting, decoders, samplers, sizes, and shrinking; exposed for integration, not covered by the PVP contract. |

An ordinary generator is `FTAGen symbol a`, that is `Gen symbol ()`. The
equality facade fixes the theory in `ECTAGen a`, the refinement facade in
`LTAGen a`; both re-export
`Data.CFTA.Gen`, so `node`, `oneof`, `cardinality`, `unrank`, and `forAll`
are the same functions in every theory. See
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
It also constructs the same language as an interned `Common.PlainNode String`,
imports it with `fromAutomaton`, and checks the imported generator.

`FTAGen.node "pair"` closes an applicative child block with one constructor.
Each binding supplies one direct child. Enable `ApplicativeDo` and
`QualifiedDo`, and finish the block with `FTAGen.pure`. Child generators must be
independent. `leaf value symbol` is a constructor without children, and
`oneof` and `frequency` choose between generators; an empty alternative is
skipped, not an error.

`fromAutomaton` reads an interned automaton as a generator of the terms it
accepts. An acyclic automaton gives a finite generator with one rank per
distinct term: where alternatives overlap or an equality reaches below
direct children, the count is symbolic, and ranks order constructors by the
symbol's `Ord`. A cyclic automaton gives a recursive generator counted by
size, the number of term nodes; it must be unambiguous, because its count
sums over accepting runs. `fromAutomatonUpToDepth` bounds the automaton by
constructor depth first, a leaf having depth zero, and `upToSize` bounds any
generator to the members of at most a given number of source choices, in
size-major rank order. Use `Data.CFTA.Interned.fromFTA` first when the source
is an explicit-state automaton; the import is total and retains shared states.

`fromDatatype` reads a derived grammar as a generator of its values,
recursive when the datatype is, and `fromDatatypeUpToDepth` bounds it by
constructor depth. The value and its constructor term share one rank, and
the codec runs only when a selected value is demanded. Depth counts
constructors, including primitive fields: a `Leaf Bool` term has depth one
and two tree nodes.

`Data.CFTA.Ranked` is independent of automaton representation. `Indexed`
describes a finite rank domain, and `fromIndexed` is the generator over it.
Counting and replay do not require enumerating the entire source.

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

import qualified Data.CFTA.Gen as FTAGen
import Data.CFTA.Generic (HasFTA, deriveFTAWith, domain)

-- | Arithmetic expressions with integer literals.
data Expr = Lit Int | Add Expr Expr
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | Print every expression in a depth-bounded language.
main :: IO ()
main = do
    datatype <- either (fail . show) pure $ deriveFTAWith @Expr (domain @Int [0, 1])
    let language = FTAGen.fromDatatypeUpToDepth 3 datatype
    expressions <- FTAGen.orFail $ FTAGen.values language
    mapM_ print expressions
```

Add both `microcfta` and `microcfta-generator` to your component's
`build-depends`. In this checkout, save the program as `Main.hs` at the
workspace root and run:

```sh
cabal build microcfta-generator
cabal exec -- ghc -package microcfta -package microcfta-generator -e main Main.hs
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
the member at a zero-based rank, and `values` lists every member in rank order.
The example prints all 38 expressions. `orFail` stops the program with the
`explain` text when the language cannot be listed.

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
ranks identify distinct terms; an ambiguous handwritten grammar is counted
symbolically, so one term still has one rank.

For another complete example, see
[`FinitePairs.hs`](examples/FinitePairs.hs), or run
`cabal run cfta-pairs` from the workspace root.

## Equality-constrained generators

An equality generator is `Gen Symbol EqConstraints`, written `ECTAGen`. Its
transparent regions retain an exact equality-constrained support,
cardinality, and replay rank; the QuickCheck functions add sampling, opaque
fallbacks, and structural shrinking. Run the complete introductory example
from the workspace root with `nix-shell --run 'cabal run cfta-finite-languages'`.

Import the QuickCheck-facing API:

```haskell
import Data.CFTA.Gen.Equality.QuickCheck (ECTAGen)
import qualified Data.CFTA.Gen.Equality.QuickCheck as ECTAGen
```

The QuickCheck facade re-exports the qualified do-notation, so `ECTAGen.do`
and `ECTAGen.pure` sit next to `ECTAGen.node`; the ordinary and refinement
facades give `FTAGen.do` and `LTAGen.do` the same way.

### Generator API

`fromAutomatonUpToDepth` reads an equality-constrained automaton, a
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
selected term. `fromAutomaton` reads an acyclic automaton the same way, and a
cyclic one as a recursive generator counted by size.

`elements` and `fromIndexed` turn a finite indexed source into an ECTA whose leaves contain
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
large languages. The snippets in this section are fragments of one complete
program, the typed-expression flagship
[`Data.CFTA.Gen.TypedExpressionLanguage`](https://github.com/Tritlo/microecta/blob/main/microcfta-generator/common/Data/CFTA/Gen/TypedExpressionLanguage.hs);
read it as a whole when the pieces below are not enough. The `key` is the type returned by the classifier and used to
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
group by group, so alternated layers stay grouped. `uniformlyGrouped`
combines grouped generators in proportion to their exact cardinalities, so
every member of the union is equally likely, which is what a layered
language wants; `uniformly` does the same for flat generators. The
expressions of depth at most `n` are one such union, with no count computed
by hand:

```haskell
upToDepthByType 0 = literalsByType
upToDepthByType depth =
  ECTAGen.uniformlyGrouped
    [literalsByType, applicationLayer (upToDepthByType (depth - 1))]
```
 `ungroup` returns an ordinary `ECTAGen` with
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

Both layers also support qualified do-notation through `Data.CFTA.Gen.Do`,
imported qualified under the generator's alias. Enable `QualifiedDo` together
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
forces the complete symbolic representation, a `Node (Label Symbol) EqConstraints`:
`Label` wraps the user's symbols, and the other constructors of
`Data.CFTA.Gen.Label` are the engine's private labels for the applicative
spine, choices, source indexes, joins, keys, and recursive families.

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
integers = FTAGen.namedElements [("zero", 0), ("one", 1)]

-- | Apply a named function to the integer source.
incremented :: Gen.ECTAGen Int
incremented = FTAGen.namedElements [("increment", (+ 1))] <*> integers
```

`FTAGen.inspect incremented` returns an `Inspection`, and `drawInspection` draws
it as an ASCII tree. Its `inspectionGraph` is a
`Node (InspectionSymbol Symbol) EqConstraints`. For another rendering, pass it
to `ECTA.toTree`, then render the typed labels with `fmap` and
`Data.Tree.drawTree`. Each `InspectionSymbol` retains
`originalSymbol`, a `Label Symbol`, and an optional `displayLabel`. `inspectionName` holds a group
name when one is available. `ViewPath` locations belong to the graph passed to
`toTree`.

Source names describe source choices. `fmap` preserves those names; it does not
infer names for mapped results. `regroupBy` clears old group names because the
keys change. Apply `nameGroups` after regrouping to name the new keys. Source
names remain available through grouping, application, and recursion.

The diagnostic graph preserves construction structure and equality obligations.
Names distinguish occurrences that share one semantic node, such as integer
and Boolean sources with the same rank indices. The graph does not run equality
reduction. Use `FTAGen.support` for membership and other semantic operations.

Counts and rank decoding do not evaluate display names or construct the
diagnostic graph. Retaining the extra fields and closures still uses memory.
Inspecting the graph also allocates its nodes and formatted names.

Run `cabal run cfta-draw-typed-expressions` to draw the actual finite and recursive
expression generators. The [example](examples/DrawTypedExpressions.hs) calls
`drawInspection`, which shows source choices such as `Add :: Int -> Int -> Int`
and `IntLiteral 0 :: Int`, with `Int` and `Bool` labels on the equality witnesses.

#### Read the ASCII tree

The drawing alternates between state lines (`q0`, `q1`, ...) and transition
lines (`choice 0`, `"if"`, `Add :: Int -> Int -> Int`, ...). A transition
shows its display name when it has one. Otherwise it shows its symbol with
`show`, so a `Symbol` appears in quotes, or a short name for a construction
step, such as `choice 0`. At a state, choose one transition alternative. A
chosen transition uses all of its child states in order. For example, the two
alternatives below `q5` select `Add` or `Multiply`; the children below
`"binary-application"` supply its operation and both arguments.

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
| `0:1` | `q9` | `0`: `"if"` | `1`: the condition argument | `q14` |

The location is stored as `[(1, 0), (0, 1)]` in `viewPath`. The child indexes
include the operation: below `"if"`, child `0` holds the operation, child `1`
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
`"binary-application" [0.1 = 2.0, 0.0 = 1.0]`, each dot-separated path starts at
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
of the terms it accepts, with the automaton itself as the support. An
acyclic automaton is a finite generator, as above; a cyclic one is a
recursive generator, counting terms by size — the number of term nodes.

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
`groupBy` all work on `upToSize n (fromAutomaton node)`, and so does
`termAt` on a mapped one.

The recursive count does not count equality constraints. They correlate an
edge's children, so the edge's count is the size of an intersection rather
than a product of the children's counts; a cyclic automaton carrying them is
rejected with `CannotCountConstrainedEdges` rather than miscounted. Bound
the automaton first: the finite import counts equalities exactly.

Nor does it count ambiguity. A node's count is the sum over its edges, which
counts accepting *runs*, so a node with two edges that accept a common term
would count that term twice and `unrank` would return it at two ranks. Every
reachable node is checked, and an ambiguous cyclic automaton is rejected
with `AmbiguousAutomaton`. Two edges overlap when they share a symbol and
arity and every child position has a non-empty intersection, which without
constraints is exactly when they share a term. The finite import counts an
ambiguous automaton symbolically instead.

`fromIndexed` is the transparent boundary for a FEAT-style finite enumeration:
it needs only a cardinality and a stable function from an integer index to a
value. `elements` is the corresponding list convenience function.

`Data.CFTA.Ranked.fromIndexedOnDemand` is the automaton-adapter variant. It keeps
the same cardinality, ranks, and sampler but never tabulates a small indexed
source while compiling its replay decoder. Symbolic counting uses it so the
automaton remains a graph until one rank is selected.

`samplePool n native` bridges a large or infinite QuickCheck source into this finite
world. Its outer `Gen` samples `n` values once and returns an `ECTAGen` whose
ranks are those draws. The result supports exact inspection and constrained
joins. Repeated draws remain repeated ranks and therefore retain their
empirical weight. Reuse the returned generator when two choices must range over
the same frozen universe.

`freeze seed n native` is `samplePool` with the draws fixed by a seed, so it is an
ordinary transparent generator rather than a `Gen` of one: it can be weighted
by `uniformly`, keyed, joined, replayed, and shrunk, and its ranks are the same
in every run under the same seed. The native generator runs at QuickCheck size
30, the default of `generate`; use `resize` on it for another size.

Every failure is a `GenError`. The derived `Show` names the case, and
`explain` says what it means and which combinator resolves it; sampling a
generator that could not be built raises both together. `orFail` turns a
`GenError` result into a failure with the `explain` text, for `main` and tests.

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

A refinement generator is `Gen LiquidSymbol LiquidConstraint`, written
`LTAGen`. Each value carries a refinement, a formula that the solver knows
about it. A condition on one child goes where the child is drawn, with
`satisfying`. A relation between children is the contract of a `guarded`
node. Call `compile` once, then use pure sampling, replay, and shrinking.
Compilation keeps symbolic counts and constructs selected values on demand.

### A complete first program

This program generates safe divisions. The solver removes the zero
denominator before the division is evaluated.

```haskell
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}

import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTAGen
import Data.CFTA.Refinement.Expression ((./=))
import qualified Test.QuickCheck as QC

divisions :: LTAGen.LTAGen (Integer, Integer)
divisions = LTAGen.node "divide" $ LTAGen.do
    d <- LTAGen.elements [0 .. 5] `LTAGen.satisfying` (\v -> v ./= 0)
    LTAGen.pure (d, 12 `div` d)

main :: IO ()
main = do
    gen <- LTAGen.compile divisions
    print (LTAGen.values gen)
    QC.quickCheck $ LTAGen.forAll gen $ \(d, q) -> d /= 0 && q == 12 `div` d
```

Use the packages `base`, `microcfta`, `microcfta-generator`, and `QuickCheck`.
Install Z3 and put it on `PATH`. The program prints
`Right [(1,12),(2,6),(3,4),(4,3),(5,2)]`.

A refinement is a Haskell function of the value, such as `\v -> v ./= 0`. Its
terms take integer literals and arithmetic, as in `\v -> v .== 2 * n + 1`. The
logic has the comparisons `.==`, `./=`, `.<`, `.<=`, `.>`, and `.>=`, and the
connectives `.&&`, `.||`, and `lnot`. `elements` gives each integer `x` the
refinement `\v -> v .== literal x`, so the solver knows each value exactly.
`satisfying` keeps the terms whose refinement implies the condition. The
solver declares every free name as an integer.

Run the checked introductory example from the workspace:

```sh
nix-shell --run 'cabal run cfta-safe-division'
```

### Refined pools and contracts

A pool can say less than the value. Then the solver knows only what the pool
says:

```haskell
ranged :: [(Integer, Refinement)]
ranged =
    [ (1, \v -> 0 .<= v .&& v .< 2)
    , (3, \v -> 2 .<= v .&& v .< 4)
    , (5, \v -> 4 .<= v .&& v .< 6)
    ]

below :: Expr -> Expr -> Formula
below left right = left .< right

pairs :: LTAGen.LTAGen (Integer, Integer)
pairs = LTAGen.guarded "pair" below $ LTAGen.do
    left <- LTAGen.pool ranged
    right <- LTAGen.pool ranged
    LTAGen.pure (left, right)
```

`pool` takes values with their refinements and names each entry by `show`.
`guarded` closes the block with a contract: a function with one term for each
child, in order. The solver proves each conjunct of the contract, and assumes
the refinement of each child that the conjunct names. Here the ranges order three pairs: `(1,3)`, `(1,5)`, and
`(3,5)`. The contract names the children as a function signature names its
parameters, and the do-block binds their values.

The generator trusts a pool's refinements. It does not inspect a Haskell value
to prove its refinement. `checkPool solver ranged` asks the solver to prove
each refinement for its value, and returns the values that it cannot prove.
[`LiquidPairs.hs`](https://github.com/Tritlo/microecta/blob/main/microcfta-generator/examples/LiquidPairs.hs)
runs this program with `checkPool`, and CI runs it with the other examples.
`compileAssuming` adds ambient facts, such as `[variable "input" .== 2]`, that
the solver may assume. `compileWith` takes a solver from `withZ3`, to share one
solver between several generators, and returns the error instead of failing.
Mapping a generator changes its Haskell value and retains the term and
refinement that justify its conditions.

### Values without a pool

`every` draws every value of a type, each refined as itself, as `elements`
refines its members. On this leaf, a condition narrows the values, and a
contract over such children keeps the tuples that it admits. `compile` counts
them without enumeration and without the solver:

```haskell
boundedReads :: LTAGen.LTAGen (Integer, Integer)
boundedReads = LTAGen.guarded "read-at" (\n i -> 0 .<= i .&& i .< n) $ LTAGen.do
    n <- LTAGen.every `LTAGen.satisfying` (\v -> 1 .<= v .&& v .<= 1000000)
    i <- LTAGen.every `LTAGen.satisfying` (\v -> (-10) .<= v .&& v .<= 1000000)
    LTAGen.pure (n, i)
```

The signature makes both children `Integer`, which is unbounded, so the
conditions bound them. Where nothing fixes the type, write `every @Integer`.
The compiled generator has 500,000,500,000 members. Ranks follow the
lexicographic order of the children, so rank 0 is `(1,0)` and the last
rank is `(1000000,999999)`. Sampling decodes one rank at a time, and a shrink
goes to an earlier rank. Each member's term has the exact leaf of each
value, as `elements` gives.

The conditions and the contract must be linear, with integer coefficients, and
each integer must be bounded. `Data.CFTA.Refinement.Lattice` counts the
integer points of such a formula exactly: it sums the variables out with
Faulhaber polynomials, as in Pugh, "Counting solutions to Presburger formulas"
(PLDI 1994), and it decodes a rank with one binary search for each variable.
When it sums a variable out, each bound must have the coefficient one or minus
one on that variable. A contract can also name a child from `elements`, whose
refinement fixes one integer. A domain that the counter cannot count gives
`UncountableIntegers`. Another guard on a child from `every`, a computed
label, and a guard of an enclosing constructor that reads such a child give
`IntegerLeafRead`.
[`BoundedReads.hs`](https://github.com/Tritlo/microecta/blob/main/microcfta-generator/examples/BoundedReads.hs)
runs this program, and CI runs it with the other examples.

`every` takes every type that integers stand for: `Integer`, `Word8`, `Char`,
`Bool`, another integral type, or an enumeration that derives `Literal` via
`Enumerated`. A bounded type needs no condition. A condition or a contract
reads a value as its integer, so it compares the value with a `literal`, as in
`(./= literal Red)`.
[`docs/symbolic-values.md`](../docs/symbolic-values.md) explains the types,
what `compile` can count, and how the counter works, and
[`TypedValues.hs`](https://github.com/Tritlo/microecta/blob/main/microcfta-generator/examples/TypedValues.hs)
relates a color, a brightness byte, and a flag in one contract.

### Construction and compilation

`elements` and `pool` choose uniformly. `namedPool` takes
`Refined value symbol refinement` atoms with explicit symbols, and `leaf` is one
such atom. Repeated entries are repeated ranks. `oneof` and `frequency` are the
generic choices: `frequency` weights its branches as QuickCheck's does, and
skips an empty branch.

Each qualified do-block describes independent direct children, and its
adjacent `node` or `guarded` supplies the constructor. A contract must take
exactly one argument per child; write `_` for an unused child. An
argument-count mismatch is a construction error, including when the source is
empty. `satisfying` applies to the root of the generator it follows: a pool, a
leaf, a node, a bounded import, a choice of these, or a mapped generator. A
condition names only `v` and ambient names; a relation between children
belongs in a contract.

`node` and `guarded` use the universal result refinement. `refinedNode`
supplies a fixed result refinement, and `refinedNodeByRoots` computes one from
the labels of the children, a list of `LiquidSymbol`. Both take a positional
guard from `Data.CFTA.Refinement.Guard`. That is the form of the paper's
encodings, where a function type is a subtree of the term: for example
``actual `isSubtypeOf` expected``, ``argument `requires` refinement``, or
`withActualFor actual formal dependentResultCheck`. `descendant argument [1]`
selects the argument's second child. Raw `LiquidConstraint` values remain
available and retain the paper's Boolean meaning for missing paths.

A constructor without a condition or a contract is built at once, like any
other generator. A constructor that needs the solver defers the generator: `cardinality`,
`unrank`, and `support` report `SourceRequiresCompilation` until `compile`
has decided every guard. `compile` folds the generator's construction once,
with the solver. Each child language is grouped by the observations its
parent guard reads: the label at the child's root, and at deeper paths the
guard names. The solver decides the guard once per tuple of child groups,
and the accepted tuples become one join per constructor. No candidate is
built to decide a guard, so the accepted language can be larger than a
machine integer. Groups are ordered by the first member that has their
observations, so ranks keep source order.

`isSameTermAs` normally requires exact subtree equality. Inside `withActualFor`,
it compares views with the formal symbol replaced by the actual symbol,
including free variables in refinement annotations. The generated terms and
values stay unchanged. Several replacements in `withActualsFor` apply
simultaneously. Compilation can decide this scoped equality on observed leaves.
Scoped equality on compound subtrees remains unsupported by the compiler.

The result of `compile` is an ordinary finite generator: `cardinality`,
`unrank`, `termAt`, `support`, `shrinkRank`, and `smallerMembers` work on it,
and sampling, replay, and shrinking make no solver calls. `termAt` returns
the engine's labelled term; `surface` reads the accepted liquid term under
it. An undecidable guard, a guard the observations cannot decide, and a
guard the symbolic counter cannot count are compile failures, each
explained by `explain`; an empty language is not a failure. Ranks are
deterministic for a fixed generator. A changed pool, bound, or
specification can change them.

### Import an LTA

`fromAutomaton` reads a liquid automaton, and `fromAutomatonUpToDepth` bounds
it first by tree height, leaves having height zero. An automaton whose guards
the engine can count is read at once, with one rank per distinct accepted
term: Boolean equality between subterms, nested equalities, negation,
disjunction, and overlapping alternatives are counted symbolically. An
automaton with guards that need the solver waits for `compile`, which prunes
it first. Both compose with ordinary sources:

```haskell
boundedTerms = LTAGen.fromAutomatonUpToDepth 6 automaton

wrapped = LTAGen.node "wrap" $ LTAGen.do
  term <- boundedTerms `LTAGen.satisfying` desiredRefinement
  LTAGen.pure (decode term)

compiled <- LTAGen.compile wrapped
```

Under a guard, the pruned automaton is split by the observations the guard
reads, so an import stays a graph until one rank is selected. An empty or
negative-bound import is an empty source and can occur beside a nonempty
alternative. A guard that remains after pruning and that the symbolic
counter cannot count is reported as `ResidualGuard`. Core `denotationAtMost`
remains an explicit bounded reference evaluator.

`fromDatatypeUpToDepth` accepts a derived
`TypedFTA (Refinement, LiquidConstraint) a`. Use `annotateDatatype`, or
`annotateConstructors` to annotate constructors by name, to supply the
refinement and constraint for each constructor. The datatype supplies its
fields and recursive structure; the retained codec supplies `a`. The caller
must still justify the refinements assigned to each constructor.
[`AutomatonInterop.hs`](https://github.com/Tritlo/microecta/blob/main/microcfta-generator/examples/AutomatonInterop.hs) derives a recursive
natural-number grammar, annotates it, imports it with `fromDatatypeUpToDepth`,
keeps its positive terms with `satisfying`, and composes them with
`elements`:

```sh
nix-shell --run 'cabal run cfta-automaton-interop'
```

`validOutcomes` is the explicit oracle. It enumerates every candidate the
construction describes, checks each complete witness with the solver, and
returns the accepted values in source order. It has no materialization
limit, so use it on small diagnostic inputs.

### Frozen native pools

A pool need not be part of a long-lived specification. Draw it once from a
native QuickCheck generator of values with their refinements:

```haskell
lefts  = LTAGen.pool <$> QC.vectorOf 32 nativeRefinedInt
rights = LTAGen.pool <$> QC.vectorOf 8  nativeRefinedInt
```

Sample once and use the same `LTAGen` at both child positions when they
should share a universe. The pools stay fixed inside the compiled generator;
changing them for each individual test would make ranks, replay, and
shrinking unstable and would also invoke Z3 per test. Independent pool sizes
multiply: the example describes 32 x 8 candidate pairs. For replay across
process runs, fix the draws with a seed through `Test.QuickCheck.FTAGen.unGen`,
as `freeze` does for unrefined values.

### What the LTA adds

An FTA says which constructor shapes exist. An ECTA additionally says that two
paths must contain the same term. An LTA can say that one path's refinement
implies another predicate, including after substituting actual argument names
for formal parameters. That permits constraints such as:

```haskell
safeDivision =
  LTAGen.node "divide" $ LTAGen.do
    numerator   <- integers
    denominator <- integers `LTAGen.satisfying` (\v -> v ./= 0)
    LTAGen.pure (Divide numerator denominator)

safeReads =
  LTAGen.guarded "read-at" (\n i -> 0 .<= i .&& i .< n) $ LTAGen.do
    buffer <- buffers
    index  <- indexes
    LTAGen.pure (ReadAt buffer index)
```

For dependent application with a generated function, put the result type,
function, and argument in the term exactly as the paper does, and give names
to the nested type positions with a positional guard:

```haskell
applicationGuard result function argument =
  allOf
    [ argument `isSubtypeOf` descendant function [1] -- input type
    , withActualFor argument (descendant function [0]) $
        descendant function [2] `isSubtypeOf` result -- output type
    ]
```

The compiler checks these contracts through grouped observations. A
contract that needs complete candidates is reported, not guessed.

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
  LTAGen.refinedNodeByRoots
    "step"
    stepRefinementFromRoots
    validStep $ LTAGen.do
      prefix  <- prefixes
      command <- commandContracts
      LTAGen.pure (predictPrefixStep prefix command)

validStep previous command =
  allOf
    [ previous `isSubtypeOf` command
    , withActualFor previous (descendant command [0]) $
        descendant command [1] `isSubtypeOf` root
    ]

Right compiled <- LTAGen.compileWith solver (tracesOfLength length)
```

The first guard says that the preceding trace's output state inhabits the next
command's input space. The second substitutes that actual state for the
command's formal `model` and proves its output formula implies the new trace
root. These are the paper's positional guards, not a contract: each command is
generated data that carries its stack types as refinements, so the step relates
refinements rather than values. With the top stack type in the low bits, for example, pushing an integer
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

One operation layer is ordinary applicative LTA syntax with a contract:

```haskell
takenVectors maximumLength children =
  LTAGen.refinedNodeByRoots "take" (const . resultRefinement) (contract takeContract) $ LTAGen.do
    result <- possibleLengths maximumLength
    count  <- possibleLengths maximumLength
    input  <- children
    LTAGen.pure $ SizedVector
      (Take (numberValue count) $ vectorExpression input)
      (numberRefinement result)

takeContract :: Expr -> Expr -> Expr -> Formula
takeContract result k n = 0 .<= k .&& k .<= n .&& result .== k
```

A vector's own refinement is its exact length, so the contract names the
length of the input vector by the child's term `n`. The contract of `append` is
`result .== n + m`, and that of `zipWith` is `m .== n .&& result .== n`. Each
constructor proposes its result length as its first child, and
`refinedNodeByRoots` makes that child's refinement the node's own, so the
proofs compose at the next expression layer without a refinement wrapper in
`Program`.

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
safeReads = LTAGen.guarded "read-at" inBounds $ LTAGen.do
  buffer <- sourceBuffers
  ~(_, index) <- indexes
  LTAGen.pure (ReadAt (bufferExpression buffer) index)

inBounds :: Expr -> Expr -> Formula
inBounds n i = 0 .<= i .&& i .< n
```

A buffer's refinement is `v == tripleLength` for the triple, and an index's is
`v == indexTwo` for index two. Z3 assumes those refinements for `n` and `i`,
uses facts such as `tripleLength = 3` from the environment, and retains indexes
0, 1, and 2 while rejecting -1 and 3.

The same module demonstrates a dependent result. Append proposes a result
length as its first child, its contract is `result .== n + m`, and
`refinedNodeByRoots` keeps the proven result refinement. A later `head` node
draws a buffer with ``allBuffers `satisfying` (\v -> v .>= 1)``, so it can prove
the appended buffer non-empty. The property itself needs no precondition:

```haskell
withZ3Assuming solverDeclarations solverAssumptions $ \solver -> do
  Right compiled <- LTAGen.compileWith solver safePrograms
  quickCheck $ LTAGen.forAll compiled $ \program ->
    programIsSafe program && safeResult program == Just (runProgram program)
```

The specs enumerate all 14 accepted programs, verify exact append lengths, and
run the partial interpreter through QuickCheck. This is the distinction from
an ECTA key: the accepted combinations depend on arithmetic implication under
an environment, not equality of a finite classification tag.

### Shrinking, similarity, and pools

A compiled generator shrinks structurally, as every generator does.
`shrinkRank` jumps to the smallest member of an earlier alternative and
shrinks each product component independently; every candidate is a member
of the compiled language with a smaller rank, so a shrink never leaves the
accepted language. `smallerMembers` streams every member of strictly smaller
size, and `forAll` searches it first, so the reported counterexample is
size-minimal whenever that search reaches one.

For a two-entry pool ordered as `[nonNegative, exactOne]` and a pair guard
``left `isSubtypeOf` right``, the raw product is:

```text
(0,0)  accepted
(0,1)  rejected: non-negative does not entail exactly-one
(1,0)  accepted
(1,1)  accepted
```

The compiled generator holds the three accepted pairs at ranks 0, 1, and 2,
and `(1,1)` shrinks toward `(1,0)` and `(0,0)`; `(0,1)` is never handed to
QuickCheck.

The refinement is a trusted annotation on the Haskell value. The library can
prove it only for a type with a `Literal` encoding: `elements` infers the exact
refinement of each value, and `checkPool` proves hand-written ones. For another
type, the caller must justify the refinements before constructing the pool.

Similarity minimisation remains separate and opt-in because dropping a
syntactically different value is often the wrong trade-off for testing. Declare
the non-liquid type class when semantic representatives are what you want:

```haskell
Right representatives <-
  LTAGen.minimizePoolBy solver operationKind candidates
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
states. QuickCheck needs a finite language, so bound the import by tree
height before compiling:

```haskell
Right compiled <- LTAGen.compileWith solver (LTAGen.fromAutomatonUpToDepth 6 recursiveLTA)
```

Depth zero keeps nullary transitions. Every parent-to-child edge consumes one
unit, including edges outside a cycle. A negative bound or empty language
gives `EmptyGenerator`. Ranks remain deterministic inside the bounded
language. A recursive LTA without solver guards can also be read unbounded
with `fromAutomaton`, as a recursive generator counted by size.

Enter the repository's `nix-shell` to place Z3 on `PATH`, then run the complete
example, which bounds a recursive datatype grammar:

```sh
cabal run cfta-automaton-interop
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

Each successful FTA cell draws 100,000 samples. These rows predate the
unification of the generators on one engine; the current engine draws
depth-four expressions about ten times faster than the FTA row below. Rerun
the command at the end of this section to measure the current code.

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

The typed stack-machine benchmark separates five useful paths:

- **naive** draws uniformly from all nine raw commands at every position and
  rejects the complete sequence if abstract replay fails;
- **QSM online** follows the normal state-machine-testing shape: choose a
  command admitted by the current model, advance the model, and continue;
- **bespoke** is ordinary compositional QuickCheck code which weights every
  valid next command by its number of complete suffixes;
- **ranked** is the strongest handwritten control: it duplicates the count and
  global-unrank algorithm in application code and constructs `Trace` directly;
- **LTA do** compiles the qualified-do surface: it groups the live refinement
  observations and lowers solver-approved tuples through the engine's joins;
- **LTA automaton** compiles the hand-built trace automaton, prunes it, and
  decodes each selected `Tree LiquidSymbol` to a `Trace`. The table below
  lists this row twice, as the earlier materialized and fused decoders.

Naive rejection, bespoke, ranked, and the LTA rows are uniform over the
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

The package has two test suites, `gen-tests` and `refinement-tests`; the
second needs `z3`. `-j1` keeps an optimized build of the core inside a small
machine's memory.
