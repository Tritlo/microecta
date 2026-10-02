# microcfta-generator

Ranked generation, random sampling, replay, and shrinking for the automata of
[`microcfta`](../microcfta/README.md), with QuickCheck integration. There is
one generator type, `Gen symbol a`, and one facade per kind of automaton:

| Module | Purpose |
| --- | --- |
| `Data.CFTA.Gen` | The generator: sources, constructors, choices, joins, recursion, imported automata and datatypes, exact inspection, replay, and shrinking, for every kind of automaton. |
| `Data.CFTA.Gen.QuickCheck` | Sampling and properties over a generator, and frozen pools. |
| `Data.CFTA.Gen.Do` | Qualified applicative do-notation, re-exported by the three `QuickCheck` facades; `FTAGen.do`, `ECTAGen.do`, and `LTAGen.do` are this module under the facade's alias. |
| `Data.CFTA.Gen.Error` | The one failure vocabulary, and `explain`. |
| `Data.CFTA.Gen.Equality` | `ECTAGen`: equality-constrained generators, and imports ranked by symbol text. |
| `Data.CFTA.Gen.Equality.QuickCheck` | Re-exports `Data.CFTA.Gen.Equality` with the QuickCheck functions. |
| `Data.CFTA.Ranked`, `Data.CFTA.Ranked.QuickCheck` | Finite ranks, weighted sampling, replay, and structural shrinking, independent of automata. |
| `Data.CFTA.Gen.Internal.*`, `Data.CFTA.Ranked.Internal.*` | The engine: static and recursive languages, joins, symbolic counting, decoders, samplers, sizes, and shrinking; exposed for integration, not covered by the PVP contract. |

## Ordinary generators

Run the complete example from the workspace root:

```sh
nix-shell --run 'cabal run cfta-pairs'
```

[`examples/FinitePairs.hs`](examples/FinitePairs.hs) derives the pair datatype
with the finite `Int` domain `[0, 1]`. It checks all replay ranks and samples
the accepted pairs with QuickCheck. It also constructs the same language as an
interned `Common.Node String`, imports it with `fromAutomaton`, and checks
the imported generator.

`FTAGen.node "pair"` closes an applicative child block with one constructor.
Each binding supplies one direct child. A binding whose generator is itself a
product, such as `f <$> a <*> b`, supplies one child for each of its parts;
close it with its own `node` to make it one child. Enable `ApplicativeDo` and
`QualifiedDo`, and finish the block with `FTAGen.pure`. Child generators must be
independent. `leaf value symbol` is a constructor without children, and
`oneof` and `frequency` choose between generators. They skip an empty
alternative and do not report an error.

`fromAutomaton` reads an interned automaton as a generator of the terms it
accepts. An acyclic automaton gives a finite generator with one rank per
distinct term: where alternatives overlap or an equality reaches below
direct children, the count is symbolic. Ranks order the constructors at each
node by arity, then by the symbol's `Ord`, so nullary constructors come first
and the ranks do not depend on the order in which the automaton was built. A
cyclic automaton gives a recursive generator counted by size, the number of
term nodes, and uses the same order within each size; it must be
unambiguous, because its count sums over accepting runs. A symbolic count has
no size classes, so its members report size one, and `smallerMembers` and the
size-minimal search of `forAll` find no smaller member. `fromAutomatonUpToDepth` bounds the automaton by
constructor depth first, a leaf having depth zero, and `upToSize` bounds any
generator to the members of at most a given number of source choices, in
size-major rank order. Use `Data.CFTA.Interned.fromFTA` first when the source
is an explicit-state automaton; the import is total and retains shared states.

`fromDatatype` reads a derived grammar as a generator of its values,
recursive when the datatype is, and `fromDatatypeUpToDepth` bounds it by
constructor depth. The value and its constructor term share one rank, and
the codec runs only when a selected value is demanded. Ranks order the
constructors of a type by arity, then in declaration order, and atomic
literals in domain order. The generator decodes one term per constructor when
it is built, so an atomic type whose `Show` text `Read` does not accept gives
`UndecodableConstructor` at once. Depth counts
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

An expression at the next depth is one of the two literals or an `Add` of an
ordered pair of expressions from the previous depth, so `n` expressions give
`2 + n * n`. The rank decoder constructs the
selected values from the compiled grammar.

The QuickCheck adapter adds random sampling and shrinking. Counts and replay
ranks identify distinct terms; an ambiguous handwritten grammar is counted
symbolically, so one term still has one rank.

For another complete example, see
[`FinitePairs.hs`](examples/FinitePairs.hs), or run
`cabal run cfta-pairs` from the workspace root.

## Equality-constrained generators

An equality generator is `Gen Symbol`, written `ECTAGen`. Its
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
`Node Symbol`, up to a depth. Build it with `mkEdge`, or
annotate an explicit-state automaton with `Data.CFTA.annotate` and intern it
with `Data.CFTA.Interned.fromFTA`.
`fromDatatypeUpToDepth` accepts a derived `TypedFTA Constraint a` and returns
typed values. Both functions are available from the QuickCheck API.

For example, derive `(Bool, Bool)` with `deriveFTA`, then use
`annotateDatatype` to attach `equalityConstraint (mkEqConstraints [[path [0], path [1]]])` to its
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

`elements` and `fromIndexed` turn a finite indexed source into an ECTA whose
leaves contain stable indices, not generated values. `Functor` and
`Applicative` composition preserve that symbolic structure, so ordinary
`ApplicativeDo` builds ECTA products. Alongside the ECTA, the generator tracks
an exact cardinality and a rank-to-outcome selector; applicative products
multiply their counts rather than materializing their Cartesian products.

`match` generates two values under a reified key equality: in
`match (authenticatedUser :==: fileOwner) authentication filesystem`, the
`:==:` keeps both projections as data, so the match can group each input by
its own key, encode the shared keys as an actual ECTA equality constraint,
count the matching group products, and unrank directly into the selected
group. `:&&:` conjoins several equalities. This is the exact-uniform
conditioning of [Claessen, Duregård and Pałka, *Generating Constrained Random
Data with Uniform Distribution*, JFP 25,
2015](https://doi.org/10.1017/S0956796815000143). The condition is reified as
data, so `match` does not test it on samples. `match` accepts arbitrary value
projections, so it must enumerate the input ranks to find its groups. To
condition three or more generators, use the grouped layer (`groupOn` and
`apply`).

`relate leftKey rightKey relation left right` admits every pair for which the
projected keys satisfy `relation`. The relation is an ordinary Haskell
function such as `canRead Admin Public = True`; it may be asymmetric and the
two key types may differ. A transparent join evaluates it once per live key
pair, then counts, ranks, and samples the accepted group products directly.
An opaque input uses rejection filtering. For an equality, `match` is shorter
and faster, because it intersects the two key maps and does not test their
Cartesian product.

`relateM` is the compile-time, effectful form for finite transparent inputs. It
groups each input once, invokes the callback once per live key pair, and then
uses the same equality join. `relateGroupsM` starts from already grouped
languages and therefore never enumerates their members. The LTA compiler uses
it to turn solver-approved refinement tuples into a pure ECTA rank plan.
`relateN` generalizes that operation to homogeneous n-ary key tuples, and
`filterGroupsM` performs an effectful selection over an existing key space
without visiting the members below each key.

`Grouped key a` keeps the grouping of a generator, for nested or very large
languages. The snippets in this section are fragments of one complete
program, the typed-expression flagship
[`Data.CFTA.Gen.TypedExpressionLanguage`](https://github.com/Tritlo/microecta/blob/main/microcfta-generator/common/Data/CFTA/Gen/TypedExpressionLanguage.hs).
Read the whole program when the snippets are not sufficient. The `key` is the
type that the classifier returns. It decides which groups can be joined, and it
is not part of the generated `a`. Matching key values receive equal internal
labels on constrained ECTA paths.

`groupOn` classifies the outcomes of any transparent generator and enumerates
them once. `keyed key generator` declares that every member already has one
known key. `keyed` does not enumerate members, so it also accepts a recursive
transparent generator, and the caller must declare the correct key. Grouped
generators support ordinary `fmap`, and `mapWithKey` when the function also
needs the key. `regroupOn` changes the classification without enumerating
values, `sizes` returns the stored cardinality of every group, and `atKey`
selects one group as an ordinary conditional generator.

A `Sig` classifies an operation of any arity. It has the form of a many-sorted
operation signature, with `:*` between argument keys and `:->` before the
result key: `leftKey :* rightKey :-> resultKey`. `apply` matches each
signature key with the corresponding argument family. It equates their paths
in one ECTA edge, with one equality constraint per argument, and keeps the
result key for later equality constraints. The operation family holds
functions (`fmap` a compiling function onto it), and the argument families
arrive as an `Args` chain.

`frequencies` chooses among grouped generators with relative weights, group by
group, so alternated layers stay grouped. `uniformlyGrouped` combines grouped
generators in proportion to their exact cardinalities, so every member of the
union is equally likely. A layered language needs this. `uniformly` does the
same for flat generators. The expressions of depth at most `n` are one such
union, and no count is computed by hand:

```haskell
upToDepthByType 0 = literalsByType
upToDepthByType depth =
  ECTAGen.uniformlyGrouped
    [literalsByType, applicationLayer (upToDepthByType (depth - 1))]
```

`ungroup` returns an ordinary `ECTAGen` with the same exact distribution.
Stable source order and ascending key order give deterministic replay ranks.

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
  ECTAGen.groupOn binarySignature (ECTAGen.elements binaryFunctionInstances)

binarySignature instance_ =
  firstArgumentType instance_
    :* secondArgumentType instance_
    :-> binaryResultType instance_

literalsByType :: Grouped Type TypedExpression
literalsByType = ECTAGen.groupOn expressionType (ECTAGen.elements literals)

unaryFunctionsBySignature :: Grouped UnarySignature (TypedExpression -> TypedExpression)
unaryFunctionsBySignature =
  compileNot <$ ECTAGen.keyed unarySignature (ECTAGen.elements [()])

conditionalFunctionsBySignature =
  compileConditional
    <$> ECTAGen.groupOn conditionalSignature (ECTAGen.elements allTypes)

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
replay, while `countOn` reports exact coverage of ranked outcomes. A retained
`Grouped` key is also a symbolic observation. `countsAtSize` reports how many
members reach each key. `massesAtSize` reports the exact key distribution used
by sampling that size. Declared atomic weights can therefore produce equal
counts and unequal masses. Recursive groups memoize both size series, so these
queries do not enumerate traces. ECTA support is demand-driven: counts, masses,
replay, sampling, and constrained joins retain it as a lazy thunk. `support`
forces the complete symbolic representation, a `Node (Label Symbol)`:
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
The generic `countOn`, `pmf`, and `pmfAtSize` observers are therefore best for
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
whenever that search reaches one. After that search, `forAll` uses size-major
structural shrinking through `shrinkRank`. For a recursive generator,
`shrinkRank` reads its candidates from the form bounded at the current size,
because only a bounded form gives a recursive member components to shrink.
Every candidate is a member of
the generated language, and the failing rank is printed for deterministic
replay with `unrank`. A generator with an opaque region has no ranks at all, so
`forAll` tests it by sampling with no shrinking. `sized` builds and compiles
one generator per QuickCheck size (shared across samples), so layered
generators can scale with the size parameter.

The greedy shrinkers of QuickCheck, Hedgehog, Hypothesis, and falsify stop at
a local minimum. Bounded-exhaustive tools find a smallest counterexample by testing the
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
coverage = ECTAGen.countOn authenticatedUser authentication
```

### Inspect a generator

Use `namedElements` to retain source names, including names for function values.
Use `nameGroups` to retain display names for classified keys without decoding
their members. Both functions preserve semantic support, ranks, and weights.

```haskell
{-# LANGUAGE OverloadedStrings #-}

import qualified Data.CFTA.Gen.Equality.QuickCheck as ECTAGen

-- | Two named integer source choices.
integers :: ECTAGen.ECTAGen Int
integers = ECTAGen.namedElements [("zero", 0), ("one", 1)]

-- | Apply a named function to the integer source.
incremented :: ECTAGen.ECTAGen Int
incremented = ECTAGen.namedElements [("increment", (+ 1))] <*> integers
```

`ECTAGen.inspect incremented` returns an `Inspection`, and `drawInspection` draws
it as an ASCII tree. Its `inspectionGraph` is a
`Node (InspectionSymbol Symbol)`. For another rendering, pass it
to `ECTA.toTree`, then render the typed labels with `fmap` and
`Data.Tree.drawTree`. Each `InspectionSymbol` retains `originalSymbol`, a
`Label Symbol`, and an optional `displayLabel`. `inspectionName` holds a group
name when one is available. `ViewPath` locations belong to the graph passed to
`toTree`.

Source names describe source choices. `fmap` preserves those names; it does not
infer names for mapped results. `regroupOn` clears old group names because the
keys change. Apply `nameGroups` after regrouping to name the new keys. Source
names remain available through grouping, application, and recursion.

The diagnostic graph preserves construction structure and equality obligations.
Names distinguish occurrences that share one semantic node, such as integer
and Boolean sources with the same rank indices. The graph does not run equality
reduction. Use `ECTAGen.support` for membership and other semantic operations.

Counts and rank decoding do not evaluate display names or construct the
diagnostic graph. Retaining the extra fields and closures still uses memory.
Inspecting the graph also allocates its nodes and formatted names.

Run `cabal run cfta-draw-typed-expressions` to draw the actual finite and
recursive expression generators. The [example](examples/DrawTypedExpressions.hs) calls
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
unbounded without unrolling it layer by layer:

```haskell
tree :: ECTAGen Tree
tree = ECTAGen.recur $ \self ->
    ECTAGen.oneof
        [ Leaf <$> ECTAGen.elements [0 .. 2]
        , Branch <$> self <*> self
        ]
```

The result is the whole language. It has no cardinality. It has size
classes, counted by FEAT-style convolution, where the size of a member is its
number of source choices. For the tree above, `countAtSize tree 4` is
`Right 405`. Ranks are size-major, so `unrank tree 0` is the smallest member
and every rank replays as usual. The ECTA support is a `Mu` node: one finite
automaton for infinitely many terms.

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
larger bound. `forAll` first tests the whole size classes below the failing
member. After its cap, it shrinks the components of the form bounded at the
failing member's size.

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
infinitely many members, so bound it with `upToSize` before making it atomic,
and do that *outside* the recursive definition. Neither `upToSize` nor `atomic`
can be applied to the `recur` argument, or to anything built from it: the bound
would need the size classes that definition is still computing, and an atom
over them would have a cardinality depending on itself. Both shapes are
rejected with `BoundedRecursiveOccurrence`. Opaque generators have no size
structure and cannot be made atomic.

The self-reference has to go through `recur`. A generator that names itself
directly, as in `tree = Branch <$> tree <*> tree`, is an infinite Haskell
value. Building it never finishes, so the program hangs and the library
cannot report an error. In the other direction, a body that never uses the
argument is not recursive, and `recur` returns it unchanged: a finite body
stays a finite generator, with its cardinality and inspection. A body that
cannot be built reports its own error, and `recur` does not turn it into a
recursive language that every finite inspector calls unbounded.

Two rules apply inside the knot. The recursion must be guarded: every
occurrence of the argument sits under at least one `<*>`. Otherwise the
language has no smallest member, so `recur` rejects the definition with
`UnguardedRecursion` and does not hang. The check is per definition, so inside
a nested `recur` an occurrence of the *outer* language must also sit under an
application within the inner body. Structural alternatives around a recursive
occurrence must carry equal weights. `oneof` gives equal weights, and the size
bound controls how large members get. `frequency` with unequal weights on
recursive branches is an error. A weighted finite choice may still enter
through `atomic`, retaining its own distribution inside every recursive size.

Inspection that needs one ECTA term per member (`groupOn`, `match`, `relate`,
`pmf`, `countOn`) is not available on a language built with `recur`, bounded or
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

The set of keys in the family is part of the fixpoint, so `recurGrouped`
solves it first. It starts from the empty family and adds the result keys of
operations whose argument keys are already present. Then it ties the languages
over that set. All the keys share one `Mu` node whose edges carry their key as
a first child; an occurrence at one key is that node under an edge holding
the key's label, with an equality constraint tying the two. A recursive
family is therefore one recursive automaton whose cycle carries the keyed
joins' equality constraints. Only an ECTA can hold this shape.

For the language above, unfolding that automaton twice accepts exactly the 46
expressions produced by the hand-unrolled depth-one generator. This includes
unary `Not`, the binary functions, and ternary `IfExpression`. `ungroup` and
`atKey` are the exits back to an ordinary recursive generator, so bounding,
sampling, replay, and shrinking all work as above. `sizes` has no cardinality
to report for a recursive family; use `countAtSize` on `atKey`.

`fromAutomaton` goes the other way: it reads an existing automaton as a generator
of the terms it accepts, with the automaton itself as the support. An
acyclic automaton is a finite generator, as above; a cyclic one is a
recursive generator, counting terms by size, which is the number of term
nodes.

```haskell
import qualified Data.Tree as Tree

types :: Node Symbol
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
terms, bounding one of these keeps full inspection: `pmf`, `countOn`, and
`groupOn` all work on `upToSize n (fromAutomaton node)`, and so does
`termAt` on a mapped one.

The recursive count does not count equality constraints. They correlate an
edge's children, so the edge's count is the size of an intersection rather
than a product of the children's counts; a cyclic automaton carrying them is
rejected with `CannotCountConstrainedEdges`. Bound
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
`Selective` instance. This keeps inspectable applicative regions inside ECTA
and makes the loss of structure explicit.
## Sampling performance

The flagship FTA and ECTA languages each have three exact-uniform generators:

- The naive generator makes an unconstrained representation, then recognizes
  or rejects it.
- The bespoke generator is handwritten and specialized to the language.
- The FTA or ECTA generator compiles the declarative automaton to a rank
  decoder.

All rows at a given depth therefore sample the same finite language with the
same uniform distribution. A smaller or biased baseline would make a speed
comparison meaningless. The FTA's naive generator builds a generic
ranked term, recognizes it with a one-state FTA, then decodes it. There is no
semantic condition to reject, so that row is the zero-rejection control. The
ECTA's naive generator creates a raw application at each layer and rejects it
after independent type inference; its root alternatives are weighted by raw
candidate counts, so conditioning preserves uniformity. The bespoke ECTA
generator carries the requested result type through ordinary Haskell.

Every cell runs in a fresh process because the interning tables never evict.
The first-sample column includes construction; the throughput and allocation
columns reuse the resulting generator. A complete cell has a
30-second wall-clock limit and successful cells are the median of three runs.

### Ordinary generators: untyped integer expressions

Each successful FTA cell draws 100,000 samples.

| depth | members | engine | first sample | samples/s | alloc/sample | setup mem | retained after 100k |
| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 8 | naive | 0.03 ms | 3,247,563 | 1.1 KB | 32.8 KB | 35.0 KB |
| 1 | 8 | bespoke | 0.01 ms | 13,326,681 | 384 B | 1.0 KB | 3.1 KB |
| 1 | 8 | FTA | 0.03 ms | 10,916,059 | 432 B | 40.9 KB | 43.3 KB |
| 2 | 128 | naive | 0.03 ms | 1,321,243 | 2.4 KB | 32.9 KB | 35.0 KB |
| 2 | 128 | bespoke | 0.01 ms | 5,944,053 | 768 B | 1.0 KB | 3.2 KB |
| 2 | 128 | FTA | 0.04 ms | 5,220,430 | 704 B | 47.5 KB | 52.5 KB |
| 3 | 32,768 | naive | 0.02 ms | 616,877 | 4.9 KB | 32.9 KB | 35.0 KB |
| 3 | 32,768 | bespoke | 0.01 ms | 2,928,788 | 1.5 KB | 1.1 KB | 3.2 KB |
| 3 | 32,768 | FTA | 0.04 ms | 3,042,596 | 1.3 KB | 55.4 KB | 73.8 KB |
| 4 | 2,147,483,648 | naive | 0.03 ms | 281,145 | 10.0 KB | 32.9 KB | 35.0 KB |
| 4 | 2,147,483,648 | bespoke | 0.01 ms | 1,440,284 | 3.0 KB | 1.1 KB | 3.2 KB |
| 4 | 2,147,483,648 | FTA | 0.05 ms | 1,250,528 | 2.5 KB | 66.1 KB | 143.4 KB |

An ordinary FTA adds no semantic pruning to this language, so this row is the
control. The FTA decoder stays within about 20% of the direct bespoke
generator at every depth. The naive row is 3.4x to 4.9x slower than the FTA,
because it builds a generic term and then recognizes it.

### Equality generators: typed integer and Boolean expressions

Each successful ECTA cell draws 20,000 samples. The smaller fixed workload
keeps depth three measurable while preserving the depth-four rejection
failure; it is still large enough for stable normalized rates.

| depth | members | engine | first sample | samples/s | alloc/sample | setup mem | retained after 20k |
| ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 42 | naive | 0.01 ms | 2,460,466 | 1.1 KB | 1.6 KB | 3.6 KB |
| 1 | 42 | bespoke | 0.01 ms | 5,753,013 | 350 B | 2.5 KB | 6.2 KB |
| 1 | 42 | ECTA | 0.08 ms | 6,921,840 | 458 B | 56.5 KB | 58.9 KB |
| 2 | 27,054 | naive | 0.03 ms | 248,396 | 9.3 KB | 32.9 KB | 35.0 KB |
| 2 | 27,054 | bespoke | 0.03 ms | 3,317,611 | 754 B | 4.0 KB | 31.3 KB |
| 2 | 27,054 | ECTA | 0.10 ms | 3,390,678 | 933 B | 67.2 KB | 70.2 KB |
| 3 | 8,887,065,932,466 | naive | 0.06 ms | 43,394 | 61.4 KB | 33.2 KB | 35.3 KB |
| 3 | 8,887,065,932,466 | bespoke | 0.16 ms | 1,219,930 | 1.9 KB | 10.3 KB | 89.5 KB |
| 3 | 8,887,065,932,466 | ECTA | 0.18 ms | 1,567,726 | 2.3 KB | 77.6 KB | 81.8 KB |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | naive | 0.24 ms | 9,897 | 262.7 KB | 33.6 KB | 35.8 KB |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | bespoke | 1.44 ms | 369,357 | 7.0 KB | 21.8 KB | 212.8 KB |
| 4 | 494,767,711,145,600,737,617,026,761,045,287,855,174 | ECTA | 0.24 ms | 471,472 | 7.7 KB | 89.2 KB | 94.2 KB |

At depth three the ECTA decoder is about 36x faster than rejection and 1.3x
faster than the bespoke generator. It allocates about 27x less per sample than
rejection, and 1.2x as much as the bespoke generator. At depth four the ECTA
is about 48x faster than rejection and 1.3x faster than the bespoke
generator. The setup cost stays below 0.25 ms because the finite dependency
structure is compiled once and every later sample is one rank decode.

Measured with GHC 9.14.1 and `-O2` on an x86_64 machine under WSL2 on
2026-09-30. An empty generator ran at about 11.7M draws/s and one `chooseInt`
at 48.8M draws/s during the ECTA run. Rates move by up to about 20% between
runs on this machine, and with the QuickCheck and `random` versions in use.
Reproduce one table, or all four repository tables, with:

```sh
cabal bench microcfta-generator:untyped-expression-speed --enable-optimization=2
cabal bench microcfta-generator:typed-expression-speed --enable-optimization=2
./scripts/benchmark-generators.sh
```

## Concurrency

Generators are safe to use from any thread. They build automata, and
`microcfta` interns nodes through process-global tables, which are
synchronized.

A testing library needs this, because test runners run tests in parallel:
`tasty` runs independent tests concurrently by default when the test binary is
linked with `-threaded` and run with `+RTS -N`, and `hspec` does so under
`parallel`. A property that draws from an `ECTAGen` can run that way even when
nothing in your code looks concurrent. With `microecta` 0.1.0.0, that gave
silent corruption, not a crash; see the concurrency note in the `microcfta`
README.
