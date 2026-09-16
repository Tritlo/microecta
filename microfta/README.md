# microfta

Describe whole sets of trees with a finite graph. `microfta` derives tree
languages from Haskell datatypes, checks whether a value belongs to a language,
and combines languages with shared structure.

Use it to describe expression grammars, restrict recursive data, or build the
ordinary tree-automaton layer of a constraint system. A finite automaton can
represent an infinite language. You can inspect and transform its grammar
without enumerating its values.

- **Start with your datatype.** Derive `HasFTA` to get a grammar, constructor
  metadata, and codecs between Haskell values and constructor trees.
- **Restrict a language.** Choose finite literal domains, bound tree depth,
  and intersect grammars.
- **Share repeated structure.** Interned nodes reuse equal subgraphs across
  construction and operations.
- **Use the core on its own.** Recognition and graph operations need no
  generator, equality-constraint package, or solver.

## Start with a datatype

Suppose an expression is a literal or the sum of two expressions. Derive
`HasFTA` with `DeriveAnyClass`, alongside the usual `Generic` instance:

```haskell
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import GHC.Generics (Generic)

import qualified Data.Tree.FTA as FTA
import Data.Tree.FTA.Generic (HasFTA, datatypeDecode, datatypeFTA, deriveFTAWith, domain, encodeTerm)

-- | Arithmetic expressions with integer literals.
data Expr = Lit Int | Add Expr Expr
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | Derive a grammar, recognize values, and restrict their depth.
main :: IO ()
main = case deriveFTAWith @Expr (domain @Int [0, 1]) of
    Left err -> fail (show err)
    Right datatype -> do
        let grammar = datatypeFTA datatype
            value = Add (Lit 0) (Lit 1)
            shallow = FTA.boundDepth 2 grammar

        print (length (FTA.states grammar))
        print (FTA.accepts grammar (encodeTerm value))
        print (FTA.accepts grammar (encodeTerm (Lit 7)))
        print (datatypeDecode datatype (encodeTerm value) == Just value)
        print (FTA.accepts shallow (encodeTerm value))
        print (FTA.accepts shallow (encodeTerm (Add value (Lit 0))))
```

Add `microfta` to your component's `build-depends`. To try the example in this
checkout, save it as `Main.hs` at the workspace root and run:

```sh
cabal build microfta
cabal exec -- runghc -package=microfta Main.hs
```

The output is:

```text
2
True
False
True
True
False
```

The grammar has two states: one for `Expr` and one for `Int`. `Lit` connects
an expression to a literal. `Add` connects it to two more expressions. These
recursive transitions describe expressions of any depth with literals `0`
and `1`.

`encodeTerm` converts a value to a constructor tree. `FTA.accepts` checks that
tree against the grammar. The grammar rejects `Lit 7` because `7` is outside
the configured domain. `datatypeDecode` converts a constructor tree back to
the typed value.

`boundDepth 2` produces a finite language from the recursive grammar. Depth
counts edges from the root: an integer literal is at depth zero, `Lit 0` has
depth one, and `Add (Lit 0) (Lit 1)` has depth two. The nested `Add` in the last
check has depth three, so the bounded grammar rejects it.

### Choose domains and retain metadata

Use `deriveFTA @YourType` when no primitive field needs a domain. `Bool`,
lists, `Maybe`, `Either`, unit, and tuples have built-in `HasFTA` instances.
Derive `HasFTA` for each user datatype in a mutually recursive family.

`Int`, `Integer`, `Char`, and `Text` require explicit finite domains. Combine
domains with `(<>)`; for example, `domain @Int [0, 1] <> domain @Char ['a', 'b']`.
A missing domain produces `Left (MissingDomain ...)`.

The derived graph retains constructor names, field types, and record selector
names. `fieldNamed` locates a record field. `annotateDatatype` adds constructor
annotations while retaining the grammar and its codecs. A constraint layer
can interpret those annotations without rebuilding the datatype description.

The codecs describe the whole datatype. They do not enforce literal domains
or interpret annotations. Use recognition against the grammar to check those
domains. Derivation supports regular algebraic datatypes; it rejects recursion
that grows type arguments. Function fields have no built-in instance. GADTs
and existential fields cannot use the default `Generic` derivation.

## Build languages with shared structure

You can construct a language directly when no Haskell datatype describes it.
Here is a binary tree whose leaves can each be `"zero"` or `"one"`:

```haskell
import qualified Data.Tree.FTA.Interned as Common

choices :: Common.PlainNode String
choices = Common.Node [Common.Edge "zero" [], Common.Edge "one" []]

pair :: Common.PlainNode String -> Common.PlainNode String
pair child = Common.Node [Common.Edge "pair" [child, child]]

language :: Common.PlainNode String
language = iterate pair choices !! 5

sharedNodeCount :: Int
sharedNodeCount = Common.nodeCount language -- 6
```

Each accepted tree has 32 independently chosen leaves. The language contains
4,294,967,296 trees, but its graph has six shared nodes. Constructing the graph
does not construct those trees. Reusing `child` shares its language; it does
not require the two selected child trees to be equal.

`Common.union` combines alternatives. `Common.intersect` retains trees that
both inputs accept. `Common.nodeRepresentsWith (\() _ -> True)` recognizes
ordinary terms. `Common.toFTA` exposes each reachable node as one explicit
state for inspection or use by another package.

`Common.Mu` describes recursive languages. Each recursive cycle must pass
through a constructor edge; `Mu id` is not supported. `Common.toFTA` rejects
an open recursive root.

## Use named states when you need them

The explicit-state interface is useful when a grammar comes from a file or
state names are part of your application:

```haskell
import Data.Tree.FTA (FTAError, PlainFTA, accepts)
import qualified Data.Tree.FTA.Syntax as Syntax
import Data.Tree.Term (Term (Term))

naturals :: Either (FTAError Int String) (PlainFTA Int String)
naturals =
    Syntax.automaton
        0
        [ Syntax.row
            0
            [ Syntax.transition "zero" []
            , Syntax.transition "successor" [0]
            ]
        ]

oneAccepted :: Either (FTAError Int String) Bool
oneAccepted = fmap (`accepts` Term "successor" [Term "zero" []]) naturals

-- Right True
```

An automaton checks symbol arities and child-state references at construction.
Cycles are valid. `PlainFTA` uses `()` for transition annotations.

`Data.Tree.FTA.intersect` constructs reachable product states and pairs the
input annotations. Apply `stripGuards` to the result of two plain FTAs before
calling `accepts`. Use `intersectWith` when you need a different annotation
combination. `stripGuards` removes annotations; it does not solve constraints.

## Generate a language up to a depth bound

Add [`microfta-generator`](../microfta-generator/README.md) to turn a grammar
into a generator. This complete example generates expressions with literals
`0` and `1`, up to constructor-tree depth 3:

```haskell
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import GHC.Generics (Generic)

import qualified Data.Tree.FTA.Gen as Gen
import Data.Tree.FTA.Generic (HasFTA, deriveFTAWith, domain)

-- | Arithmetic expressions with integer literals.
data Expr = Lit Int | Add Expr Expr
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | Print every expression in a depth-bounded language.
main :: IO ()
main = do
    datatype <- either (fail . show) pure $ deriveFTAWith @Expr (domain @Int [0, 1])
    language <- either (fail . show) pure $ Gen.fromDatatypeUpToDepth 3 datatype
    mapM_ (either (fail . show) print . Gen.unrank language) [0 .. Gen.cardinality language - 1]
```

Add both `microfta` and `microfta-generator` to your component's
`build-depends`. In this checkout, save the program as `Main.hs` at the
workspace root and run:

```sh
cabal build microfta-generator
cabal exec -- runghc -package=microfta -package=microfta-generator Main.hs
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

As in the recognition example, the bound includes the `Int` child of `Lit`.
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
[`FinitePairs.hs`](../microfta-generator/examples/FinitePairs.hs), or run
`cabal run fta-pairs` from the workspace root.

## Module guide

| Module | Use it for |
| --- | --- |
| `Data.Tree.FTA.Generic` | Datatype derivation, finite domains, metadata, and typed codecs. |
| `Data.Tree.FTA` | Checked transition graphs, recognition, depth bounds, and product intersection. |
| `Data.Tree.FTA.Syntax` | Named states and transitions without unit-annotation boilerplate. |
| `Data.Tree.FTA.Interned` | Shared nodes and edges, recursive languages, union, and intersection. |
| `Data.Tree.Term` | Concrete constructor trees. |
| `Data.Tree.FTA.Constraint` | Conjunction, the unconstrained value, and known contradictions. |

The interned engine has a symbol type and a constraint type. Ordinary
languages use `()` as the constraint. A `Constraint` instance supplies
conjunction and known contradictions; `nodeRepresentsWith` takes the
concrete-term interpreter. This permits constraint-specific packages to share
the graph implementation.

## Memory and cache lifetime

The explicit-state graphs in `Data.Tree.FTA`, including the datatype tutorial
above, are ordinary Haskell values. The garbage collector can reclaim them
when no references remain.

The interned API uses process-global node, edge, and operation memo tables.
These tables hold strong references and do not evict entries. Reusing a graph
can reuse its cached entries, but constructing distinct graphs can retain
memory for the lifetime of the process. Completing generation or enumeration
does not clear these tables.

There is no safe public reset operation. Interned equality and hashing use
canonical identities. Removing a live node from its table can give a later
copy of the same structure a different identity. Account for this retention
when using the interned API in a long-running process.

## Development

Run the core tests from the workspace root:

```sh
cabal test microfta:unit-tests
```
